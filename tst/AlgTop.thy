theory AlgTop
  imports "AlgTopCached6.AlgTopCached6"
begin
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



(** Theorem 71.3 stub: infinite case has sorry. Not on \<S>75.3 chain. **)

(** from \<S>71 Theorem 71.3: arbitrary (possibly infinite) wedge of circles. **)
theorem Theorem_71_3_wedge_of_circles_general:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX J p"
  shows "\<exists>(G::int set) mul e invg (\<iota>::'i \<Rightarrow> int).
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
  show ?thesis
  proof (cases "finite J")
    case True
    \<comment> \<open>Finite case: bijection J \<leftrightarrow> {..<card J}, relabel wedge, apply Theorem 71.1.\<close>
    have hcard: "{0..<card J} = {..<card J}" by (by100 auto)
    from ex_bij_betw_nat_finite[OF True] obtain f where
      hf: "bij_betw f {..<card J} J" using hcard by (by100 auto)
    \<comment> \<open>Extract the circle family from the wedge.\<close>
    from assms[unfolded top1_is_wedge_of_circles_on_def]
    obtain C where
      hC: "\<forall>\<alpha>\<in>J. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
             \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
      and hcover: "(\<Union>\<alpha>\<in>J. C \<alpha>) = X"
      and hdisjoint: "\<forall>\<alpha>\<in>J. \<forall>\<beta>\<in>J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
      and hweak: "\<forall>D. D \<subseteq> X \<longrightarrow>
             (closedin_on X TX D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      by (elim conjE exE) (rule that, assumption+)
    \<comment> \<open>Define relabeled circles: C'(i) = C(f(i)).\<close>
    define C' where "C' i = C (f i)" for i
    have hf_inj: "inj_on f {..<card J}" using hf unfolding bij_betw_def by (by100 blast)
    have hf_surj: "f ` {..<card J} = J" using hf unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>Show: wedge with index {..<card J}.\<close>
    have hwedge': "top1_is_wedge_of_circles_on X TX {..<card J} p"
      unfolding top1_is_wedge_of_circles_on_def
    proof (intro conjI)
      show "is_topology_on_strict X TX"
        using assms unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
      show "is_hausdorff_on X TX"
        using assms unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
      show "p \<in> X"
        using assms unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
      show "\<exists>Ca. (\<forall>\<alpha>\<in>{..<card J}. Ca \<alpha> \<subseteq> X \<and> p \<in> Ca \<alpha>
               \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                        (Ca \<alpha>) (subspace_topology X TX (Ca \<alpha>)) h))
          \<and> (\<Union>\<alpha>\<in>{..<card J}. Ca \<alpha>) = X
          \<and> (\<forall>\<alpha>\<in>{..<card J}. \<forall>\<beta>\<in>{..<card J}. \<alpha> \<noteq> \<beta> \<longrightarrow> Ca \<alpha> \<inter> Ca \<beta> = {p})
          \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
               (closedin_on X TX D \<longleftrightarrow>
                (\<forall>\<alpha>\<in>{..<card J}. closedin_on (Ca \<alpha>) (subspace_topology X TX (Ca \<alpha>)) (Ca \<alpha> \<inter> D))))"
      proof (rule exI[of _ C'])
        have hC'_props: "\<forall>i\<in>{..<card J}. C' i \<subseteq> X \<and> p \<in> C' i
            \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                     (C' i) (subspace_topology X TX (C' i)) h)"
        proof (intro ballI)
          fix i assume "i \<in> {..<card J}"
          hence "f i \<in> J" using hf_surj by (by100 blast)
          thus "C' i \<subseteq> X \<and> p \<in> C' i
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                       (C' i) (subspace_topology X TX (C' i)) h)"
            unfolding C'_def using hC by (by100 blast)
        qed
        have hcover': "(\<Union>i\<in>{..<card J}. C' i) = X"
        proof -
          have "(\<Union>i\<in>{..<card J}. C' i) = (\<Union>i\<in>{..<card J}. C (f i))"
            unfolding C'_def ..
          also have "\<dots> = (\<Union>\<alpha>\<in>f`{..<card J}. C \<alpha>)"
            by (by5000 auto)
          also have "\<dots> = (\<Union>\<alpha>\<in>J. C \<alpha>)" using hf_surj by (by100 simp)
          finally show ?thesis using hcover by (by100 simp)
        qed
        have hdisjoint': "\<forall>i\<in>{..<card J}. \<forall>j\<in>{..<card J}. i \<noteq> j \<longrightarrow> C' i \<inter> C' j = {p}"
        proof (intro ballI impI)
          fix i j assume "i \<in> {..<card J}" "j \<in> {..<card J}" "i \<noteq> j"
          hence "f i \<in> J" "f j \<in> J" "f i \<noteq> f j"
            using hf_surj hf_inj unfolding inj_on_def by (by100 blast)+
          thus "C' i \<inter> C' j = {p}" unfolding C'_def using hdisjoint by (by100 blast)
        qed
        have hweak': "\<forall>D. D \<subseteq> X \<longrightarrow>
            (closedin_on X TX D \<longleftrightarrow>
             (\<forall>i\<in>{..<card J}. closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D)))"
        proof (intro allI impI)
          fix D assume hD: "D \<subseteq> X"
          show "closedin_on X TX D \<longleftrightarrow>
              (\<forall>i\<in>{..<card J}. closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D))"
          proof
            assume hcl: "closedin_on X TX D"
            show "\<forall>i\<in>{..<card J}. closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D)"
            proof (intro ballI)
              fix i assume "i \<in> {..<card J}"
              hence "f i \<in> J" using hf_surj by (by100 blast)
              from hweak hD hcl this show "closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D)"
                unfolding C'_def by (by100 blast)
            qed
          next
            assume hall: "\<forall>i\<in>{..<card J}. closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D)"
            have "\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
            proof (intro ballI)
              fix \<alpha> assume "\<alpha> \<in> J"
              hence "\<alpha> \<in> f ` {..<card J}" using hf_surj by (by100 simp)
              then obtain i where hi: "i \<in> {..<card J}" and hfi: "f i = \<alpha>" by (by100 auto)
              from hall[rule_format, OF hi]
              show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
                unfolding C'_def using hfi by (by100 simp)
            qed
            thus "closedin_on X TX D" using hweak[rule_format, OF hD] by (by100 simp)
          qed
        qed
        show "(\<forall>i\<in>{..<card J}. C' i \<subseteq> X \<and> p \<in> C' i
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C' i) (subspace_topology X TX (C' i)) h))
            \<and> (\<Union>i\<in>{..<card J}. C' i) = X
            \<and> (\<forall>i\<in>{..<card J}. \<forall>j\<in>{..<card J}. i \<noteq> j \<longrightarrow> C' i \<inter> C' j = {p})
            \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
                 (closedin_on X TX D \<longleftrightarrow>
                  (\<forall>i\<in>{..<card J}. closedin_on (C' i) (subspace_topology X TX (C' i)) (C' i \<inter> D))))"
          using hC'_props hcover' hdisjoint' hweak' by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply Theorem 71.1 to the relabeled wedge.\<close>
    from Theorem_71_1_wedge_of_circles_finite[OF hwedge']
    obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int" where
      hfree0: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<card J}" and
      hiso0: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)"
      by (by100 blast)
    \<comment> \<open>Relabel generators: \<iota>'(\<alpha>) = \<iota>0(f^{-1}(\<alpha>)) for \<alpha> \<in> J.\<close>
    let ?finv = "inv_into {..<card J} f"
    define \<iota>' where "\<iota>' \<alpha> = \<iota>0 (?finv \<alpha>)" for \<alpha>
    have hfinv_in: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> ?finv \<alpha> \<in> {..<card J}"
    proof -
      fix \<alpha> assume "\<alpha> \<in> J"
      hence "\<alpha> \<in> f ` {..<card J}" using hf_surj by (by100 simp)
      thus "?finv \<alpha> \<in> {..<card J}" by (rule inv_into_into)
    qed
    have hfinv_f: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> f (?finv \<alpha>) = \<alpha>"
    proof -
      fix \<alpha> assume "\<alpha> \<in> J"
      hence "\<alpha> \<in> f ` {..<card J}" using hf_surj by (by100 simp)
      thus "f (?finv \<alpha>) = \<alpha>" by (rule f_inv_into_f)
    qed
    have hf_finv: "\<And>i. i \<in> {..<card J} \<Longrightarrow> ?finv (f i) = i"
      using hf_inj by (rule inv_into_f_f)
    have hfree': "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>' J"
      unfolding top1_is_free_group_full_on_def
    proof (intro conjI allI impI)
      show "top1_is_group_on G0 mul0 e0 invg0"
        using hfree0 unfolding top1_is_free_group_full_on_def by (by100 blast)
      show "\<forall>s\<in>J. \<iota>' s \<in> G0"
      proof (intro ballI)
        fix s assume "s \<in> J"
        have "?finv s \<in> {..<card J}" by (rule hfinv_in[OF \<open>s \<in> J\<close>])
        thus "\<iota>' s \<in> G0" unfolding \<iota>'_def
          using hfree0 unfolding top1_is_free_group_full_on_def by (by100 blast)
      qed
      show "inj_on \<iota>' J"
      proof (rule inj_onI)
        fix x y assume "x \<in> J" "y \<in> J" "\<iota>' x = \<iota>' y"
        hence "\<iota>0 (?finv x) = \<iota>0 (?finv y)" unfolding \<iota>'_def by (by100 simp)
        moreover have "?finv x \<in> {..<card J}" "?finv y \<in> {..<card J}"
          using hfinv_in \<open>x \<in> J\<close> \<open>y \<in> J\<close> by (by100 blast)+
        moreover have "inj_on \<iota>0 {..<card J}"
          using hfree0 unfolding top1_is_free_group_full_on_def by (by100 blast)
        ultimately have "?finv x = ?finv y" unfolding inj_on_def by (by100 blast)
        hence "f (?finv x) = f (?finv y)" by (by100 simp)
        thus "x = y" using hfinv_f \<open>x \<in> J\<close> \<open>y \<in> J\<close> by (by100 simp)
      qed
      show "G0 = top1_subgroup_generated_on G0 mul0 e0 invg0 (\<iota>' ` J)"
      proof -
        have "\<iota>' ` J = \<iota>0 ` {..<card J}"
        proof
          show "\<iota>' ` J \<subseteq> \<iota>0 ` {..<card J}"
          proof (rule image_subsetI)
            fix \<alpha> assume "\<alpha> \<in> J"
            have "?finv \<alpha> \<in> {..<card J}" by (rule hfinv_in[OF \<open>\<alpha> \<in> J\<close>])
            thus "\<iota>' \<alpha> \<in> \<iota>0 ` {..<card J}" unfolding \<iota>'_def by (by100 blast)
          qed
          show "\<iota>0 ` {..<card J} \<subseteq> \<iota>' ` J"
          proof (rule image_subsetI)
            fix i assume "i \<in> {..<card J}"
            have "f i \<in> J" using hf_surj \<open>i \<in> {..<card J}\<close> by (by100 blast)
            moreover have "\<iota>' (f i) = \<iota>0 i" unfolding \<iota>'_def using hf_finv[OF \<open>i \<in> {..<card J}\<close>]
              by (by100 simp)
            ultimately show "\<iota>0 i \<in> \<iota>' ` J" by (by100 force)
          qed
        qed
        thus ?thesis using hfree0 unfolding top1_is_free_group_full_on_def by (by100 simp)
      qed
      fix ws :: "('i \<times> bool) list"
      assume hws_ne: "ws \<noteq> []"
      assume hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>' s, b)) ws)"
      assume hws_in: "\<forall>i<length ws. fst (ws ! i) \<in> J"
      \<comment> \<open>Relabel ws to use {..<card J}: ws' = map (\<lambda>(s,b). (finv s, b)) ws.\<close>
      let ?ws' = "map (\<lambda>(s, b). (?finv s, b)) ws"
      have hws'_ne: "?ws' \<noteq> []" using hws_ne by (by100 simp)
      have hws'_in: "\<forall>i<length ?ws'. fst (?ws' ! i) \<in> {..<card J}"
      proof (intro allI impI)
        fix i assume "i < length ?ws'"
        hence "i < length ws" by (by100 simp)
        hence "fst (ws ! i) \<in> J" using hws_in by (by100 blast)
        hence hfst_J: "fst (ws ! i) \<in> J" using hws_in by (by100 blast)
        have "?finv (fst (ws ! i)) \<in> {..<card J}" by (rule hfinv_in[OF hfst_J])
        moreover obtain s b where hsb: "ws ! i = (s, b)" by (cases "ws ! i")
        ultimately show "fst (?ws' ! i) \<in> {..<card J}"
          using \<open>i < length ws\<close> by (by100 simp)
      qed
      have hmap_eq: "map (\<lambda>(s, b). (\<iota>' s, b)) ws = map (\<lambda>(s, b). (\<iota>0 s, b)) ?ws'"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>(s, b). (\<iota>' s, b)) ws) = length (map (\<lambda>(s, b). (\<iota>0 s, b)) ?ws')"
          by (by100 simp)
        fix i assume "i < length (map (\<lambda>(s, b). (\<iota>' s, b)) ws)"
        hence hi: "i < length ws" by (by100 simp)
        obtain s b where hsb: "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
        show "map (\<lambda>(s, b). (\<iota>' s, b)) ws ! i = map (\<lambda>(s, b). (\<iota>0 s, b)) ?ws' ! i"
          using hi hsb unfolding \<iota>'_def by (by100 auto)
      qed
      have hred': "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>0 s, b)) ?ws')"
        using hred hmap_eq by (by100 simp)
      have hfree0_words: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>0 s, b)) ws')
          \<Longrightarrow> (\<forall>i<length ws'. fst (ws' ! i) \<in> {..<card J})
          \<Longrightarrow> top1_group_word_product mul0 e0 invg0 (map (\<lambda>(s, b). (\<iota>0 s, b)) ws') \<noteq> e0"
        using hfree0 unfolding top1_is_free_group_full_on_def by (by100 blast)
      from hfree0_words[OF hws'_ne hred' hws'_in]
      have "top1_group_word_product mul0 e0 invg0 (map (\<lambda>(s, b). (\<iota>0 s, b)) ?ws') \<noteq> e0" .
      hence "top1_group_word_product mul0 e0 invg0 (map (\<lambda>(s, b). (\<iota>' s, b)) ws) \<noteq> e0"
        by (subst hmap_eq) (by100 assumption)
      thus "top1_group_word_product mul0 e0 invg0 (map (\<lambda>(s, b). (\<iota>' s, b)) ws) \<noteq> e0" .
    qed
    show ?thesis using hfree' hiso0 by (by100 blast)
  next
    case False
    \<comment> \<open>Infinite case: direct limit argument.\<close>
    show ?thesis sorry \<comment> \<open>Direct limit argument for infinite J: finite sub-wedges + compactness.\<close>
  qed
qed




lemma finite_wedge_pi1_free_with_generators:
  fixes X :: "'a set" and TX :: "'a set set" and J :: "'i set" and p :: 'a
  assumes hwedge: "top1_is_wedge_of_circles_on X TX J p"
      and hfin: "finite J"
  shows "\<exists>(G::int set) mul e invg (\<eta>::'i \<Rightarrow> int) \<Phi>.
      top1_is_free_group_full_on G mul e invg \<eta> J
    \<and> top1_group_iso_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) \<Phi>
    \<and> bij_betw \<Phi> G (top1_fundamental_group_carrier X TX p)"
proof -
  \<comment> \<open>The existing Theorem\_71\_1 already proves freeness + abstract iso.
     We just need to extract bijectivity from the iso.\<close>
  from Theorem_71_3_wedge_of_circles_general[OF hwedge]
  obtain G :: "int set" and mul e invg and \<eta> :: "'i \<Rightarrow> int" where
    hfree: "top1_is_free_group_full_on G mul e invg \<eta> J" and
    hiso: "top1_groups_isomorphic_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)"
    by (by100 blast)
  \<comment> \<open>Extract the isomorphism function \<Phi>.\<close>
  from hiso[unfolded top1_groups_isomorphic_on_def top1_group_iso_on_def]
  obtain \<Phi> where
    h\<Phi>_hom: "top1_group_hom_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) \<Phi>" and
    h\<Phi>_bij: "bij_betw \<Phi> G (top1_fundamental_group_carrier X TX p)"
    by (by100 blast)
  have h\<Phi>_iso: "top1_group_iso_on G mul
      (top1_fundamental_group_carrier X TX p)
      (top1_fundamental_group_mul X TX p) \<Phi>"
    unfolding top1_group_iso_on_def using h\<Phi>_hom h\<Phi>_bij by (by100 blast)
  show ?thesis
    apply (rule exI[of _ G], rule exI[of _ mul], rule exI[of _ e],
           rule exI[of _ invg], rule exI[of _ \<eta>], rule exI[of _ \<Phi>])
    using hfree h\<Phi>_iso h\<Phi>_bij by (by100 blast)
qed

text \<open>Expert Step 8: finite-index wrapper for the witnessed wedge theorem.
  Allows application with arbitrary finite index sets (not just {..<n}).\<close>
lemma finite_wedge_pi1_free_with_chosen_loops_arb:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
    and C :: "'i \<Rightarrow> 'a set" and g :: "'i \<Rightarrow> real \<times> real \<Rightarrow> 'a"
  assumes hwedge: "top1_is_wedge_of_circles_on X TX J p"
      and hfin: "finite J"
      and hg: "\<forall>j\<in>J. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C j) (subspace_topology X TX (C j)) (g j)"
      and hbase: "\<forall>j\<in>J. g j (1, 0) = p"
      and hC_data: "\<forall>j\<in>J. C j \<subseteq> X \<and> p \<in> C j"
      and hC_union: "(\<Union>j\<in>J. C j) = X"
      and hC_disj: "\<forall>i\<in>J. \<forall>j\<in>J. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
      and hC_closed: "\<forall>D\<subseteq>X. closedin_on X TX D \<longleftrightarrow>
          (\<forall>j\<in>J. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))"
  shows "\<exists>(F::int set) mul e invg (\<eta>::'i \<Rightarrow> int) \<Phi>.
      top1_is_free_group_full_on F mul e invg \<eta> J
    \<and> top1_group_iso_on F mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) \<Phi>
    \<and> (\<forall>j\<in>J. \<Phi> (\<eta> j) = {l. top1_loop_equiv_on X TX p
        (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l})"
proof -
  define n where "n = card J"
  \<comment> \<open>Get bijection enum: {..<card J} \<rightarrow> J.\<close>
  from ex_bij_betw_nat_finite[OF hfin] obtain enum where
    henum_raw: "bij_betw enum {0..<card J} J" by (by100 blast)
  have henum: "bij_betw enum {..<n} J"
  proof -
    have "{0..<card J} = {..<card J}" by (by100 auto)
    thus ?thesis using henum_raw unfolding n_def by (by100 simp)
  qed
  define inv_enum where "inv_enum = the_inv_into {..<n} enum"
  have hinv: "bij_betw inv_enum J {..<n}"
    using bij_betw_the_inv_into[OF henum] unfolding inv_enum_def by (by100 blast)
  have henum_inv: "\<forall>j\<in>J. enum (inv_enum j) = j"
    using f_the_inv_into_f_bij_betw[OF henum] unfolding inv_enum_def by (by100 blast)
  have hinv_enum: "\<forall>k<n. inv_enum (enum k) = k"
    using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF henum]] unfolding inv_enum_def by (by100 blast)
  have henum_in: "\<forall>k<n. enum k \<in> J"
    using henum unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Reindex C and g: C'(k) = C(enum(k)), g'(k) = g(enum(k)).\<close>
  define C' where "C' k = C (enum k)" for k
  define g' where "g' k = g (enum k)" for k
  \<comment> \<open>Extract wedge conditions.\<close>
  have hstrict: "is_topology_on_strict X TX"
    using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
  have hhaus: "is_hausdorff_on X TX"
    using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
  have hp_X: "p \<in> X"
    using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
  \<comment> \<open>Transfer conditions from J to {..<n}.\<close>
  have hC'_sub: "\<forall>k<n. C' k \<subseteq> X \<and> p \<in> C' k"
    using hC_data henum_in unfolding C'_def by (by100 blast)
  have hC'_union: "(\<Union>k\<in>{..<n}. C' k) = X"
  proof -
    have "(\<Union>k\<in>{..<n}. C' k) = (\<Union>k\<in>{..<n}. C (enum k))" unfolding C'_def by (by100 simp)
    also have "\<dots> = (\<Union>j\<in>J. C j)"
      using henum unfolding bij_betw_def by (by100 force)
    also have "\<dots> = X" using hC_union by (by100 blast)
    finally show ?thesis .
  qed
  have hC'_disj: "\<forall>i<n. \<forall>k<n. i \<noteq> k \<longrightarrow> C' i \<inter> C' k = {p}"
  proof (intro allI impI)
    fix i k assume "i < n" "k < n" "i \<noteq> k"
    have "enum i \<in> J" using henum_in \<open>i < n\<close> by (by100 blast)
    have "enum k \<in> J" using henum_in \<open>k < n\<close> by (by100 blast)
    have hinj: "inj_on enum {..<n}" using henum unfolding bij_betw_def by (by100 blast)
    have "enum i \<noteq> enum k"
      using hinj \<open>i < n\<close> \<open>k < n\<close> \<open>i \<noteq> k\<close> unfolding inj_on_def by (by100 blast)
    thus "C' i \<inter> C' k = {p}"
      using hC_disj \<open>enum i \<in> J\<close> \<open>enum k \<in> J\<close> \<open>enum i \<noteq> enum k\<close> unfolding C'_def by (by100 blast)
  qed
  have hC'_homeo: "\<forall>k<n. top1_homeomorphism_on top1_S1 top1_S1_topology
      (C' k) (subspace_topology X TX (C' k)) (g' k)"
    using hg henum_in unfolding C'_def g'_def by (by100 blast)
  have hC'_base: "\<forall>k<n. g' k (1, 0) = p"
    using hbase henum_in unfolding g'_def by (by100 blast)
  \<comment> \<open>Coherent topology condition.\<close>
  have hC'_closed: "\<forall>D\<subseteq>X. closedin_on X TX D \<longleftrightarrow>
      (\<forall>k<n. closedin_on (C' k) (subspace_topology X TX (C' k)) (C' k \<inter> D))"
  proof (intro allI impI iffI)
    fix D assume "D \<subseteq> X" "closedin_on X TX D"
    fix k assume "k < n"
    hence "enum k \<in> J" using henum_in by (by100 blast)
    from hC_closed \<open>D \<subseteq> X\<close> \<open>closedin_on X TX D\<close>
    have "\<forall>j\<in>J. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D)" by (by100 blast)
    thus "closedin_on (C' k) (subspace_topology X TX (C' k)) (C' k \<inter> D)"
      using \<open>enum k \<in> J\<close> unfolding C'_def by (by100 blast)
  next
    fix D assume "D \<subseteq> X" "\<forall>k<n. closedin_on (C' k) (subspace_topology X TX (C' k)) (C' k \<inter> D)"
    have "\<forall>j\<in>J. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D)"
    proof
      fix j assume "j \<in> J"
      have "inv_enum j \<in> {..<n}" using hinv \<open>j \<in> J\<close> unfolding bij_betw_def by (by100 blast)
      hence "inv_enum j < n" by (by100 blast)
      have "closedin_on (C' (inv_enum j)) (subspace_topology X TX (C' (inv_enum j)))
          (C' (inv_enum j) \<inter> D)"
        using \<open>\<forall>k<n. closedin_on (C' k) (subspace_topology X TX (C' k)) (C' k \<inter> D)\<close>
        \<open>inv_enum j < n\<close> by (by100 blast)
      moreover have "C' (inv_enum j) = C j"
        unfolding C'_def using henum_inv \<open>j \<in> J\<close> by (by100 simp)
      ultimately show "closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D)"
        by (by100 simp)
    qed
    thus "closedin_on X TX D" using hC_closed \<open>D \<subseteq> X\<close> by (by100 blast)
  qed
  \<comment> \<open>Apply the nat-indexed theorem.\<close>
  from finite_wedge_pi1_free_with_chosen_loops[OF hstrict hhaus hp_X
      hC'_sub hC'_union hC'_disj hC'_homeo hC'_base hC'_closed]
  obtain F mul e invg and \<eta>_nat :: "nat \<Rightarrow> int" and \<Phi> where
    hfree_nat: "top1_is_free_group_full_on F mul e invg \<eta>_nat {..<n}"
    and hiso: "top1_group_iso_on F mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) \<Phi>"
    and hgen_nat: "\<forall>k<n. \<Phi> (\<eta>_nat k) = {l. top1_loop_equiv_on X TX p
        (\<lambda>t. g' k (cos (2 * pi * t), sin (2 * pi * t))) l}"
    by (by5000 blast)
  \<comment> \<open>Reindex: \<eta> j = \<eta>\_nat (inv\_enum j) for j \<in> J.\<close>
  define \<eta> where "\<eta> j = \<eta>_nat (inv_enum j)" for j
  \<comment> \<open>F is free on J via reindexing.\<close>
  have hfree_J: "top1_is_free_group_full_on F mul e invg \<eta> J"
  proof -
    have "\<eta> = \<eta>_nat \<circ> inv_enum" unfolding \<eta>_def comp_def by (by100 simp)
    thus ?thesis using free_group_full_reindex[OF hfree_nat hinv] by (by100 simp)
  qed
  \<comment> \<open>Generator correspondence.\<close>
  have hgen_J: "\<forall>j\<in>J. \<Phi> (\<eta> j) = {l. top1_loop_equiv_on X TX p
      (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
  proof
    fix j assume "j \<in> J"
    have "inv_enum j < n" using hinv \<open>j \<in> J\<close> unfolding bij_betw_def by (by100 blast)
    have "\<Phi> (\<eta> j) = \<Phi> (\<eta>_nat (inv_enum j))" unfolding \<eta>_def by (by100 simp)
    also have "\<dots> = {l. top1_loop_equiv_on X TX p
        (\<lambda>t. g' (inv_enum j) (cos (2 * pi * t), sin (2 * pi * t))) l}"
      using hgen_nat \<open>inv_enum j < n\<close> by (by100 blast)
    also have "g' (inv_enum j) = g j"
      unfolding g'_def using henum_inv \<open>j \<in> J\<close> by (by100 simp)
    finally show "\<Phi> (\<eta> j) = {l. top1_loop_equiv_on X TX p
        (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}" .
  qed
  show ?thesis
    apply (rule exI[of _ F], rule exI[of _ mul], rule exI[of _ e],
           rule exI[of _ invg], rule exI[of _ \<eta>], rule exI[of _ \<Phi>])
    using hfree_J hiso hgen_J by (by100 blast)
qed

text \<open>Helper: foldr of pointwise-equal function lists gives pointwise-equal results.\<close>
lemma foldr_path_product_pointwise_eq:
  fixes xs ys :: "(real \<Rightarrow> 'a) list" and base :: "real \<Rightarrow> 'a"
  assumes hlen: "length xs = length ys"
    and hpw: "\<forall>k<length xs. \<forall>t\<in>I_set. (xs!k) t = (ys!k) t"
  shows "\<forall>t\<in>I_set. foldr top1_path_product xs base t = foldr top1_path_product ys base t"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  from Nil(1) have "ys = []" by (by100 simp)
  thus ?case by (by100 simp)
next
  case (Cons f rest)
  then obtain g rest' where hys: "ys = g # rest'" by (cases ys) (by100 simp)+
  have hlen': "length rest = length rest'" using Cons(2) hys by (by100 simp)
  have hpw_rest: "\<forall>k<length rest. \<forall>t\<in>I_set. (rest!k) t = (rest'!k) t"
    using Cons(3) hys by (by100 force)
  have hpw_head: "\<forall>t\<in>I_set. f t = g t"
    using Cons(3) hys by (by100 force)
  have hIH: "\<forall>t\<in>I_set. foldr top1_path_product rest base t
      = foldr top1_path_product rest' base t"
    using Cons(1)[OF hlen' hpw_rest] .
  show ?case unfolding hys
  proof (intro ballI)
    fix t assume ht: "t \<in> I_set"
    show "foldr top1_path_product (f # rest) base t
        = foldr top1_path_product (g # rest') base t"
    proof (cases "t \<le> 1/2")
      case True
      have "2*t \<in> I_set" using ht True unfolding top1_unit_interval_def by (by100 auto)
      thus ?thesis unfolding top1_path_product_def using True hpw_head by (by100 simp)
    next
      case False
      have h2t1: "2*t-1 \<in> I_set" using ht False unfolding top1_unit_interval_def by (by100 auto)
      have "foldr top1_path_product rest base (2*t-1) = foldr top1_path_product rest' base (2*t-1)"
        using hIH h2t1 by (by100 blast)
      thus ?thesis unfolding top1_path_product_def using False by (by100 simp)
    qed
  qed
qed

text \<open>Helper: word\_product in \<pi>_1 = class of foldr path product.
  By induction: each \<pi>_1 multiplication step corresponds to a path\_product step.\<close>
lemma word_product_foldr_class:
  assumes hTA: "is_topology_on Y TY"
    and hloops: "\<forall>k<length ws. top1_is_loop_on Y TY y0 (fs k)"
    and hmatch: "\<forall>k<length ws.
        {g. top1_loop_equiv_on Y TY y0 (fs k) g}
      = (if snd (ws!k) then fst (ws!k)
         else top1_fundamental_group_invg Y TY y0 (fst (ws!k)))"
  shows "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0)
      ws
    = {g. top1_loop_equiv_on Y TY y0
        (foldr top1_path_product (map fs [0..<length ws]) (top1_constant_path y0)) g}"
  using assms
proof (induction ws arbitrary: fs)
  case Nil
  show ?case unfolding top1_fundamental_group_id_def by (by100 simp)
next
  case (Cons w rest)
  obtain x b where hw: "w = (x, b)" by (cases w) (by100 blast)
  \<comment> \<open>Shifted fs for the tail.\<close>
  define fs' where "fs' k = fs (Suc k)" for k
  have hloops': "\<forall>k<length rest. top1_is_loop_on Y TY y0 (fs' k)"
    using Cons(3) unfolding fs'_def by (by100 force)
  have hmatch': "\<forall>k<length rest.
      {g. top1_loop_equiv_on Y TY y0 (fs' k) g}
    = (if snd (rest!k) then fst (rest!k)
       else top1_fundamental_group_invg Y TY y0 (fst (rest!k)))"
    using Cons(4) unfolding fs'_def hw by (by100 force)
  \<comment> \<open>IH gives word\_product rest = class of foldr rest.\<close>
  have hIH: "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) rest
    = {g. top1_loop_equiv_on Y TY y0
        (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}"
    using Cons(1)[OF Cons(2) hloops' hmatch'] .
  \<comment> \<open>fs 0 is a loop, and its class matches w.\<close>
  have hfs0_loop: "top1_is_loop_on Y TY y0 (fs 0)"
    using Cons(3) by (by100 force)
  have hfs0_class: "{g. top1_loop_equiv_on Y TY y0 (fs 0) g}
      = (if b then x else top1_fundamental_group_invg Y TY y0 x)"
    using Cons(4) hw by (by100 force)
  \<comment> \<open>The foldr of the rest is a loop.\<close>
  have hfoldr_loop: "top1_is_loop_on Y TY y0
      (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))"
  proof -
    have hy0_Y: "y0 \<in> Y"
    proof -
      have hfs0: "top1_is_loop_on Y TY y0 (fs 0)" using Cons(3) by (by100 force)
      have "fs 0 0 = y0" using hfs0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
      moreover have "fs 0 0 \<in> Y" using hfs0 \<open>0 \<in> I_set\<close>
        unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hconst: "top1_is_loop_on Y TY y0 (top1_constant_path y0)"
      using top1_constant_path_is_loop[OF hTA hy0_Y] .
    have hloops_set: "\<forall>g \<in> set (map fs' [0..<length rest]). top1_is_loop_on Y TY y0 g"
      using hloops' by (by100 force)
    show ?thesis using foldr_path_product_loops_is_loop[OF hTA hconst hloops_set] .
  qed
  \<comment> \<open>Apply top1\_fundamental\_group\_mul\_class.\<close>
  have hmul: "top1_fundamental_group_mul Y TY y0
      {g. top1_loop_equiv_on Y TY y0 (fs 0) g}
      {g. top1_loop_equiv_on Y TY y0
          (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}
    = {g. top1_loop_equiv_on Y TY y0
          (top1_path_product (fs 0)
            (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))) g}"
    using top1_fundamental_group_mul_class[OF hTA hfs0_loop hfoldr_loop] .
  \<comment> \<open>word\_product (w#rest) = \<pi>_1\_mul(x\^b, word\_product rest).\<close>
  have hstep: "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) (w # rest)
    = top1_fundamental_group_mul Y TY y0
        (if b then x else top1_fundamental_group_invg Y TY y0 x)
        (top1_group_word_product
          (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
          (top1_fundamental_group_invg Y TY y0) rest)"
    unfolding hw by (cases b) (by100 simp)+
  \<comment> \<open>Substitute class(fs 0) for x\^b, and IH for word\_product rest.\<close>
  have "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) (w # rest)
    = top1_fundamental_group_mul Y TY y0
        {g. top1_loop_equiv_on Y TY y0 (fs 0) g}
        {g. top1_loop_equiv_on Y TY y0
            (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}"
    using hstep hfs0_class hIH by (by100 simp)
  \<comment> \<open>= class of (fs 0 * foldr rest const) by mul\_class.\<close>
  also have "\<dots> = {g. top1_loop_equiv_on Y TY y0
      (top1_path_product (fs 0)
        (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))) g}"
    using hmul .
  \<comment> \<open>= class of foldr (map fs [0..<Suc(length rest)]) const.\<close>
  also have "top1_path_product (fs 0)
      (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))
    = foldr top1_path_product (map fs [0..<length (w # rest)]) (top1_constant_path y0)"
  proof -
    have "map fs [0..<Suc (length rest)] = fs 0 # map fs' [0..<length rest]"
      unfolding fs'_def using upt_rec[of 0 "Suc (length rest)"] map_Suc_upt[of 0 "length rest", symmetric]
      by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  finally show ?case .
qed

text \<open>Helper: two loops that agree pointwise on I\_set have the same loop-equiv class.
  Proof: the constant homotopy H(s,t) = f(s) witnesses path\_homotopic\_on f g,
  since f(s) = g(s) for all s \<in> I\_set.\<close>
lemma loop_equiv_class_pointwise_I:
  assumes hTA: "is_topology_on X TX"
    and hf: "top1_is_loop_on X TX x0 f"
    and hg: "top1_is_loop_on X TX x0 g"
    and hpw: "\<forall>t\<in>I_set. f t = g t"
  shows "{l. top1_loop_equiv_on X TX x0 f l} = {l. top1_loop_equiv_on X TX x0 g l}"
proof -
  \<comment> \<open>f and g are path-homotopic via the constant homotopy H(s,t) = f(s).\<close>
  have hfg: "top1_path_homotopic_on X TX x0 x0 f g"
    unfolding top1_path_homotopic_on_def
  proof (intro conjI)
    show "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def by (by100 blast)
    show "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def by (by100 blast)
    \<comment> \<open>The homotopy H(s,t) = f(s). H is continuous because f is continuous and H doesn't depend on t.\<close>
    define H where "H p = f (fst p)" for p :: "real \<times> real"
    show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F
        \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s)
        \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x0)"
    proof (rule exI[of _ H], intro conjI)
      \<comment> \<open>H(s,0) = f(s).\<close>
      show "\<forall>s\<in>I_set. H (s, 0) = f s" unfolding H_def by (by100 simp)
      \<comment> \<open>H(s,1) = f(s) = g(s) for s \<in> I\_set.\<close>
      show "\<forall>s\<in>I_set. H (s, 1) = g s" unfolding H_def using hpw by (by100 simp)
      \<comment> \<open>H(0,t) = f(0) = x0.\<close>
      show "\<forall>t\<in>I_set. H (0, t) = x0" unfolding H_def
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      \<comment> \<open>H(1,t) = f(1) = x0.\<close>
      show "\<forall>t\<in>I_set. H (1, t) = x0" unfolding H_def
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      \<comment> \<open>H is continuous: H = f \<circ> fst, composition of continuous maps.\<close>
      show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H"
      proof -
        have hI_top: "is_topology_on I_set I_top"
          using top1_unit_interval_topology_is_topology_on by (by100 blast)
        have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (\<lambda>p. f (fst p))"
          using homotopy_const_continuous[OF hf_cont hI_top] by (by100 blast)
        moreover have "\<And>p. f (fst p) = H p" unfolding H_def by (by100 simp)
        ultimately show ?thesis unfolding II_topology_def by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>loop\_equiv is an equivalence relation, so equiv classes of equivalent elements are equal.\<close>
  have hfg_equiv: "top1_loop_equiv_on X TX x0 f g"
    unfolding top1_loop_equiv_on_def using hf hg hfg by (by100 blast)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix l
    assume "l \<in> {l. top1_loop_equiv_on X TX x0 f l}"
    hence "top1_loop_equiv_on X TX x0 f l" by (by100 blast)
    hence hl: "top1_is_loop_on X TX x0 l" and hfl: "top1_path_homotopic_on X TX x0 x0 f l"
      unfolding top1_loop_equiv_on_def by (by100 blast)+
    have "top1_path_homotopic_on X TX x0 x0 g l"
    proof -
      have hgf: "top1_path_homotopic_on X TX x0 x0 g f"
        using Lemma_51_1_path_homotopic_sym[OF hfg] by (by100 blast)
      from Lemma_51_1_path_homotopic_trans[OF hTA hgf hfl]
      show ?thesis .
    qed
    thus "l \<in> {l. top1_loop_equiv_on X TX x0 g l}"
      unfolding top1_loop_equiv_on_def using hg hl by (by100 blast)
  next
    fix l
    assume "l \<in> {l. top1_loop_equiv_on X TX x0 g l}"
    hence "top1_loop_equiv_on X TX x0 g l" by (by100 blast)
    hence hl: "top1_is_loop_on X TX x0 l" and hgl: "top1_path_homotopic_on X TX x0 x0 g l"
      unfolding top1_loop_equiv_on_def by (by100 blast)+
    have "top1_path_homotopic_on X TX x0 x0 f l"
      using Lemma_51_1_path_homotopic_trans[OF hTA hfg hgl] .
    thus "l \<in> {l. top1_loop_equiv_on X TX x0 f l}"
      unfolding top1_loop_equiv_on_def using hf hl by (by100 blast)
  qed
qed

theorem Theorem_74_2_scheme_presentation:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
    and scheme :: "(nat \<times> bool) list"
  assumes hscheme: "top1_quotient_of_scheme_on X TX scheme"
      and hx0: "x0 \<in> X"
      and hlen: "length scheme \<ge> 3"
      \<comment> \<open>All vertices map to x0 (book: "\<pi> maps all vertices to a single point x_0").\<close>
      and hvert: "\<exists>P q vx vy. top1_is_polygonal_region_on P (length scheme)
          \<and> top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
          \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
          \<and> (\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j))
          \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)))"
      \<comment> \<open>Each label has a True-direction edge (Munkres convention: counterclockwise).\<close>
      and htrue_dir: "\<forall>\<alpha>\<in>fst ` set scheme.
          \<exists>i<length scheme. fst (scheme!i) = \<alpha> \<and> snd (scheme!i) = True"
      \<comment> \<open>Vertex connectivity: the scheme's label graph connects all vertices.\<close>
      and hvert_conn_assm: "\<forall>(q::real\<times>real\<Rightarrow>'a) (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
          (\<forall>i<length scheme. \<forall>j<length scheme.
            fst (scheme!i) = fst (scheme!j) \<longrightarrow>
            (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
               (1-t) * vy i + t * vy (Suc i mod length scheme))
             = (if snd (scheme!i) = snd (scheme!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                        (1-t) * vy j + t * vy (Suc j mod length scheme))
                else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                        t * vy j + (1-t) * vy (Suc j mod length scheme)))))
          \<longrightarrow> (\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j))"
  shows "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
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
    hvert_id: "\<forall>i<length scheme. \<forall>j<length scheme. q (vxP i, vyP i) = q (vxP j, vyP j)" and
    hno_extra: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vxP i + t * vxP (Suc i mod length scheme),
             (1-t) * vyP i + t * vyP (Suc i mod length scheme))
        = q ((1-s) * vxP j + s * vxP (Suc j mod length scheme),
             (1-s) * vyP j + s * vyP (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    by (elim conjE exE) (rule that, assumption+)
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  \<comment> \<open>Step 2 (book): "A = \<pi>(Bd P) is a wedge of k circles."
     Since all vertices are identified by q, the boundary edges become loops in X.
     Edges with the same label are identified, giving k distinct circles.
     All circles share the common point x0 = q(vertex).\<close>
  let ?k = "card (fst ` set scheme)"
  \<comment> \<open>Step 2-5 combined: Get CW data, show A is a wedge, apply Theorem 72.1.\<close>
  \<comment> \<open>Use scheme\_quotient\_CW\_data to get a single A with all properties.\<close>
  from scheme_quotient_CW_data[OF hscheme hlen hvert_conn_assm]
  obtain A h a qC vxC vyC where hA_cl: "closedin_on X TX A"
      and hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
      and hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and ha_A: "a \<in> A"
      and hh_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
          (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          (X - A) (subspace_topology X TX (X - A)) h"
      and hh_S1: "h ` top1_S1 \<subseteq> A"
      and hh_S1': "\<forall>z\<in>top1_S1. h z \<in> A"
      and hA_eq: "A = qC ` (\<Union>i<length scheme. {((1-t) * vxC i + t * vxC (Suc i mod length scheme),
                   (1-t) * vyC i + t * vyC (Suc i mod length scheme)) | t. t \<in> I_set})"
      and ha_eq: "a = qC (vxC 0, vyC 0)"
      and hvert_C: "\<forall>i<length scheme. \<forall>j<length scheme. qC (vxC i, vyC i) = qC (vxC j, vyC j)"
      and hedge_C: "\<forall>i<length scheme. \<forall>j<length scheme.
          fst (scheme!i) = fst (scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. qC ((1-t) * vxC i + t * vxC (Suc i mod length scheme),
              (1-t) * vyC i + t * vyC (Suc i mod length scheme))
           = (if snd (scheme!i) = snd (scheme!j)
              then qC ((1-t) * vxC j + t * vxC (Suc j mod length scheme),
                      (1-t) * vyC j + t * vyC (Suc j mod length scheme))
              else qC (t * vxC j + (1-t) * vxC (Suc j mod length scheme),
                      t * vyC j + (1-t) * vyC (Suc j mod length scheme))))"
      and hno_C: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          qC ((1-t) * vxC i + t * vxC (Suc i mod length scheme),
             (1-t) * vyC i + t * vyC (Suc i mod length scheme))
        = qC ((1-s) * vxC j + s * vxC (Suc j mod length scheme),
             (1-s) * vyC j + s * vyC (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
      and hqC_edge_cont: "\<forall>i<length scheme.
          top1_continuous_map_on I_set top1_unit_interval_topology A (subspace_topology X TX A)
            (\<lambda>t. qC ((1-t) * vxC i + t * vxC (Suc i mod length scheme),
                      (1-t) * vyC i + t * vyC (Suc i mod length scheme)))"
      and hh_edge_arc: "\<forall>i<length scheme. \<forall>t\<in>I_set.
          h (cos (2 * pi * (real i + t) / real (length scheme)),
             sin (2 * pi * (real i + t) / real (length scheme)))
        = qC ((1-t) * vxC i + t * vxC (Suc i mod length scheme),
             (1-t) * vyC i + t * vyC (Suc i mod length scheme))"
    by - (erule exE, erule exE, erule exE, erule exE, erule exE, erule exE,
          (erule conjE)+, rule that, assumption+)
  \<comment> \<open>For each label \<alpha> \<in> J, pick a canonical TRUE-direction edge index i(\<alpha>).
     Defined ONCE at \<S>74.2 scope so all sub-proofs use the same constant.\<close>
  define i_of where "i_of \<alpha> = (SOME i. i < length scheme \<and> fst (scheme!i) = \<alpha> \<and> snd (scheme!i) = True)" for \<alpha>
  have hi_of: "\<And>\<alpha>. \<alpha> \<in> fst ` set scheme \<Longrightarrow>
      i_of \<alpha> < length scheme \<and> fst (scheme!(i_of \<alpha>)) = \<alpha> \<and> snd (scheme!(i_of \<alpha>)) = True"
  proof -
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> fst ` set scheme"
    have "\<exists>i. i < length scheme \<and> fst (scheme!i) = \<alpha> \<and> snd (scheme!i) = True"
      using htrue_dir h\<alpha> by (by100 blast)
    thus "i_of \<alpha> < length scheme \<and> fst (scheme!(i_of \<alpha>)) = \<alpha> \<and> snd (scheme!(i_of \<alpha>)) = True"
      unfolding i_of_def by (rule someI_ex)
  qed
  \<comment> \<open>Step 2 (book): "A is a wedge of k circles." (Using the SAME A from CW data.)\<close>
  have hA_wd_and_gen: "top1_is_wedge_of_circles_on A (subspace_topology X TX A) (fst ` set scheme) a
    \<and> (\<exists>\<iota>A. top1_is_free_group_full_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
        (top1_fundamental_group_mul A (subspace_topology X TX A) a)
        (top1_fundamental_group_id A (subspace_topology X TX A) a)
        (top1_fundamental_group_invg A (subspace_topology X TX A) a)
        \<iota>A (fst ` set scheme)
      \<and> (\<forall>s\<in>fst ` set scheme. \<iota>A s =
          {l. top1_loop_equiv_on A (subspace_topology X TX A) a
            (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                      (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme))) l}))"
  proof -
    \<comment> \<open>Abbreviations.\<close>
    let ?n = "length scheme"
    let ?TA = "subspace_topology X TX A"
    let ?J = "fst ` set scheme"
    have hn_pos: "?n > 0" using hlen by (by100 linarith)
    \<comment> \<open>Prerequisites: strict topology and Hausdorff for A.\<close>
    have hX_s: "is_topology_on_strict X TX"
      using hscheme unfolding top1_quotient_of_scheme_on_def by (by100 blast)
    have hX_h: "is_hausdorff_on X TX"
      by (rule scheme_quotient_hausdorff[OF hscheme hlen])
    have hA_sub: "A \<subseteq> X" using hA_cl closedin_sub by (by100 blast)
    have hA_strict: "is_topology_on_strict A ?TA"
      using subspace_topology_is_strict[OF hX_s hA_sub] by (by100 blast)
    have hA_haus: "is_hausdorff_on A ?TA"
      using Theorem_17_11 hX_h hA_sub by (by100 blast)

    \<comment> \<open>i\_of and hi\_of now at \<S>74.2 outer scope (line ~8955).\<close>

    \<comment> \<open>Define the edge map for index i: edge\_i(t) = (1-t)*v_i + t*v_{i+1}.\<close>
    define edge_pt where "edge_pt i t = ((1-t) * vxC i + t * vxC (Suc i mod ?n),
                                         (1-t) * vyC i + t * vyC (Suc i mod ?n))" for i t

    \<comment> \<open>Define C(\<alpha>) = qC ` {edge_{i(\<alpha>)}(t) | t \<in> I\_set}.\<close>
    define C where "C \<alpha> = qC ` {edge_pt (i_of \<alpha>) t | t. t \<in> I_set}" for \<alpha>

    \<comment> \<open>--- (A) C(\<alpha>) \<subseteq> A for each \<alpha> \<in> J ---\<close>
    have hC_sub: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> C \<alpha> \<subseteq> A"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have hi: "i_of \<alpha> < ?n" using hi_of[OF h\<alpha>] by (by100 blast)
      show "C \<alpha> \<subseteq> A" unfolding C_def hA_eq edge_pt_def
        using hi by (by100 blast)
    qed

    \<comment> \<open>--- (B) a \<in> C(\<alpha>) for each \<alpha> \<in> J ---\<close>
    have ha_C: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> a \<in> C \<alpha>"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have hi: "i_of \<alpha> < ?n" using hi_of[OF h\<alpha>] by (by100 blast)
      have "edge_pt (i_of \<alpha>) 0 = (vxC (i_of \<alpha>), vyC (i_of \<alpha>))"
        unfolding edge_pt_def by (by100 simp)
      have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "qC (edge_pt (i_of \<alpha>) 0) \<in> C \<alpha>" unfolding C_def using h0_I by (by100 blast)
      moreover have "qC (edge_pt (i_of \<alpha>) 0) = qC (vxC (i_of \<alpha>), vyC (i_of \<alpha>))"
        unfolding edge_pt_def by (by100 simp)
      moreover have "qC (vxC (i_of \<alpha>), vyC (i_of \<alpha>)) = qC (vxC 0, vyC 0)"
        using hvert_C hi hn_pos by (by100 blast)
      moreover have "qC (vxC 0, vyC 0) = a" using ha_eq by (by100 simp)
      ultimately show "a \<in> C \<alpha>" by (by100 simp)
    qed

    \<comment> \<open>--- (C) \<Union>{C(\<alpha>) | \<alpha> \<in> J} = A ---\<close>
    have hC_union: "(\<Union>\<alpha> \<in> ?J. C \<alpha>) = A"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> (\<Union>\<alpha> \<in> ?J. C \<alpha>)"
      then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> ?J" "x \<in> C \<alpha>" by (by100 blast)
      thus "x \<in> A" using hC_sub by (by100 blast)
    next
      fix x assume "x \<in> A"
      then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
        and hx: "x = qC (edge_pt i t)"
        unfolding hA_eq edge_pt_def by (by100 blast)
      let ?\<alpha> = "fst (scheme!i)"
      have h\<alpha>J: "?\<alpha> \<in> ?J" using hi by (by100 force)
      have hi\<alpha>: "i_of ?\<alpha> < ?n" "fst (scheme!(i_of ?\<alpha>)) = ?\<alpha>"
        using hi_of[OF h\<alpha>J] by (by100 blast)+
      \<comment> \<open>Same label: hedge\_C says qC(edge\_i(t)) = qC(edge\_{i(\<alpha>)}(t')) for appropriate t'.\<close>
      have hsame_label: "fst (scheme!i) = fst (scheme!(i_of ?\<alpha>))" using hi\<alpha>(2) by (by100 simp)
      \<comment> \<open>By hedge\_C, the image of edge\_i under qC equals the image of edge\_{i(\<alpha>)} under qC.\<close>
      have "x \<in> C ?\<alpha>"
      proof -
        have hhedge: "qC (edge_pt i t)
          = (if snd (scheme!i) = snd (scheme!(i_of ?\<alpha>))
             then qC (edge_pt (i_of ?\<alpha>) t)
             else qC ((t * vxC (i_of ?\<alpha>) + (1-t) * vxC (Suc (i_of ?\<alpha>) mod ?n),
                       t * vyC (i_of ?\<alpha>) + (1-t) * vyC (Suc (i_of ?\<alpha>) mod ?n))))"
          using hedge_C hi hi\<alpha>(1) hsame_label ht
          unfolding edge_pt_def by (by5000 metis)
        show ?thesis
        proof (cases "snd (scheme!i) = snd (scheme!(i_of ?\<alpha>))")
          case True
          hence "qC (edge_pt i t) = qC (edge_pt (i_of ?\<alpha>) t)"
            using hhedge by (by100 simp)
          hence "x = qC (edge_pt (i_of ?\<alpha>) t)" using hx by (by100 simp)
          thus ?thesis unfolding C_def using ht by (by100 blast)
        next
          case False
          \<comment> \<open>Reversed orientation: t \<mapsto> 1-t.\<close>
          let ?t' = "1 - t"
          have ht': "?t' \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
          have "qC (edge_pt i t) = qC ((t * vxC (i_of ?\<alpha>) + (1-t) * vxC (Suc (i_of ?\<alpha>) mod ?n),
                       t * vyC (i_of ?\<alpha>) + (1-t) * vyC (Suc (i_of ?\<alpha>) mod ?n)))"
            using hhedge False by (by100 simp)
          moreover have "((t * vxC (i_of ?\<alpha>) + (1-t) * vxC (Suc (i_of ?\<alpha>) mod ?n),
                       t * vyC (i_of ?\<alpha>) + (1-t) * vyC (Suc (i_of ?\<alpha>) mod ?n)))
                       = edge_pt (i_of ?\<alpha>) ?t'"
            unfolding edge_pt_def by (by5000 auto)
          ultimately have "x = qC (edge_pt (i_of ?\<alpha>) ?t')" using hx by (by100 simp)
          thus ?thesis unfolding C_def using ht' by (by100 blast)
        qed
      qed
      thus "x \<in> (\<Union>\<alpha> \<in> ?J. C \<alpha>)" using h\<alpha>J by (by100 blast)
    qed

    \<comment> \<open>--- (D) C(\<alpha>) \<inter> C(\<beta>) = {a} for \<alpha> \<noteq> \<beta> ---\<close>
    have hC_disj: "\<And>\<alpha> \<beta>. \<alpha> \<in> ?J \<Longrightarrow> \<beta> \<in> ?J \<Longrightarrow> \<alpha> \<noteq> \<beta> \<Longrightarrow> C \<alpha> \<inter> C \<beta> = {a}"
    proof -
      fix \<alpha> \<beta> assume h\<alpha>: "\<alpha> \<in> ?J" and h\<beta>: "\<beta> \<in> ?J" and hne: "\<alpha> \<noteq> \<beta>"
      have hi\<alpha>: "i_of \<alpha> < ?n" "fst (scheme!(i_of \<alpha>)) = \<alpha>" using hi_of[OF h\<alpha>] by (by100 blast)+
      have hi\<beta>: "i_of \<beta> < ?n" "fst (scheme!(i_of \<beta>)) = \<beta>" using hi_of[OF h\<beta>] by (by100 blast)+
      have hlabel_ne: "fst (scheme!(i_of \<alpha>)) \<noteq> fst (scheme!(i_of \<beta>))"
        using hi\<alpha>(2) hi\<beta>(2) hne by (by100 simp)
      show "C \<alpha> \<inter> C \<beta> = {a}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> C \<alpha> \<inter> C \<beta>"
        then obtain t s where ht: "t \<in> I_set" and hs: "s \<in> I_set"
          and hxt: "x = qC (edge_pt (i_of \<alpha>) t)"
          and hxs: "x = qC (edge_pt (i_of \<beta>) s)"
          unfolding C_def by (by100 blast)
        have heq: "qC (edge_pt (i_of \<alpha>) t) = qC (edge_pt (i_of \<beta>) s)"
          using hxt hxs by (by100 simp)
        \<comment> \<open>By hno\_C: either (i_of \<alpha> = i_of \<beta> \<and> t = s) or same label. But labels differ!\<close>
        from hno_C have hcase: "(i_of \<alpha> = i_of \<beta> \<and> t = s)
          \<or> (fst (scheme!(i_of \<alpha>)) = fst (scheme!(i_of \<beta>)) \<and>
             (if snd (scheme!(i_of \<alpha>)) = snd (scheme!(i_of \<beta>)) then s = t else s = 1 - t))"
          using hi\<alpha>(1) hi\<beta>(1) ht hs heq unfolding edge_pt_def by (by100 blast)
        \<comment> \<open>The second disjunct is impossible since labels differ.\<close>
        have "i_of \<alpha> = i_of \<beta> \<and> t = s" using hcase hlabel_ne by (by100 blast)
        \<comment> \<open>But i_of \<alpha> = i_of \<beta> implies same label, contradiction.\<close>
        hence "i_of \<alpha> = i_of \<beta>" by (by100 blast)
        hence "fst (scheme!(i_of \<alpha>)) = fst (scheme!(i_of \<beta>))" by (by100 simp)
        hence "\<alpha> = \<beta>" using hi\<alpha>(2) hi\<beta>(2) by (by100 simp)
        hence False using hne by (by100 blast)
        thus "x \<in> {a}" by (by100 blast)
      next
        fix x assume "x \<in> {a}"
        hence "x = a" by (by100 simp)
        thus "x \<in> C \<alpha> \<inter> C \<beta>" using ha_C[OF h\<alpha>] ha_C[OF h\<beta>] by (by100 blast)
      qed
    qed

    \<comment> \<open>--- (E) Homeomorphism S1 to C(alpha) for each alpha ---\<close>
    have hC_homeo: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> \<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) f"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have hi\<alpha>: "i_of \<alpha> < ?n" "fst (scheme!(i_of \<alpha>)) = \<alpha>" using hi_of[OF h\<alpha>] by (by100 blast)+
      \<comment> \<open>Define the edge map f_\<alpha>(t) = qC(edge_{i(\<alpha>)}(t)).\<close>
      define f_\<alpha> where "f_\<alpha> t = qC (edge_pt (i_of \<alpha>) t)" for t
      \<comment> \<open>f_\<alpha> is continuous from I\_set to A.\<close>
      have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f_\<alpha>"
      proof -
        have "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA
            (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                      (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n)))"
          using hqC_edge_cont hi\<alpha>(1) by (by100 blast)
        moreover have "\<And>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                      (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))
                    = f_\<alpha> t"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>f_\<alpha>(0) = a and f_\<alpha>(1) = a.\<close>
      have hf0: "f_\<alpha> 0 = a"
      proof -
        have "f_\<alpha> 0 = qC (vxC (i_of \<alpha>), vyC (i_of \<alpha>))"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        also have "... = qC (vxC 0, vyC 0)"
          using hvert_C hi\<alpha>(1) hn_pos by (by100 blast)
        also have "... = a" using ha_eq by (by100 simp)
        finally show ?thesis .
      qed
      have hf1: "f_\<alpha> 1 = a"
      proof -
        have hi1: "Suc (i_of \<alpha>) mod ?n < ?n" using hn_pos by (by100 simp)
        have "f_\<alpha> 1 = qC (vxC (Suc (i_of \<alpha>) mod ?n), vyC (Suc (i_of \<alpha>) mod ?n))"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        also have "... = qC (vxC 0, vyC 0)"
          using hvert_C hi1 hn_pos by (by100 blast)
        also have "... = a" using ha_eq by (by100 simp)
        finally show ?thesis .
      qed
      \<comment> \<open>f_\<alpha> is a loop in A at basepoint a.\<close>
      have hf_loop: "top1_is_loop_on A ?TA a f_\<alpha>"
        unfolding top1_is_loop_on_def top1_is_path_on_def
        using hf_cont hf0 hf1 by (by100 blast)
      \<comment> \<open>A has a topology.\<close>
      have hA_top: "is_topology_on A ?TA"
        using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>By loop\_factors\_through\_S1: get g : S1 \<to> A continuous with f_\<alpha>(s) = g(R\_to\_S1(s)).\<close>
      from loop_factors_through_S1[OF hA_top hf_loop]
      obtain g where hg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology A ?TA g"
        and hg_base: "g (1, 0) = a"
        and hg_factor: "\<forall>s\<in>I_set. f_\<alpha> s = g (top1_R_to_S1 s)"
        by (by100 blast)
      \<comment> \<open>g is surjective onto C(\<alpha>).\<close>
      have hg_surj: "g ` top1_S1 = C \<alpha>"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> g ` top1_S1"
        then obtain z where "z \<in> top1_S1" "x = g z" by (by100 blast)
        \<comment> \<open>z = R\_to\_S1(t) for some t \<in> I\_set (R\_to\_S1 surjects I\_set onto S1).\<close>
        then obtain t where "t \<in> I_set" "top1_R_to_S1 t = z"
        proof -
          obtain x y where hq_eq: "z = (x, y)" by (cases z)
          have hcirc: "x^2 + y^2 = 1"
            using \<open>z \<in> top1_S1\<close> hq_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "x = cos t0" "y = sin t0"
            using sincos_total_2pi[OF hcirc] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z"
            unfolding top1_R_to_S1_def t'_def hq_eq
            using \<open>x = cos t0\<close> \<open>y = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        hence "x = g (top1_R_to_S1 t)" using \<open>x = g z\<close> by (by100 simp)
        hence "x = f_\<alpha> t" using hg_factor \<open>t \<in> I_set\<close> by (by100 simp)
        hence "x = qC (edge_pt (i_of \<alpha>) t)" unfolding f_\<alpha>_def by (by100 simp)
        thus "x \<in> C \<alpha>" unfolding C_def using \<open>t \<in> I_set\<close> by (by100 blast)
      next
        fix x assume "x \<in> C \<alpha>"
        then obtain t where "t \<in> I_set" "x = qC (edge_pt (i_of \<alpha>) t)"
          unfolding C_def by (by100 blast)
        hence "x = f_\<alpha> t" unfolding f_\<alpha>_def by (by100 simp)
        hence "x = g (top1_R_to_S1 t)" using hg_factor \<open>t \<in> I_set\<close> by (by100 simp)
        moreover have "top1_R_to_S1 t \<in> top1_S1"
          unfolding top1_R_to_S1_def top1_S1_def
          using sin_cos_squared_add[of "2 * pi * t"]
          by (by5000 auto)
        ultimately show "x \<in> g ` top1_S1" by (by100 blast)
      qed
      \<comment> \<open>g is injective on S1.\<close>
      have hg_inj: "inj_on g top1_S1"
      proof (rule inj_onI)
        fix z1 z2 assume hz1: "z1 \<in> top1_S1" and hz2: "z2 \<in> top1_S1" and hgeq: "g z1 = g z2"
        \<comment> \<open>Lift z1, z2 to t1, t2 \<in> I\_set.\<close>
        obtain t1 where ht1: "t1 \<in> I_set" "top1_R_to_S1 t1 = z1"
        proof -
          obtain x1 y1 where hz1_eq: "z1 = (x1, y1)" by (cases z1)
          have hcirc1: "x1^2 + y1^2 = 1"
            using hz1 hz1_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "x1 = cos t0" "y1 = sin t0"
            using sincos_total_2pi[OF hcirc1] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z1"
            unfolding top1_R_to_S1_def t'_def hz1_eq
            using \<open>x1 = cos t0\<close> \<open>y1 = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        obtain t2 where ht2: "t2 \<in> I_set" "top1_R_to_S1 t2 = z2"
        proof -
          obtain x2 y2 where hz2_eq: "z2 = (x2, y2)" by (cases z2)
          have hcirc2: "x2^2 + y2^2 = 1"
            using hz2 hz2_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "x2 = cos t0" "y2 = sin t0"
            using sincos_total_2pi[OF hcirc2] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z2"
            unfolding top1_R_to_S1_def t'_def hz2_eq
            using \<open>x2 = cos t0\<close> \<open>y2 = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        \<comment> \<open>From the factoring: f_\<alpha>(t1) = g(z1) = g(z2) = f_\<alpha>(t2).\<close>
        have "f_\<alpha> t1 = g (top1_R_to_S1 t1)" using hg_factor ht1(1) by (by100 simp)
        also have "... = g z1" using ht1(2) by (by100 simp)
        also have "... = g z2" using hgeq by (by100 simp)
        also have "... = g (top1_R_to_S1 t2)" using ht2(2) by (by100 simp)
        also have "... = f_\<alpha> t2" using hg_factor ht2(1) by (by100 simp)
        finally have hfeq: "f_\<alpha> t1 = f_\<alpha> t2" .
        hence "qC (edge_pt (i_of \<alpha>) t1) = qC (edge_pt (i_of \<alpha>) t2)"
          unfolding f_\<alpha>_def by (by100 simp)
        \<comment> \<open>By hno\_C with i = j = i\_of \<alpha>: t1 = t2.\<close>
        hence "(i_of \<alpha> = i_of \<alpha> \<and> t1 = t2)
          \<or> (fst (scheme!(i_of \<alpha>)) = fst (scheme!(i_of \<alpha>)) \<and>
             (if snd (scheme!(i_of \<alpha>)) = snd (scheme!(i_of \<alpha>)) then t2 = t1 else t2 = 1 - t1))"
          using hno_C hi\<alpha>(1) ht1(1) ht2(1) unfolding edge_pt_def by (by100 blast)
        hence "t1 = t2" by (by100 auto)
        thus "z1 = z2" using ht1(2) ht2(2) by (by100 simp)
      qed
      \<comment> \<open>g is a bijection from S1 to C(\<alpha>).\<close>
      have hg_bij: "bij_betw g top1_S1 (C \<alpha>)"
        unfolding bij_betw_def using hg_inj hg_surj by (by100 blast)
      \<comment> \<open>S1 is compact.\<close>
      have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology" by (rule S1_compact)
      \<comment> \<open>C(\<alpha>) is Hausdorff (subspace of Hausdorff A).\<close>
      have hC_haus: "is_hausdorff_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
        using Theorem_17_11 hA_haus hC_sub[OF h\<alpha>] by (by100 blast)
      \<comment> \<open>S1 topology and C(\<alpha>) topology.\<close>
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hC_top: "is_topology_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
      proof -
        have "is_topology_on_strict (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
          using subspace_topology_is_strict[OF hA_strict hC_sub[OF h\<alpha>]] by (by100 blast)
        thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
      qed
      \<comment> \<open>Restrict g to codomain C(\<alpha>).\<close>
      have hg_cont_C: "top1_continuous_map_on top1_S1 top1_S1_topology
            (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) g"
      proof -
        have himg: "g ` top1_S1 \<subseteq> C \<alpha>" using hg_surj by (by100 blast)
        have hCsub: "C \<alpha> \<subseteq> A" using hC_sub[OF h\<alpha>] .
        \<comment> \<open>Use Theorem\_18\_2 restrict\_range.\<close>
        from Theorem_18_2[OF hS1_top hA_top hA_top]
        have "\<forall>W f. top1_continuous_map_on top1_S1 top1_S1_topology A ?TA f \<and>
                     W \<subseteq> A \<and> f ` top1_S1 \<subseteq> W
                     \<longrightarrow> top1_continuous_map_on top1_S1 top1_S1_topology W (subspace_topology A ?TA W) f"
          by (by100 blast)
        thus ?thesis using hg_cont hCsub himg by (by100 blast)
      qed
      \<comment> \<open>By Theorem 26.6: compact + Hausdorff + continuous bijection = homeomorphism.\<close>
      have "top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) g"
        using Theorem_26_6[OF hS1_top hC_top hS1_compact hC_haus hg_cont_C hg_bij] by (by100 blast)
      thus "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) f"
        by (by100 blast)
    qed

    \<comment> \<open>--- (F) Weak topology condition ---\<close>
    \<comment> \<open>Finiteness of the index set J.\<close>
    have hJ_finite: "finite ?J" by (by100 simp)

    \<comment> \<open>Each C(\<alpha>) is compact (continuous image of compact I\_set via edge map).\<close>
    have hC_compact: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> top1_compact_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have hi\<alpha>: "i_of \<alpha> < ?n" using hi_of[OF h\<alpha>] by (by100 blast)
      \<comment> \<open>The edge map f(t) = qC(edge(t)) is continuous from I\_set to A.\<close>
      let ?f = "\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                         (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))"
      have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA ?f"
        using hqC_edge_cont hi\<alpha> by (by100 blast)
      \<comment> \<open>I\_set is compact.\<close>
      have hI_compact: "top1_compact_on I_set top1_unit_interval_topology"
      proof -
        have "compact {0..1::real}" by (rule compact_Icc)
        have "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (by5000 auto)
        have "compact I_set" using \<open>compact {0..1::real}\<close> \<open>I_set = _\<close> by (by100 simp)
        have "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by (by100 simp)
        thus ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      have hA_top: "is_topology_on A ?TA"
        using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>?f(I\_set) = C(\<alpha>).\<close>
      have himg: "?f ` I_set = C \<alpha>"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> ?f ` I_set"
        then obtain t where "t \<in> I_set" "x = ?f t" by (by100 blast)
        thus "x \<in> C \<alpha>" unfolding C_def edge_pt_def by (by100 blast)
      next
        fix x assume "x \<in> C \<alpha>"
        then obtain t where "t \<in> I_set" "x = qC (edge_pt (i_of \<alpha>) t)"
          unfolding C_def by (by100 blast)
        hence "x = ?f t" unfolding edge_pt_def by (by100 simp)
        thus "x \<in> ?f ` I_set" using \<open>t \<in> I_set\<close> by (by100 blast)
      qed
      \<comment> \<open>Continuous image of compact is compact.\<close>
      have "top1_compact_on (?f ` I_set) (subspace_topology A ?TA (?f ` I_set))"
        using top1_compact_on_continuous_image[OF hI_compact hA_top hf_cont] by (by100 blast)
      thus "top1_compact_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
        using himg by (by100 simp)
    qed

    \<comment> \<open>Each C(\<alpha>) is closed in A (compact in Hausdorff).\<close>
    have hC_closed: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> closedin_on A ?TA (C \<alpha>)"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have "C \<alpha> \<subseteq> A" using hC_sub[OF h\<alpha>] .
      moreover have "top1_compact_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
        using hC_compact[OF h\<alpha>] .
      ultimately show "closedin_on A ?TA (C \<alpha>)"
        using Theorem_26_3[OF hA_haus] by (by100 blast)
    qed

    \<comment> \<open>A has a topology.\<close>
    have hA_top: "is_topology_on A ?TA"
      using hA_strict unfolding is_topology_on_strict_def by (by100 blast)

    have hC_weak: "\<And>D. D \<subseteq> A \<Longrightarrow>
        (closedin_on A ?TA D \<longleftrightarrow> (\<forall>\<alpha>\<in>?J. closedin_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (C \<alpha> \<inter> D)))"
    proof (intro iffI ballI)
      \<comment> \<open>Forward: D closed in A implies D \<inter> C(\<alpha>) closed in C(\<alpha>).\<close>
      fix D \<alpha> assume hD_sub: "D \<subseteq> A" and hD_cl: "closedin_on A ?TA D" and h\<alpha>: "\<alpha> \<in> ?J"
      show "closedin_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (C \<alpha> \<inter> D)"
        using Theorem_17_2[OF hA_top hC_sub[OF h\<alpha>]]
        using hD_cl by (by100 blast)
    next
      \<comment> \<open>Backward: D \<inter> C(\<alpha>) closed in C(\<alpha>) for all \<alpha> implies D closed in A.\<close>
      fix D assume hD_sub: "D \<subseteq> A"
        and hD_each: "\<forall>\<alpha>\<in>?J. closedin_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (C \<alpha> \<inter> D)"
      \<comment> \<open>Each D \<inter> C(\<alpha>) is closed in A (by Theorem 17.3: C(\<alpha>) closed in A, D \<inter> C(\<alpha>) closed in C(\<alpha>)).\<close>
      have hDC_closed: "\<forall>\<alpha>\<in>?J. closedin_on A ?TA (C \<alpha> \<inter> D)"
      proof (intro ballI)
        fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
        show "closedin_on A ?TA (C \<alpha> \<inter> D)"
          using Theorem_17_3[OF hA_top hC_closed[OF h\<alpha>] hD_each[rule_format, OF h\<alpha>]]
          by (by100 blast)
      qed
      \<comment> \<open>D = \<Union>{D \<inter> C(\<alpha>) | \<alpha> \<in> J} since D \<subseteq> A = \<Union>C(\<alpha>).\<close>
      have hD_eq: "D = (\<Union>\<alpha>\<in>?J. C \<alpha> \<inter> D)"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> D"
        hence "x \<in> A" using hD_sub by (by100 blast)
        hence "x \<in> (\<Union>\<alpha>\<in>?J. C \<alpha>)" using hC_union by (by100 simp)
        then obtain \<alpha> where "\<alpha> \<in> ?J" "x \<in> C \<alpha>" by (by100 blast)
        thus "x \<in> (\<Union>\<alpha>\<in>?J. C \<alpha> \<inter> D)" using \<open>x \<in> D\<close> by (by100 blast)
      next
        fix x assume "x \<in> (\<Union>\<alpha>\<in>?J. C \<alpha> \<inter> D)"
        thus "x \<in> D" by (by100 blast)
      qed
      \<comment> \<open>Finite union of closed sets is closed.\<close>
      let ?F = "(\<lambda>\<alpha>. C \<alpha> \<inter> D) ` ?J"
      have "finite ?F" using hJ_finite by (by100 simp)
      have "\<forall>S\<in>?F. closedin_on A ?TA S"
        using hDC_closed by (by100 blast)
      have "closedin_on A ?TA (\<Union>?F)"
        using closedin_Union_finite[OF hA_top \<open>finite ?F\<close> \<open>\<forall>S\<in>?F. closedin_on A ?TA S\<close>] .
      moreover have "\<Union>?F = (\<Union>\<alpha>\<in>?J. C \<alpha> \<inter> D)" by (by100 blast)
      ultimately have "closedin_on A ?TA (\<Union>\<alpha>\<in>?J. C \<alpha> \<inter> D)" by (by100 simp)
      thus "closedin_on A ?TA D" using hD_eq by (by100 simp)
    qed

    \<comment> \<open>--- (G) Subspace topology on C(\<alpha>) agrees ---\<close>
    have hC_sub_eq: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow>
        subspace_topology A ?TA (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have "C \<alpha> \<subseteq> A" using hC_sub[OF h\<alpha>] by (by100 blast)
      thus "subspace_topology A ?TA (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
        by (rule subspace_topology_trans)
    qed

    \<comment> \<open>--- Assemble the wedge ---\<close>
    \<comment> \<open>--- Assemble the wedge ---\<close>
    have hA_wd_part: "top1_is_wedge_of_circles_on A ?TA ?J a"
      unfolding top1_is_wedge_of_circles_on_def
    proof (intro conjI)
      show "is_topology_on_strict A ?TA" by (rule hA_strict)
      show "is_hausdorff_on A ?TA" by (rule hA_haus)
      show "a \<in> A" by (rule ha_A)
      show "\<exists>Ca. (\<forall>\<alpha>\<in>?J. Ca \<alpha> \<subseteq> A \<and> a \<in> Ca \<alpha> \<and>
            (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (Ca \<alpha>)
                 (subspace_topology A ?TA (Ca \<alpha>)) h)) \<and>
           (\<Union>\<alpha>\<in>?J. Ca \<alpha>) = A \<and>
           (\<forall>\<alpha>\<in>?J. \<forall>\<beta>\<in>?J. \<alpha> \<noteq> \<beta> \<longrightarrow> Ca \<alpha> \<inter> Ca \<beta> = {a}) \<and>
           (\<forall>D\<subseteq>A. closedin_on A ?TA D \<longleftrightarrow>
                   (\<forall>\<alpha>\<in>?J. closedin_on (Ca \<alpha>) (subspace_topology A ?TA (Ca \<alpha>)) (Ca \<alpha> \<inter> D)))"
      proof (rule exI[of _ C], intro conjI)
        show "\<forall>\<alpha>\<in>?J. C \<alpha> \<subseteq> A \<and> a \<in> C \<alpha> \<and>
              (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>)
                   (subspace_topology A ?TA (C \<alpha>)) h)"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
          show "C \<alpha> \<subseteq> A \<and> a \<in> C \<alpha> \<and>
                (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>)
                     (subspace_topology A ?TA (C \<alpha>)) h)"
            using hC_sub[OF h\<alpha>] ha_C[OF h\<alpha>] hC_homeo[OF h\<alpha>] by (by100 blast)
        qed
      next
        show "(\<Union>\<alpha>\<in>?J. C \<alpha>) = A" by (rule hC_union)
      next
        show "\<forall>\<alpha>\<in>?J. \<forall>\<beta>\<in>?J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {a}"
          using hC_disj by (by100 blast)
      next
        show "\<forall>D\<subseteq>A. closedin_on A ?TA D \<longleftrightarrow>
                 (\<forall>\<alpha>\<in>?J. closedin_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (C \<alpha> \<inter> D))"
          using hC_weak by (by100 blast)
      qed
    qed
    \<comment> \<open>--- Gen tracking: apply wrapper inside this scope ---\<close>
    \<comment> \<open>Extract specific homeomorphisms with basepoint from hC\_homeo proof.\<close>
    have hC_homeo_base: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> \<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) f \<and> f (1, 0) = a
        \<and> (\<forall>s\<in>I_set. f (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s))"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      \<comment> \<open>Repeat the hC\_homeo construction with stronger conclusion.
         The homeomorphism g from loop\_factors\_through\_S1 has g(1,0)=a
         and g(R\_to\_S1(s))=qC(edge\_pt(i\_of \<alpha>, s)).\<close>
      from hC_homeo[OF h\<alpha>] obtain g_ex where
        "top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) g_ex"
        by (by100 blast)
      \<comment> \<open>But g\_ex may not have the basepoint/factoring property. We need the specific
         g from loop\_factors\_through\_S1, which was constructed inside hC\_homeo.
         Reprove with the stronger conclusion.\<close>
      have hi\<alpha>: "i_of \<alpha> < ?n" "fst (scheme!(i_of \<alpha>)) = \<alpha>" using hi_of[OF h\<alpha>] by (by100 blast)+
      define f_\<alpha> where "f_\<alpha> t = qC (edge_pt (i_of \<alpha>) t)" for t
      have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f_\<alpha>"
      proof -
        have "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA
            (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                      (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n)))"
          using hqC_edge_cont hi\<alpha>(1) by (by100 blast)
        moreover have "\<And>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                      (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))
                    = f_\<alpha> t"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      have hf0: "f_\<alpha> 0 = a"
      proof -
        have "f_\<alpha> 0 = qC (vxC (i_of \<alpha>), vyC (i_of \<alpha>))"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        also have "\<dots> = qC (vxC 0, vyC 0)"
          using hvert_C hi\<alpha>(1) hn_pos by (by100 blast)
        also have "\<dots> = a" using ha_eq by (by100 simp)
        finally show ?thesis .
      qed
      have hf1: "f_\<alpha> 1 = a"
      proof -
        have hi1: "Suc (i_of \<alpha>) mod ?n < ?n" using hn_pos by (by100 simp)
        have "f_\<alpha> 1 = qC (vxC (Suc (i_of \<alpha>) mod ?n), vyC (Suc (i_of \<alpha>) mod ?n))"
          unfolding f_\<alpha>_def edge_pt_def by (by100 simp)
        also have "\<dots> = qC (vxC 0, vyC 0)"
          using hvert_C hi1 hn_pos by (by100 blast)
        also have "\<dots> = a" using ha_eq by (by100 simp)
        finally show ?thesis .
      qed
      have hf_loop: "top1_is_loop_on A ?TA a f_\<alpha>"
        unfolding top1_is_loop_on_def top1_is_path_on_def
        using hf_cont hf0 hf1 by (by100 blast)
      from loop_factors_through_S1[OF hA_top hf_loop]
      obtain g where hg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology A ?TA g"
        and hg_base: "g (1, 0) = a"
        and hg_factor: "\<forall>s\<in>I_set. f_\<alpha> s = g (top1_R_to_S1 s)"
        by (by100 blast)
      \<comment> \<open>g is a homeomorphism S1 \<rightarrow> C(\<alpha>) (surjection + injection + compactness).\<close>
      \<comment> \<open>g surjects onto C(\<alpha>).\<close>
      have hg_surj: "g ` top1_S1 = C \<alpha>"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> g ` top1_S1"
        then obtain z where "z \<in> top1_S1" "x = g z" by (by100 blast)
        then obtain t where "t \<in> I_set" "top1_R_to_S1 t = z"
        proof -
          obtain xc yc where hq_eq: "z = (xc, yc)" by (cases z)
          have hcirc: "xc^2 + yc^2 = 1"
            using \<open>z \<in> top1_S1\<close> hq_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "xc = cos t0" "yc = sin t0"
            using sincos_total_2pi[OF hcirc] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z"
            unfolding top1_R_to_S1_def t'_def hq_eq
            using \<open>xc = cos t0\<close> \<open>yc = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        hence "x = g (top1_R_to_S1 t)" using \<open>x = g z\<close> by (by100 simp)
        hence "x = f_\<alpha> t" using hg_factor \<open>t \<in> I_set\<close> by (by100 simp)
        hence "x = qC (edge_pt (i_of \<alpha>) t)" unfolding f_\<alpha>_def by (by100 simp)
        thus "x \<in> C \<alpha>" unfolding C_def using \<open>t \<in> I_set\<close> by (by100 blast)
      next
        fix x assume "x \<in> C \<alpha>"
        then obtain t where "t \<in> I_set" "x = qC (edge_pt (i_of \<alpha>) t)"
          unfolding C_def by (by100 blast)
        hence "x = f_\<alpha> t" unfolding f_\<alpha>_def by (by100 simp)
        hence "x = g (top1_R_to_S1 t)" using hg_factor \<open>t \<in> I_set\<close> by (by100 simp)
        moreover have "top1_R_to_S1 t \<in> top1_S1"
          unfolding top1_R_to_S1_def top1_S1_def
          using sin_cos_squared_add[of "2 * pi * t"]
          by (by5000 auto)
        ultimately show "x \<in> g ` top1_S1" by (by100 blast)
      qed
      \<comment> \<open>g is injective on S1.\<close>
      have hg_inj: "inj_on g top1_S1"
      proof (rule inj_onI)
        fix z1 z2 assume hz1: "z1 \<in> top1_S1" and hz2: "z2 \<in> top1_S1" and hgeq: "g z1 = g z2"
        obtain t1 where ht1: "t1 \<in> I_set" "top1_R_to_S1 t1 = z1"
        proof -
          obtain x1 y1 where hz1_eq: "z1 = (x1, y1)" by (cases z1)
          have hcirc1: "x1^2 + y1^2 = 1"
            using hz1 hz1_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "x1 = cos t0" "y1 = sin t0"
            using sincos_total_2pi[OF hcirc1] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z1"
            unfolding top1_R_to_S1_def t'_def hz1_eq
            using \<open>x1 = cos t0\<close> \<open>y1 = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        obtain t2 where ht2: "t2 \<in> I_set" "top1_R_to_S1 t2 = z2"
        proof -
          obtain x2 y2 where hz2_eq: "z2 = (x2, y2)" by (cases z2)
          have hcirc2: "x2^2 + y2^2 = 1"
            using hz2 hz2_eq unfolding top1_S1_def by (by100 simp)
          obtain t0 where "0 \<le> t0" "t0 < 2*pi" "x2 = cos t0" "y2 = sin t0"
            using sincos_total_2pi[OF hcirc2] by (by100 blast)
          define t' where "t' = t0 / (2*pi)"
          have "0 \<le> t'" "t' < 1" unfolding t'_def
            using \<open>0 \<le> t0\<close> \<open>t0 < 2*pi\<close> pi_gt_zero by (by100 auto)+
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          moreover have "top1_R_to_S1 t' = z2"
            unfolding top1_R_to_S1_def t'_def hz2_eq
            using \<open>x2 = cos t0\<close> \<open>y2 = sin t0\<close> pi_gt_zero by (by100 simp)
          ultimately show ?thesis using that by (by100 blast)
        qed
        have "f_\<alpha> t1 = g (top1_R_to_S1 t1)" using hg_factor ht1(1) by (by100 simp)
        also have "\<dots> = g z1" using ht1(2) by (by100 simp)
        also have "\<dots> = g z2" using hgeq by (by100 simp)
        also have "\<dots> = g (top1_R_to_S1 t2)" using ht2(2) by (by100 simp)
        also have "\<dots> = f_\<alpha> t2" using hg_factor ht2(1) by (by100 simp)
        finally have hfeq: "f_\<alpha> t1 = f_\<alpha> t2" .
        hence "qC (edge_pt (i_of \<alpha>) t1) = qC (edge_pt (i_of \<alpha>) t2)"
          unfolding f_\<alpha>_def by (by100 simp)
        hence "(i_of \<alpha> = i_of \<alpha> \<and> t1 = t2)
          \<or> (fst (scheme!(i_of \<alpha>)) = fst (scheme!(i_of \<alpha>)) \<and>
             (if snd (scheme!(i_of \<alpha>)) = snd (scheme!(i_of \<alpha>)) then t2 = t1 else t2 = 1 - t1))"
          using hno_C hi\<alpha>(1) ht1(1) ht2(1) unfolding edge_pt_def by (by100 blast)
        hence "t1 = t2" by (by100 auto)
        thus "z1 = z2" using ht1(2) ht2(2) by (by100 simp)
      qed
      \<comment> \<open>By Theorem 26.6: compact + Hausdorff + continuous bijection = homeomorphism.\<close>
      have hg_bij: "bij_betw g top1_S1 (C \<alpha>)"
        unfolding bij_betw_def using hg_inj hg_surj by (by100 blast)
      have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology"
        using S1_compact by (by100 blast)
      have hC_haus: "is_hausdorff_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
        using Theorem_17_11 hA_haus hC_sub[OF h\<alpha>] by (by100 blast)
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hC_top: "is_topology_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>))"
        using subspace_topology_is_topology_on[OF hA_top hC_sub[OF h\<alpha>]] by (by100 blast)
      \<comment> \<open>Restrict g to codomain C(\<alpha>).\<close>
      have hg_cont_C: "top1_continuous_map_on top1_S1 top1_S1_topology
            (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) g"
      proof -
        have himg: "g ` top1_S1 \<subseteq> C \<alpha>" using hg_surj by (by100 blast)
        from Theorem_18_2[OF hS1_top hA_top hA_top]
        have "\<forall>W f. top1_continuous_map_on top1_S1 top1_S1_topology A ?TA f \<and>
                     W \<subseteq> A \<and> f ` top1_S1 \<subseteq> W
                     \<longrightarrow> top1_continuous_map_on top1_S1 top1_S1_topology W (subspace_topology A ?TA W) f"
          by (by100 blast)
        thus ?thesis using hg_cont hC_sub[OF h\<alpha>] himg by (by100 blast)
      qed
      have hg_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) g"
        using Theorem_26_6[OF hS1_top hC_top hS1_compact hC_haus hg_cont_C hg_bij] by (by100 blast)
      have hg_track: "\<forall>s\<in>I_set. g (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s)"
        using hg_factor unfolding f_\<alpha>_def by (by100 simp)
      show "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) f \<and> f (1, 0) = a
          \<and> (\<forall>s\<in>I_set. f (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s))"
        using hg_homeo hg_base hg_track by (by100 blast)
    qed
    define g_w where "g_w \<alpha> = (SOME f. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology A (subspace_topology X TX A) (C \<alpha>)) f \<and> f (1, 0) = a
        \<and> (\<forall>s\<in>I_set. f (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s)))" for \<alpha>
    have hg_w_props: "\<And>\<alpha>. \<alpha> \<in> ?J \<Longrightarrow> top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (g_w \<alpha>) \<and> g_w \<alpha> (1, 0) = a
        \<and> (\<forall>s\<in>I_set. g_w \<alpha> (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s))"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      from hC_homeo_base[OF h\<alpha>] show "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (g_w \<alpha>) \<and> g_w \<alpha> (1, 0) = a
          \<and> (\<forall>s\<in>I_set. g_w \<alpha> (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s))"
        unfolding g_w_def by (rule someI_ex)
    qed
    have hg_w_homeo: "\<forall>\<alpha>\<in>?J. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (g_w \<alpha>)"
      using hg_w_props by (by100 blast)
    have hg_w_base: "\<forall>\<alpha>\<in>?J. g_w \<alpha> (1, 0) = a"
      using hg_w_props by (by100 blast)
    \<comment> \<open>Apply wrapper: finite\_wedge\_pi1\_free\_with\_chosen\_loops\_arb.\<close>
    have hC_data: "\<forall>\<alpha>\<in>?J. C \<alpha> \<subseteq> A \<and> a \<in> C \<alpha>"
      using hC_sub ha_C by (by100 blast)
    have hC_disj_ball: "\<forall>i\<in>?J. \<forall>j\<in>?J. i \<noteq> j \<longrightarrow> C i \<inter> C j = {a}"
      using hC_disj by (by100 blast)
    have hC_weak_ball: "\<forall>D\<subseteq>A. closedin_on A ?TA D \<longleftrightarrow>
        (\<forall>\<alpha>\<in>?J. closedin_on (C \<alpha>) (subspace_topology A ?TA (C \<alpha>)) (C \<alpha> \<inter> D))"
      using hC_weak by (by100 blast)
    from finite_wedge_pi1_free_with_chosen_loops_arb[OF hA_wd_part hJ_finite
        hg_w_homeo hg_w_base hC_data hC_union hC_disj_ball hC_weak_ball]
    obtain F_w :: "int set" and mulF_w eF_w invgF_w and \<eta>_w :: "nat \<Rightarrow> int" and \<Phi>_w where
      hF_w_free: "top1_is_free_group_full_on F_w mulF_w eF_w invgF_w \<eta>_w ?J" and
      h\<Phi>_w_iso: "top1_group_iso_on F_w mulF_w
          (top1_fundamental_group_carrier A ?TA a)
          (top1_fundamental_group_mul A ?TA a) \<Phi>_w" and
      h\<Phi>_w_gen: "\<forall>\<alpha>\<in>?J. \<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a
          (\<lambda>t. g_w \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
      by (by5000 blast)
    \<comment> \<open>Connect g\_w loop classes to edge\_loop\_class\_a:
       g\_w(\<alpha>)(cos(2\<pi>t), sin(2\<pi>t)) = g\_w(\<alpha>)(R\_to\_S1(t)) = qC(edge\_pt(i\_of \<alpha>, t)).\<close>
    have hgen_eq_a: "\<forall>\<alpha>\<in>?J. \<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a
        (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                  (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))) l}"
    proof (intro ballI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> ?J"
      have hfact: "\<forall>s\<in>I_set. g_w \<alpha> (top1_R_to_S1 s) = qC (edge_pt (i_of \<alpha>) s)"
        using hg_w_props[OF h\<alpha>] by (by100 blast)
      have hloop_eq: "\<forall>t\<in>I_set. g_w \<alpha> (cos (2*pi*t), sin (2*pi*t)) =
          qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
              (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))"
      proof (intro ballI)
        fix t assume "t \<in> I_set"
        have "g_w \<alpha> (cos (2*pi*t), sin (2*pi*t)) = g_w \<alpha> (top1_R_to_S1 t)"
          unfolding top1_R_to_S1_def by (by100 simp)
        also have "\<dots> = qC (edge_pt (i_of \<alpha>) t)" using hfact \<open>t \<in> I_set\<close> by (by100 blast)
        also have "\<dots> = qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
            (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))"
          unfolding edge_pt_def by (by100 simp)
        finally show "g_w \<alpha> (cos (2*pi*t), sin (2*pi*t)) =
            qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))" .
      qed
      \<comment> \<open>\<Phi>\_w(\<eta>\_w(\<alpha>)) = {l. equiv(g\_w(\<alpha>) \<circ> std\_loop, l)} = edge\_loop\_class\_a(\<alpha>).
         Both use loop\_equiv\_on which only depends on behavior on I\_set.\<close>
      have "\<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a
          (\<lambda>t. g_w \<alpha> (cos (2*pi*t), sin (2*pi*t))) l}"
        using h\<Phi>_w_gen[rule_format, OF h\<alpha>] by (by100 blast)
      also have "\<dots> = {l. top1_loop_equiv_on A ?TA a
          (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                    (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))) l}"
      proof -
        let ?f = "\<lambda>t. g_w \<alpha> (cos (2*pi*t), sin (2*pi*t))"
        let ?g = "\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                          (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))"
        \<comment> \<open>?g = f\_\<alpha> (the edge loop), already proved to be a loop.\<close>
        \<comment> \<open>?g is a loop: it's the edge loop for \<alpha>, which we proved earlier as hf\_loop.\<close>
        have hg_loop: "top1_is_loop_on A ?TA a ?g"
        proof -
          have hg_cont: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA ?g"
          proof -
            have "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA
                (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                          (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n)))"
              using hqC_edge_cont hi_of[OF h\<alpha>] by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          have "?g 0 = a"
          proof -
            have "?g 0 = qC (vxC (i_of \<alpha>), vyC (i_of \<alpha>))" unfolding edge_pt_def by (by100 simp)
            also have "\<dots> = qC (vxC 0, vyC 0)"
              using hvert_C hi_of[OF h\<alpha>] hn_pos by (by100 blast)
            also have "\<dots> = a" using ha_eq by (by100 simp)
            finally show ?thesis .
          qed
          have "?g 1 = a"
          proof -
            have hi1: "Suc (i_of \<alpha>) mod ?n < ?n" using hn_pos by (by100 simp)
            have "?g 1 = qC (vxC (Suc (i_of \<alpha>) mod ?n), vyC (Suc (i_of \<alpha>) mod ?n))"
              unfolding edge_pt_def by (by100 simp)
            also have "\<dots> = qC (vxC 0, vyC 0)"
              using hvert_C hi1 hn_pos by (by100 blast)
            also have "\<dots> = a" using ha_eq by (by100 simp)
            finally show ?thesis .
          qed
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hg_cont \<open>?g 0 = a\<close> \<open>?g 1 = a\<close> by (by100 blast)
        qed
        \<comment> \<open>?f is a loop: \<Phi>\_w(\<eta>\_w \<alpha>) is in \<pi>\_1(A,a), so its representative is a loop.\<close>
        have heta_in: "\<eta>_w \<alpha> \<in> F_w"
        proof -
          have "\<forall>s\<in>?J. \<eta>_w s \<in> F_w"
            using hF_w_free unfolding top1_is_free_group_full_on_def by (by100 blast)
          thus ?thesis using h\<alpha> by (by100 blast)
        qed
        have hPhi_in: "\<Phi>_w (\<eta>_w \<alpha>) \<in> top1_fundamental_group_carrier A ?TA a"
          using h\<Phi>_w_iso heta_in unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
        hence "\<exists>f'. top1_is_loop_on A ?TA a f' \<and> \<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a f' l}"
          unfolding top1_fundamental_group_carrier_def by (by100 blast)
        then obtain f' where hf'_loop: "top1_is_loop_on A ?TA a f'"
          and hf'_class: "\<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a f' l}"
          by (by100 blast)
        have hclass_eq: "{l. top1_loop_equiv_on A ?TA a ?f l} = {l. top1_loop_equiv_on A ?TA a f' l}"
          using h\<Phi>_w_gen[rule_format, OF h\<alpha>] hf'_class by (by100 simp)
        \<comment> \<open>f' is loop-equiv to ?f, so ?f is a loop.\<close>
        have hf_loop_here: "top1_is_loop_on A ?TA a ?f"
        proof -
          have "f' \<in> {l. top1_loop_equiv_on A ?TA a ?f l}"
          proof -
            have "f' \<in> {l. top1_loop_equiv_on A ?TA a f' l}"
            proof -
              have "top1_loop_equiv_on A ?TA a f' f'"
                unfolding top1_loop_equiv_on_def
                using hf'_loop Lemma_51_1_path_homotopic_refl[OF hf'_loop[unfolded top1_is_loop_on_def]]
                by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            thus ?thesis using hclass_eq by (by100 blast)
          qed
          hence "top1_loop_equiv_on A ?TA a ?f f'" by (by100 blast)
          thus ?thesis unfolding top1_loop_equiv_on_def by (by100 blast)
        qed
        \<comment> \<open>Apply loop\_equiv\_class\_pointwise\_I.\<close>
        have hclass_result: "{l. top1_loop_equiv_on A ?TA a
            (\<lambda>t. g_w \<alpha> (cos (2*pi*t), sin (2*pi*t))) l} =
            {l. top1_loop_equiv_on A ?TA a
            (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                      (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))) l}"
          using loop_equiv_class_pointwise_I[OF hA_top hf_loop_here hg_loop hloop_eq] by (by100 blast)
        show ?thesis using hclass_result by (by100 blast)
      qed
      finally show "\<Phi>_w (\<eta>_w \<alpha>) = {l. top1_loop_equiv_on A ?TA a
          (\<lambda>t. qC ((1-t) * vxC (i_of \<alpha>) + t * vxC (Suc (i_of \<alpha>) mod ?n),
                    (1-t) * vyC (i_of \<alpha>) + t * vyC (Suc (i_of \<alpha>) mod ?n))) l}" .
    qed
    \<comment> \<open>Transfer: \<pi>\_1(A,a) free on ?J with gen = edge\_loop\_class\_a.\<close>
    have hpi1A_gen_a: "\<exists>\<iota>A. top1_is_free_group_full_on
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_id A ?TA a)
        (top1_fundamental_group_invg A ?TA a)
        \<iota>A ?J \<and> (\<forall>s\<in>?J. \<iota>A s = {l. top1_loop_equiv_on A ?TA a
            (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod ?n),
                      (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod ?n))) l})"
    proof -
      have hpi1A_grp: "top1_is_group_on
          (top1_fundamental_group_carrier A ?TA a)
          (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_id A ?TA a)
          (top1_fundamental_group_invg A ?TA a)"
        using top1_fundamental_group_is_group[OF hA_top ha_A] by (by100 blast)
      note h_fgii = free_group_invariant_under_iso[OF hF_w_free h\<Phi>_w_iso hpi1A_grp]
      define \<iota>A where "\<iota>A \<equiv> SOME \<iota>'. top1_is_free_group_full_on
          (top1_fundamental_group_carrier A ?TA a)
          (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_id A ?TA a)
          (top1_fundamental_group_invg A ?TA a)
          \<iota>' ?J \<and> (\<forall>s\<in>?J. \<iota>' s = \<Phi>_w (\<eta>_w s))"
      have "top1_is_free_group_full_on
          (top1_fundamental_group_carrier A ?TA a)
          (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_id A ?TA a)
          (top1_fundamental_group_invg A ?TA a)
          \<iota>A ?J \<and> (\<forall>s\<in>?J. \<iota>A s = \<Phi>_w (\<eta>_w s))"
        unfolding \<iota>A_def using someI_ex[OF h_fgii] by (by5000 blast)
      hence "\<forall>s\<in>?J. \<iota>A s = {l. top1_loop_equiv_on A ?TA a
            (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod ?n),
                      (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod ?n))) l}"
        using hgen_eq_a by (by100 simp)
      thus ?thesis using \<open>top1_is_free_group_full_on _ _ _ _ \<iota>A ?J \<and> _\<close> by (by100 blast)
    qed
    show ?thesis using hA_wd_part hpi1A_gen_a by (by100 blast)
  qed
  have hA_wd: "top1_is_wedge_of_circles_on A (subspace_topology X TX A) (fst ` set scheme) a"
    using hA_wd_and_gen by (by100 blast)
  have hpi1A_gen_a: "\<exists>\<iota>A. top1_is_free_group_full_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
      (top1_fundamental_group_mul A (subspace_topology X TX A) a)
      (top1_fundamental_group_id A (subspace_topology X TX A) a)
      (top1_fundamental_group_invg A (subspace_topology X TX A) a)
      \<iota>A (fst ` set scheme)
    \<and> (\<forall>s\<in>fst ` set scheme. \<iota>A s =
        {l. top1_loop_equiv_on A (subspace_topology X TX A) a
          (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                    (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme))) l})"
    using hA_wd_and_gen by (by100 blast)
  \<comment> \<open>Step 3: \<pi>_1(A) is free on the labels (Theorem 71.1) at basepoint a.\<close>
  have hA_free: "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F (fst ` set scheme)
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
          (top1_fundamental_group_mul A (subspace_topology X TX A) a)"
    using Theorem_71_3_wedge_of_circles_general hA_wd by (by5000 fastforce)
  \<comment> \<open>Step 4-5: Apply Theorem 72.1 with the SAME A (avoiding alignment issues).\<close>
  have hX_strict: "is_topology_on_strict X TX"
    using hscheme unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hX_haus: "is_hausdorff_on X TX"
    by (rule scheme_quotient_hausdorff[OF hscheme hlen])
  \<comment> \<open>Apply Theorem 72.1 with basepoint a (from CW data). This gives
     \<pi>_1(X, a) \<cong> \<pi>_1(A, a)/N(relator), where the relator is the scheme word.\<close>
  \<comment> \<open>Apply Theorem 72.1 with basepoint a' = h(1,0) \<in> A (avoids needing h(1,0) = a).\<close>
  define a' where "a' = h (1::real, 0::real)"
  have ha'_A: "a' \<in> A"
  proof -
    have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    thus ?thesis unfolding a'_def using hh_S1 by (by100 blast)
  qed
  have ha'_base: "h (1, 0) = a'" unfolding a'_def by (by100 simp)
  \<comment> \<open>Apply Theorem 72.1 with basepoint a'.\<close>
  from Theorem_72_1_attaching_two_cell[OF hX_strict hX_haus hA_cl hA_pc
      hh_cont ha'_A hh_homeo hh_S1 ha'_base]
  obtain \<iota> where h\<iota>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology A
          (subspace_topology X TX A) \<iota>"
      and h\<iota>_eq: "\<forall>z\<in>top1_S1. \<iota> z = h z"
      and h\<iota>_iso: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier X TX a')
          (top1_fundamental_group_mul X TX a')
          (top1_quotient_group_carrier_on
             (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
             (top1_fundamental_group_mul A (subspace_topology X TX A) a')
             (top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
                (top1_fundamental_group_mul A (subspace_topology X TX A) a')
                (top1_fundamental_group_id A (subspace_topology X TX A) a')
                (top1_fundamental_group_invg A (subspace_topology X TX A) a')
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                   A (subspace_topology X TX A) a' \<iota>
                   {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                         (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
          (top1_quotient_group_mul_on
             (top1_fundamental_group_mul A (subspace_topology X TX A) a'))"
    by (by100 blast)
  \<comment> \<open>Now: \<pi>_1(X, a') \<cong> \<pi>_1(A, a')/N(relator).
     The relator is the image of the S1 generator under \<iota>.
     \<pi>_1(A, a') is free on the labels (from hA\_free, transferred via basepoint change).
     The relator corresponds to the scheme word.
     So \<pi>_1(X, a') has presentation G.\<close>
  \<comment> \<open>Step (i): \<pi>\_1(A, a') is free on the labels (basepoint change from a).\<close>
  have hA_free_a': "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F (fst ` set scheme)
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')"
  proof -
    from hA_free obtain F0 :: "int set" and mulF0 eF0 invgF0 and \<iota>F0 :: "nat \<Rightarrow> int" where
      hfree0: "top1_is_free_group_full_on F0 mulF0 eF0 invgF0 \<iota>F0 (fst ` set scheme)" and
      hiso_a: "top1_groups_isomorphic_on F0 mulF0
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
          (top1_fundamental_group_mul A (subspace_topology X TX A) a)"
      by (elim conjE exE) (rule that, assumption+)
    \<comment> \<open>Basepoint change: \<pi>_1(A, a) \<cong> \<pi>_1(A, a') since A path-connected.\<close>
    have hTA: "is_topology_on A (subspace_topology X TX A)"
    proof -
      have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      have "is_topology_on X TX"
        using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF _ \<open>A \<subseteq> X\<close>])
    qed
    have hiso_aa': "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
        (top1_fundamental_group_mul A (subspace_topology X TX A) a)
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')"
      by (rule Theorem_52_1_iso[OF hTA hA_pc ha_A ha'_A])
    have "top1_groups_isomorphic_on F0 mulF0
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')"
      by (rule groups_isomorphic_trans_fwd[OF hiso_a hiso_aa'])
    thus ?thesis using hfree0 by (by100 blast)
  qed
  \<comment> \<open>Step (ii): The relator from Thm 72.1 = the scheme word in the free group.
     The boundary loop h \<circ> (cos 2\<pi>s, sin 2\<pi>s) traces edges 0..n-1,
     each mapping to the generator fst(scheme!i) (or inverse if snd=False).
     So the relator class = scheme word in \<pi>_1(A, a').\<close>
  \<comment> \<open>Step (iii): Combine into group presentation.\<close>
  \<comment> \<open>Step (ii-iii): The quotient \<pi>_1(A,a')/N(relator) is the presented group.
     This needs: relator from Thm 72.1 = scheme word in the free group.\<close>
  have hThm72_a': "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set scheme)
        { map (\<lambda>(s,b). (s, b)) scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX a')
          (top1_fundamental_group_mul X TX a')"
  proof -
    \<comment> \<open>Following Munkres Theorem 74.2 proof:
       "The loop f running around Bd P once in the counterclockwise direction
        generates the fundamental group of Bd P, and the loop \<pi> \<circ> f equals
        the loop (g_{i_1})^{\<epsilon>_1} * ... * (g_{i_n})^{\<epsilon>_n}.
        The theorem now follows from Theorem 72.1."\<close>
    \<comment> \<open>Step A: Extract free group from hA\_free\_a'.\<close>
    from hA_free_a' obtain F :: "int set" and mulF eF invgF and
        \<iota>F :: "nat \<Rightarrow> int" where
      hfree: "top1_is_free_group_full_on F mulF eF invgF \<iota>F (fst ` set scheme)" and
      hiso_AF: "top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')"
      by (elim conjE exE) (rule that, assumption+)
    \<comment> \<open>Step B: From h\<iota>\_iso, \<pi>_1(X,a') \<cong> \<pi>_1(A,a')/N(relator).
       Combined with the free group iso, we get \<pi>_1(X,a') \<cong> F/N(relator in F).
       This gives a group presentation IF we can identify the relator.\<close>
    \<comment> \<open>Step C: The relator = scheme word in the free group.
       The relator in \<pi>_1(A,a') is the class of the loop \<iota> \<circ> circle\_path.
       Since \<iota> = h on S1, this loop = h \<circ> circle\_path.
       The map h sends S1 to A by tracing each edge in order.
       Restricted to edge i, the path equals the generator loop g\_i (or g\_i^{-1}).
       So the relator class = product of generator classes = scheme word.\<close>
    \<comment> \<open>Step D: The quotient F/N(scheme\_word) with the isomorphism gives the presentation.\<close>
    \<comment> \<open>Step B': \<pi>_1(X,a') is a group.\<close>
    have hTX: "is_topology_on X TX"
      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA: "is_topology_on A (subspace_topology X TX A)"
    proof -
      have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTX])
    qed
    have ha'_X: "a' \<in> X"
    proof -
      have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      thus ?thesis using ha'_A by (by100 blast)
    qed
    have hpi1_X_grp: "top1_is_group_on
        (top1_fundamental_group_carrier X TX a')
        (top1_fundamental_group_mul X TX a')
        (top1_fundamental_group_id X TX a')
        (top1_fundamental_group_invg X TX a')"
      using top1_fundamental_group_is_group[OF hTX ha'_X] .
    \<comment> \<open>Step C': Compose: hom \<pi> = (Thm72.1 quotient map) \<circ> (free group iso).
       F --\<phi>--> \<pi>_1(A,a') --proj--> \<pi>_1(A,a')/N(rel) --\<psi>^{-1}--> \<pi>_1(X,a').
       This gives surjective hom \<pi>: F \<rightarrow> \<pi>_1(X,a').\<close>
    \<comment> \<open>Step D': ker(\<pi>) = N(scheme word in F).
       The relator in \<pi>_1(A,a') = class of \<iota> \<circ> circle.
       Under \<phi>^{-1}: maps to scheme word in F.
       So ker = N(scheme word).\<close>
    \<comment> \<open>Step E: Construct the presentation witness.
       From hiso\_AF get iso \<phi>: F \<rightarrow> \<pi>_1(A,a').
       From h\<iota>\_iso get iso \<psi>: \<pi>_1(X,a') \<rightarrow> \<pi>_1(A,a')/N(r).
       Compose: \<pi> = \<psi>^{-1} \<circ> proj \<circ> \<phi>: F \<rightarrow> \<pi>_1(X,a'), surjective.
       ker(\<pi>) = \<phi>^{-1}(N(r)) = N(\<phi>^{-1}(r)).
       Key: \<phi>^{-1}(r) = word\_product mulF eF invgF (map (\<lambda>(s,b). (\<iota>F s, b)) scheme).
       This is the relator identification.\<close>
    \<comment> \<open>For the group presentation, we need:
       1. hpi1\_X\_grp (proved above)
       2. hfree (from hA\_free\_a')
       3. A surjective hom \<pi>: F \<rightarrow> \<pi>_1(X,a')
       4. ker(\<pi>) = N(scheme word in F)
       Items 3-4 require the group theory composition + relator identification.\<close>
    \<comment> \<open>\<phi> will be constructed after hpi1\_A\_grp is available.\<close>
    \<comment> \<open>The relator class in \<pi>_1(A,a').\<close>
    define relator_class where "relator_class =
        top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
           A (subspace_topology X TX A) a' \<iota>
           {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                 (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}"
    \<comment> \<open>The normal subgroup N(relator).\<close>
    define N where "N = top1_normal_subgroup_generated_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')
        (top1_fundamental_group_id A (subspace_topology X TX A) a')
        (top1_fundamental_group_invg A (subspace_topology X TX A) a')
        {relator_class}"
    \<comment> \<open>The quotient group.\<close>
    define Q where "Q = top1_quotient_group_carrier_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') N"
    define mulQ where "mulQ = top1_quotient_group_mul_on
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')"
    \<comment> \<open>Extract \<psi>: \<pi>_1(X,a') \<rightarrow> Q (iso from Thm 72.1).\<close>
    have h\<iota>_iso': "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX a')
        (top1_fundamental_group_mul X TX a') Q mulQ"
      using h\<iota>_iso unfolding Q_def N_def relator_class_def mulQ_def by (by100 simp)
    from h\<iota>_iso'[unfolded top1_groups_isomorphic_on_def top1_group_iso_on_def]
    obtain \<psi> where
      h\<psi>_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier X TX a')
          (top1_fundamental_group_mul X TX a') Q mulQ \<psi>" and
      h\<psi>_bij: "bij_betw \<psi>
          (top1_fundamental_group_carrier X TX a') Q"
      by (by100 blast)
    \<comment> \<open>Natural quotient map proj: \<pi>_1(A,a') \<rightarrow> Q.\<close>
    define proj where "proj g = top1_group_coset_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') N g" for g
    \<comment> \<open>Projection properties.\<close>
    have hpi1_A_grp: "top1_is_group_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')
        (top1_fundamental_group_id A (subspace_topology X TX A) a')
        (top1_fundamental_group_invg A (subspace_topology X TX A) a')"
      using top1_fundamental_group_is_group[OF hTA ha'_A] .
    \<comment> \<open>Construct \<phi>: F \<rightarrow> \<pi>_1(A,a') mapping \<iota>F(s) \<rightarrow> [edge\_loop for label s].
       Munkres: "choose an edge oriented counterclockwise, let g_i = \<pi> \<circ> f_i.
       Then g_1,...,g_k represent free generators for \<pi>_1(A,x_0)."\<close>
    \<comment> \<open>i\_of and hi\_of now at \<S>74.2 outer scope (line ~8955). No re-definition needed.\<close>
    define edge_loop_class where "edge_loop_class s =
        {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
          (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                    (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme))) g}"
      for s :: nat
    have hedge_class_in: "\<forall>s\<in>fst ` set scheme.
        edge_loop_class s \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
    proof (intro ballI)
      fix s assume hs: "s \<in> fst ` set scheme"
      let ?i = "i_of s"
      have hi: "?i < length scheme" "fst (scheme!?i) = s" "snd (scheme!?i) = True"
        using hi_of[OF hs] by (by100 blast)+
      define el where "el t = qC ((1-t) * vxC ?i + t * vxC (Suc ?i mod length scheme),
          (1-t) * vyC ?i + t * vyC (Suc ?i mod length scheme))" for t
      have hel_loop: "top1_is_loop_on A (subspace_topology X TX A) a' el"
      proof -
        have hel0: "el 0 = a'"
        proof -
          have "el 0 = qC (vxC ?i, vyC ?i)" unfolding el_def by (by100 simp)
          also have "\<dots> = qC (vxC 0, vyC 0)"
          proof -
            have "0 < length scheme" using hlen by (by100 linarith)
            thus ?thesis using hvert_C[rule_format, OF hi(1) \<open>0 < length scheme\<close>] by (by100 simp)
          qed
          also have "\<dots> = a" using ha_eq by (by100 simp)
          finally show ?thesis
          proof -
            assume ha_val: "el 0 = a"
            have "h (1, 0) = qC (vxC 0, vyC 0)"
            proof -
              have "0 < length scheme" using hlen by (by100 linarith)
              moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
              ultimately have "h (cos (2*pi*(real 0+0)/real (length scheme)),
                  sin (2*pi*(real 0+0)/real (length scheme)))
                = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod length scheme),
                       (1-0)*vyC 0 + 0*vyC (Suc 0 mod length scheme))"
                using hh_edge_arc by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            thus ?thesis unfolding a'_def using ha_val ha_eq by (by100 simp)
          qed
        qed
        have hel1: "el 1 = a'"
        proof -
          have hn_pos: "length scheme > 0" using hlen by (by100 linarith)
          have hj: "Suc ?i mod length scheme < length scheme"
            using mod_less_divisor[OF hn_pos] by (by100 simp)
          have "el 1 = qC (vxC (Suc ?i mod length scheme), vyC (Suc ?i mod length scheme))"
            unfolding el_def by (by100 simp)
          also have "\<dots> = qC (vxC 0, vyC 0)"
            using hvert_C[rule_format, OF hj] hlen by (by100 force)
          also have "\<dots> = a" using ha_eq by (by100 simp)
          finally show ?thesis
          proof -
            assume ha_val: "el 1 = a"
            have "h (1, 0) = qC (vxC 0, vyC 0)"
            proof -
              have "0 < length scheme" using hlen by (by100 linarith)
              moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
              ultimately have "h (cos (2*pi*(real 0+0)/real (length scheme)),
                  sin (2*pi*(real 0+0)/real (length scheme)))
                = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod length scheme),
                       (1-0)*vyC 0 + 0*vyC (Suc 0 mod length scheme))"
                using hh_edge_arc by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            thus ?thesis unfolding a'_def using ha_val ha_eq by (by100 simp)
          qed
        qed
        have hel_cont: "top1_continuous_map_on I_set top1_unit_interval_topology
            A (subspace_topology X TX A) el"
        proof -
          have "top1_continuous_map_on I_set top1_unit_interval_topology
              A (subspace_topology X TX A) (\<lambda>t. qC ((1-t) * vxC ?i + t * vxC (Suc ?i mod length scheme),
                  (1-t) * vyC ?i + t * vyC (Suc ?i mod length scheme)))"
            using hqC_edge_cont hi(1) by (by100 blast)
          moreover have "\<And>t. qC ((1-t) * vxC ?i + t * vxC (Suc ?i mod length scheme),
              (1-t) * vyC ?i + t * vyC (Suc ?i mod length scheme)) = el t"
            unfolding el_def by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
          using hel0 hel1 hel_cont by (by5000 blast)
      qed
      have "edge_loop_class s = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' el g}"
        unfolding edge_loop_class_def el_def by (by100 simp)
      thus "edge_loop_class s \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
        unfolding top1_fundamental_group_carrier_def using hel_loop by (by100 blast)
    qed
    from free_group_hom_exists[OF hfree hpi1_A_grp hedge_class_in]
    obtain \<phi> where
      h\<phi>_hom: "top1_group_hom_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a') \<phi>" and
      h\<phi>_gen: "\<forall>s\<in>fst ` set scheme. \<phi> (\<iota>F s) = edge_loop_class s"
      by (by100 blast)
    \<comment> \<open>a = a' (both equal qC(vxC 0, vyC 0) = h(1,0)).\<close>
    have ha_eq_a': "a = a'"
    proof -
      have "h (1, 0) = qC (vxC 0, vyC 0)"
      proof -
        have "0 < length scheme" using hlen by (by100 linarith)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
        ultimately have "h (cos (2*pi*(real 0+0)/real (length scheme)),
            sin (2*pi*(real 0+0)/real (length scheme)))
          = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod length scheme),
                 (1-0)*vyC 0 + 0*vyC (Suc 0 mod length scheme))"
          using hh_edge_arc by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      thus ?thesis unfolding a'_def using ha_eq by (by100 simp)
    qed
    have hJ_fin: "finite (fst ` set scheme)" by (by100 simp)
    \<comment> \<open>Transfer wedge from basepoint a to a' (they are equal).\<close>
    have hA_wd_a': "top1_is_wedge_of_circles_on A (subspace_topology X TX A) (fst ` set scheme) a'"
      using hA_wd ha_eq_a' by (by100 simp)
    \<comment> \<open>Bijectivity of \<phi>: from finite\_wedge\_pi1\_free\_with\_chosen\_loops (Munkres 71.1
       witnessed version). Extract circle data from hA\_wd\_a', apply the theorem
       to get \<Phi> with iso + gen correspondence, then \<phi> = \<Phi> by free group uniqueness.\<close>
    \<comment> \<open>--- Bijectivity of \<phi> via wrapper + free\_group\_hom\_generators\_iso ---\<close>
    \<comment> \<open>Key: \<pi>\_1(A, a') is free on J with gen = edge\_loop\_class.
       Apply free\_group\_hom\_generators\_iso to get \<phi> bijective.\<close>
    \<comment> \<open>Step 1: Get \<pi>\_1(A, a') free on J with gen = edge\_loop\_class from wrapper.\<close>
    \<comment> \<open>\<pi>\_1(A, a') is free on J with gen = edge\_loop\_class.
       Proof: extract from hA\_free\_a' + abstract freeness + gen correlation
       (or from wrapper once circle data is hoisted). For now: sorry the gen corr.\<close>
    have hpi1A_free_gen: "\<exists>\<iota>A. top1_is_free_group_full_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')
        (top1_fundamental_group_id A (subspace_topology X TX A) a')
        (top1_fundamental_group_invg A (subspace_topology X TX A) a')
        \<iota>A (fst ` set scheme)
      \<and> (\<forall>s\<in>fst ` set scheme. \<iota>A s = edge_loop_class s)"
    proof -
      from hpi1A_gen_a
      obtain \<iota>A where h1: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
          (top1_fundamental_group_mul A (subspace_topology X TX A) a)
          (top1_fundamental_group_id A (subspace_topology X TX A) a)
          (top1_fundamental_group_invg A (subspace_topology X TX A) a)
          \<iota>A (fst ` set scheme)" and
        h2: "\<forall>s\<in>fst ` set scheme. \<iota>A s =
            {l. top1_loop_equiv_on A (subspace_topology X TX A) a
              (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                        (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme))) l}"
        by (by100 blast)
      have h1': "top1_is_free_group_full_on
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          \<iota>A (fst ` set scheme)"
        using h1 ha_eq_a' by (by100 simp)
      have h2': "\<forall>s\<in>fst ` set scheme. \<iota>A s = edge_loop_class s"
      proof
        fix s assume "s \<in> fst ` set scheme"
        have "\<iota>A s = {l. top1_loop_equiv_on A (subspace_topology X TX A) a
              (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                        (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme))) l}"
          using h2 \<open>s \<in> fst ` set scheme\<close> by (by100 blast)
        also have "\<dots> = edge_loop_class s"
        proof -
          have haa: "a = a'" by (rule ha_eq_a')
          show ?thesis
            apply (simp only: haa)
            apply (simp only: edge_loop_class_def)
            done
        qed
        finally show "\<iota>A s = edge_loop_class s" .
      qed
      show ?thesis using h1' h2' by (by100 blast)
    qed
    \<comment> \<open>PROVED from hpi1A\_gen\_a + a=a'. Old comment below for reference.\<close>
    \<comment> \<open>Apply finite\_wedge\_pi1\_free\_with\_chosen\_loops\_arb to A.
         Requires: extract circle homeomorphisms from wedge data (hA\_wd\_a'),
         verify basepoint = a', apply wrapper, connect loop classes to edge\_loop\_class.
         The proof requires hoisting the circle data (C, g, hC\_weak) from inside
         the wedge construction proof (lines 9205-9696) to this scope.
         Approximately 100 lines of technical reindexing.\<close>
    from hpi1A_free_gen obtain \<iota>A where
      hpi1A_free: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')
        (top1_fundamental_group_id A (subspace_topology X TX A) a')
        (top1_fundamental_group_invg A (subspace_topology X TX A) a')
        \<iota>A (fst ` set scheme)"
      and hpi1A_gen: "\<forall>s\<in>fst ` set scheme. \<iota>A s = edge_loop_class s"
      by (by100 blast)
    \<comment> \<open>Step 2: \<phi> maps \<iota>F(s) to edge\_loop\_class(s) = \<iota>A(s).\<close>
    have h\<phi>_gen_eq: "\<forall>s\<in>fst ` set scheme. \<phi> (\<iota>F s) = \<iota>A s"
      using h\<phi>_gen hpi1A_gen by (by100 simp)
    \<comment> \<open>Step 3: free\_group\_hom\_generators\_iso: \<phi> bijective.\<close>
    have h\<phi>_bij: "bij_betw \<phi> F
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')"
      using free_group_hom_generators_iso[OF hfree hpi1A_free h\<phi>_hom h\<phi>_gen_eq] by (by100 blast)
    have hrel_in: "relator_class \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
    proof -
      \<comment> \<open>The circle loop class is in \<pi>_1(S1,(1,0)).\<close>
      define circle_class where "circle_class =
          {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}"
      have hcc_in: "circle_class \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        unfolding top1_fundamental_group_carrier_def circle_class_def
        using standard_S1_loop_is_loop by (by100 blast)
      \<comment> \<open>\<iota>_* maps \<pi>_1(S1,(1,0)) to \<pi>_1(A,a') since \<iota> is continuous and \<iota>(1,0) = a'.\<close>
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have h10_S1: "(1::real, 0::real) \<in> top1_S1"
        unfolding top1_S1_def by (by100 simp)
      have h\<iota>_10: "\<iota> (1, 0) = a'"
        using h\<iota>_eq[rule_format, OF h10_S1] unfolding a'_def by (by100 simp)
      have h\<iota>_S1_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
             A (subspace_topology X TX A) a' \<iota>)"
        using top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA h10_S1 ha'_A h\<iota>_cont h\<iota>_10] .
      \<comment> \<open>relator\_class = \<iota>_*(circle\_class), which is in \<pi>_1(A,a') since \<iota>_* is a hom.\<close>
      have "relator_class = top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
             A (subspace_topology X TX A) a' \<iota> circle_class"
        unfolding relator_class_def circle_class_def by (by100 simp)
      moreover have "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
             A (subspace_topology X TX A) a' \<iota> circle_class
        \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
        using h\<iota>_S1_hom hcc_in unfolding top1_group_hom_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hN_normal: "top1_normal_subgroup_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a')
        (top1_fundamental_group_id A (subspace_topology X TX A) a')
        (top1_fundamental_group_invg A (subspace_topology X TX A) a') N"
      unfolding N_def
      using normal_subgroup_generated_is_normal[OF hpi1_A_grp, of "{relator_class}"] hrel_in
      by (by100 blast)
    note hqpp = quotient_projection_properties[OF hpi1_A_grp hN_normal]
    have hproj_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') Q mulQ proj"
      using hqpp unfolding proj_def Q_def mulQ_def by (by5000 blast)
    have hproj_surj: "proj ` (top1_fundamental_group_carrier A (subspace_topology X TX A) a') = Q"
      using hqpp unfolding proj_def Q_def by (by5000 blast)
    have hproj_ker: "top1_group_kernel_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_group_coset_on
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
          (top1_fundamental_group_id A (subspace_topology X TX A) a')) proj = N"
      using hqpp unfolding proj_def by (by5000 blast)
    \<comment> \<open>Compose: \<pi> = inv(\<psi>) \<circ> proj \<circ> \<phi>.\<close>
    define \<pi>F where "\<pi>F f = inv_into (top1_fundamental_group_carrier X TX a') \<psi> (proj (\<phi> f))" for f
    \<comment> \<open>Show \<pi>F is a surjective hom with ker = N(scheme word).\<close>
    \<comment> \<open>proj \<circ> \<phi> is a surjective hom F \<rightarrow> Q.\<close>
    have hproj_phi_hom: "top1_group_hom_on F mulF Q mulQ (proj \<circ> \<phi>)"
      using group_hom_comp[OF h\<phi>_hom hproj_hom] .
    have hproj_phi_surj: "(proj \<circ> \<phi>) ` F = Q"
    proof -
      have "\<phi> ` F = top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
        using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
      hence "(proj \<circ> \<phi>) ` F = proj ` (top1_fundamental_group_carrier A (subspace_topology X TX A) a')"
        using image_image[of proj \<phi> F, symmetric] by (by100 simp)
      thus ?thesis using hproj_surj by (by100 simp)
    qed
    \<comment> \<open>ker(proj \<circ> \<phi>) = \<phi>^{-1}(N).\<close>
    have hker_proj_phi: "top1_group_kernel_on F
        (top1_group_coset_on
          (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
          (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
          (top1_fundamental_group_id A (subspace_topology X TX A) a'))
        (proj \<circ> \<phi>) = {f \<in> F. \<phi> f \<in> N}"
    proof -
      \<comment> \<open>ker(proj \<circ> \<phi>) = {f \<in> F. (proj \<circ> \<phi>) f = e\_Q} = {f \<in> F. proj(\<phi> f) = coset(N, e\_A)}.
         proj(g) = coset(N, e\_A) iff g \<in> N (from hproj\_ker).\<close>
      have "top1_group_kernel_on F
          (top1_group_coset_on
            (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
            (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
            (top1_fundamental_group_id A (subspace_topology X TX A) a'))
          (proj \<circ> \<phi>) = {f \<in> F. proj (\<phi> f) =
            top1_group_coset_on
              (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
              (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
              (top1_fundamental_group_id A (subspace_topology X TX A) a')}"
        unfolding top1_group_kernel_on_def by (by100 simp)
      also have "\<dots> = {f \<in> F. \<phi> f \<in> N}"
      proof -
        have h\<phi>_image: "\<And>f. f \<in> F \<Longrightarrow> \<phi> f \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a'"
          using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
        have hcoset_iff: "\<And>g. g \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a' \<Longrightarrow>
            (proj g = top1_group_coset_on
              (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
              (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
              (top1_fundamental_group_id A (subspace_topology X TX A) a')) = (g \<in> N)"
          using hproj_ker unfolding top1_group_kernel_on_def by (by100 blast)
        show ?thesis using hcoset_iff h\<phi>_image unfolding proj_def by (by5000 force)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>By first isomorphism theorem: Q \<cong> F / ker(proj \<circ> \<phi>).
       Since Q \<cong> \<pi>_1(X,a'): \<pi>_1(X,a') \<cong> F / ker.
       If ker = N(scheme word): this gives the presentation.\<close>
    \<comment> \<open>Simplification: the goal asks for \<exists>G. presented\_by G ... \<and> G \<cong> \<pi>_1(X,a').
       Use G = Q (the quotient group), which is presented by (S, {scheme word})
       and is iso to \<pi>_1(X,a') by h\<iota>\_iso.\<close>
    \<comment> \<open>Key: the relator class under \<phi>^{-1} equals the scheme word product.
       relator\_class = image of circle loop under \<iota>.
       Under \<phi>^{-1}: this maps to word\_product(\<iota>F, scheme) in F.
       This is the core topological identification.\<close>
    \<comment> \<open>Core topology: boundary loop = scheme word in free group.
       Munkres: "the loop f running around Bd P once counterclockwise
       generates \<pi>_1(Bd P), and the loop \<pi> \<circ> f equals g_{i_1}^{\<epsilon>_1} * ... * g_{i_n}^{\<epsilon>_n}."

       Proof plan:
       1. relator\_class = class of \<iota> \<circ> circle in \<pi>_1(A,a').
       2. \<iota> \<circ> circle decomposes as product of n sub-loops, one per edge.
       3. Each sub-loop is homotopic to the edge loop g\_i (or g\_i^{-1}).
       4. Under \<phi>^{-1}: the class maps to the corresponding word in F.
       5. Word = word\_product of scheme.\<close>
    \<comment> \<open>Core relator identification: relator\_class = \<phi>(scheme\_word\_in\_F).
       Proof: The boundary loop \<iota> \<circ> circle decomposes as a product of edge loops.
       Each edge loop class = \<phi>(\<iota>F(label\_i))^{sign\_i} in \<pi>_1(A,a').
       So relator\_class = \<phi>(\<iota>F(s_0))^{b_0} * ... * \<phi>(\<iota>F(s_{n-1}))^{b_{n-1}}
       = \<phi>(word\_product of scheme) since \<phi> is a hom.
       Hence \<phi>^{-1}(relator\_class) = word\_product of scheme.\<close>
    \<comment> \<open>Helper: two loops agreeing on I\_set have the same equivalence class.\<close>
    have hloop_class_eq_pointwise:
      "\<And>f1 f2. (\<forall>t\<in>I_set. f1 t = f2 t) \<Longrightarrow>
        {g. top1_loop_equiv_on A (subspace_topology X TX A) a' f1 g}
      = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' f2 g}"
    proof -
      fix f1 f2 :: "real \<Rightarrow> 'a"
      assume hpw: "\<forall>t\<in>I_set. f1 t = f2 t"
      let ?TA = "subspace_topology X TX A"
      \<comment> \<open>Key: all conditions in loop\_equiv\_on use functions only at I\_set points.\<close>
      have hloop_iff: "\<And>f. top1_is_loop_on A ?TA a' f1 = top1_is_loop_on A ?TA a' f2"
      proof -
        have h01: "(0::real) \<in> I_set" "(1::real) \<in> I_set"
          unfolding top1_unit_interval_def by (by100 auto)+
        have hf0: "f1 0 = f2 0" using hpw h01 by (by100 blast)
        have hf1: "f1 1 = f2 1" using hpw h01 by (by100 blast)
        have hcont: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f1
            = top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f2"
        proof -
          have hfpw: "\<And>x. x \<in> I_set \<Longrightarrow> f1 x = f2 x" using hpw by (by100 blast)
          show ?thesis
          proof (rule iffI)
            assume h1: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f1"
            show "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f2"
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix x assume "x \<in> I_set"
              have "f1 x \<in> A" using h1 \<open>x \<in> I_set\<close> unfolding top1_continuous_map_on_def by (by100 blast)
              thus "f2 x \<in> A" using hfpw[OF \<open>x \<in> I_set\<close>] by (by100 simp)
            next
              fix V assume "V \<in> ?TA"
              have "{x \<in> I_set. f2 x \<in> V} = {x \<in> I_set. f1 x \<in> V}"
              proof -
                { fix x
                  have "(x \<in> I_set \<and> f2 x \<in> V) = (x \<in> I_set \<and> f1 x \<in> V)"
                    using hfpw[of x] by (cases "x \<in> I_set") (by100 simp)+
                }
                thus ?thesis by (by100 blast)
              qed
              thus "{x \<in> I_set. f2 x \<in> V} \<in> top1_unit_interval_topology"
                using h1 \<open>V \<in> ?TA\<close> unfolding top1_continuous_map_on_def by (by100 simp)
            qed
          next
            assume h2: "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f2"
            show "top1_continuous_map_on I_set top1_unit_interval_topology A ?TA f1"
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix x assume "x \<in> I_set"
              have "f2 x \<in> A" using h2 \<open>x \<in> I_set\<close> unfolding top1_continuous_map_on_def by (by100 blast)
              thus "f1 x \<in> A" using hfpw[OF \<open>x \<in> I_set\<close>] by (by100 simp)
            next
              fix V assume "V \<in> ?TA"
              have "{x \<in> I_set. f1 x \<in> V} = {x \<in> I_set. f2 x \<in> V}"
                using hfpw by (by5000 force)
              thus "{x \<in> I_set. f1 x \<in> V} \<in> top1_unit_interval_topology"
                using h2 \<open>V \<in> ?TA\<close> unfolding top1_continuous_map_on_def by (by100 simp)
            qed
          qed
        qed
        show "\<And>f. top1_is_loop_on A ?TA a' f1 = top1_is_loop_on A ?TA a' f2"
          unfolding top1_is_loop_on_def top1_is_path_on_def
          using hf0 hf1 hcont by (by5000 metis)
      qed
      have hph_iff: "\<And>g. top1_path_homotopic_on A ?TA a' a' f1 g
          = top1_path_homotopic_on A ?TA a' a' f2 g"
      proof -
        fix g :: "real \<Rightarrow> 'a"
        have hF_eq: "\<And>F s. s \<in> I_set \<Longrightarrow> (F (s, 0) = f1 s) = (F (s, 0) = f2 s)"
          using hpw by (by100 auto)
        show "top1_path_homotopic_on A ?TA a' a' f1 g
            = top1_path_homotopic_on A ?TA a' a' f2 g"
        proof (rule iffI)
          assume h1: "top1_path_homotopic_on A ?TA a' a' f1 g"
          from h1 obtain F where
            hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology A ?TA F"
            and hF0: "\<forall>s\<in>I_set. F (s, 0) = f1 s"
            and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
            and hFl: "\<forall>t\<in>I_set. F (0, t) = a'" and hFr: "\<forall>t\<in>I_set. F (1, t) = a'"
            unfolding top1_path_homotopic_on_def by (by100 blast)
          have hF0': "\<forall>s\<in>I_set. F (s, 0) = f2 s"
          proof (intro ballI)
            fix s assume "s \<in> I_set"
            from hF0 have "F (s, 0) = f1 s" using \<open>s \<in> I_set\<close> by (by100 blast)
            also from hF_eq have "f1 s = f2 s" using \<open>s \<in> I_set\<close> hpw by (by100 blast)
            finally show "F (s, 0) = f2 s" .
          qed
          have "top1_is_path_on A ?TA a' a' f2" using h1 hloop_iff
            unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
          moreover have "top1_is_path_on A ?TA a' a' g" using h1
            unfolding top1_path_homotopic_on_def by (by100 blast)
          ultimately show "top1_path_homotopic_on A ?TA a' a' f2 g"
            unfolding top1_path_homotopic_on_def
            using hF hF0' hF1 hFl hFr by (by100 blast)
        next
          assume h2: "top1_path_homotopic_on A ?TA a' a' f2 g"
          from h2 obtain F where
            hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology A ?TA F"
            and hF0: "\<forall>s\<in>I_set. F (s, 0) = f2 s"
            and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
            and hFl: "\<forall>t\<in>I_set. F (0, t) = a'" and hFr: "\<forall>t\<in>I_set. F (1, t) = a'"
            unfolding top1_path_homotopic_on_def by (by100 blast)
          have hF0': "\<forall>s\<in>I_set. F (s, 0) = f1 s"
          proof (intro ballI)
            fix s assume "s \<in> I_set"
            from hF0 have "F (s, 0) = f2 s" using \<open>s \<in> I_set\<close> by (by100 blast)
            also have "f2 s = f1 s" using hpw \<open>s \<in> I_set\<close> by (by100 auto)
            finally show "F (s, 0) = f1 s" .
          qed
          have "top1_is_path_on A ?TA a' a' f1" using h2 hloop_iff
            unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
          moreover have "top1_is_path_on A ?TA a' a' g" using h2
            unfolding top1_path_homotopic_on_def by (by100 blast)
          ultimately show "top1_path_homotopic_on A ?TA a' a' f1 g"
            unfolding top1_path_homotopic_on_def
            using hF hF0' hF1 hFl hFr by (by100 blast)
        qed
      qed
      show "{g. top1_loop_equiv_on A ?TA a' f1 g} = {g. top1_loop_equiv_on A ?TA a' f2 g}"
        unfolding top1_loop_equiv_on_def using hloop_iff hph_iff by (by100 blast)
    qed
    \<comment> \<open>Step R1: relator\_class = product of edge loop classes in \<pi>_1(A,a').\<close>
    have hrel_product: "relator_class =
        top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(s, b). (\<phi> (\<iota>F s), b)) scheme)"
    proof -
      let ?n = "length scheme"
      \<comment> \<open>Step 1: \<phi>(\<iota>F(s)) = edge\_loop\_class(s) for each label s (from h\<phi>\_gen).\<close>
      \<comment> \<open>Step 2: For each edge k with scheme!k = (s, b):
         [edge\_k sub-loop] = edge\_loop\_class(s)^b.
         True direction: sub-loop = edge\_loop(i\_of s) (from hedge\_C, same direction).
         False direction: sub-loop = reverse of edge\_loop(i\_of s) (from hedge\_C, opposite direction).\<close>
      \<comment> \<open>Step 3: [boundary loop] = product of [edge\_k sub-loops]
         = product of edge\_loop\_class(s\_k)^{b\_k}
         = product of \<phi>(\<iota>F(s\_k))^{b\_k}
         = word\_product(\<phi>(\<iota>F), scheme).\<close>
      \<comment> \<open>Step 4: relator\_class = [boundary loop] (by definition).\<close>
      \<comment> \<open>Key intermediate: for each edge k, the sub-loop class = \<phi>(\<iota>F(s))^b
         where (s,b) = scheme!k. Uses hedge\_C + edge\_loop\_class + h\<phi>\_gen.\<close>
      have hsub_class: "\<forall>k<?n. let (s, b) = scheme!k in
          {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
            (\<lambda>t. qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
                      (1-t) * vyC k + t * vyC (Suc k mod ?n))) g}
        = (if b then \<phi> (\<iota>F s) else
            top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F s)))"
      proof (intro allI impI)
        fix k assume hk: "k < ?n"
        obtain s b where hsb: "scheme ! k = (s, b)" by (cases "scheme!k") (by100 blast)
        hence hs: "fst (scheme!k) = s" and hb: "snd (scheme!k) = b" by (by100 simp)+
        have hs_label: "s \<in> fst ` set scheme" using hk hs by (by100 force)
        have hi_s: "i_of s < ?n" "fst (scheme!(i_of s)) = s" "snd (scheme!(i_of s)) = True"
          using hi_of[OF hs_label] by (by100 blast)+
        \<comment> \<open>Define edge loop for edge k and canonical edge.\<close>
        define el_k where "el_k t = qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
            (1-t) * vyC k + t * vyC (Suc k mod ?n))" for t
        define el_s where "el_s t = qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod ?n),
            (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod ?n))" for t
        \<comment> \<open>From hedge\_C: same label s, so edge k and i\_of(s) are identified.\<close>
        have hsamelabel: "fst (scheme!k) = fst (scheme!(i_of s))"
          using hs hi_s(2) by (by100 simp)
        \<comment> \<open>Case on direction b.\<close>
        \<comment> \<open>Apply hedge\_C to edges k and i\_of(s).\<close>
        have hedge_k: "\<forall>t\<in>I_set. el_k t =
            (if b then el_s t
             else qC (t * vxC (i_of s) + (1-t) * vxC (Suc (i_of s) mod ?n),
                       t * vyC (i_of s) + (1-t) * vyC (Suc (i_of s) mod ?n)))"
        proof (intro ballI)
          fix t assume ht: "t \<in> I_set"
          have hC: "qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
                        (1-t) * vyC k + t * vyC (Suc k mod ?n))
              = (if snd (scheme!k) = snd (scheme!(i_of s))
                 then qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod ?n),
                           (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod ?n))
                 else qC (t * vxC (i_of s) + (1-t) * vxC (Suc (i_of s) mod ?n),
                           t * vyC (i_of s) + (1-t) * vyC (Suc (i_of s) mod ?n)))"
            using hedge_C[rule_format, OF hk hi_s(1) hsamelabel ht] .
          \<comment> \<open>snd(scheme!(i\_of s)) = True, so snd(scheme!k) = snd(scheme!(i\_of s)) \<longleftrightarrow> b = True.\<close>
          have hdir: "(snd (scheme!k) = snd (scheme!(i_of s))) = b"
            using hb hi_s(3) by (by100 simp)
          show "el_k t = (if b then el_s t
               else qC (t * vxC (i_of s) + (1-t) * vxC (Suc (i_of s) mod ?n),
                         t * vyC (i_of s) + (1-t) * vyC (Suc (i_of s) mod ?n)))"
            using hC hdir unfolding el_k_def el_s_def by (by100 simp)
        qed
        \<comment> \<open>The class of el\_k equals edge\_loop\_class(s) (True) or invg (False).\<close>
        \<comment> \<open>\<phi>(\<iota>F s) = edge\_loop\_class(s) = {g. loop\_equiv el\_s g}.\<close>
        have hphi_s: "\<phi> (\<iota>F s) = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_s g}"
          using h\<phi>_gen[rule_format, OF hs_label] unfolding edge_loop_class_def el_s_def by (by100 simp)
        \<comment> \<open>Show the class of el\_k equals \<phi>(\<iota>F s) (if True) or invg(\<phi>(\<iota>F s)) (if False).\<close>
        have hclass_eq: "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_k g}
          = (if b then \<phi> (\<iota>F s)
             else top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F s)))"
        proof (cases b)
          case True
          have "\<forall>t\<in>I_set. el_k t = el_s t" using hedge_k True by (by100 simp)
          hence "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_k g}
              = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_s g}"
            using hloop_class_eq_pointwise by (by100 blast)
          thus ?thesis using True hphi_s by (by100 simp)
        next
          case False
          \<comment> \<open>hedge\_k with False: el\_k(t) = el\_s(1-t) = reverse(el\_s)(t) on I\_set.\<close>
          have "\<forall>t\<in>I_set. el_k t = top1_path_reverse el_s t"
          proof (intro ballI)
            fix t assume ht: "t \<in> I_set"
            have "el_k t = qC (t * vxC (i_of s) + (1-t) * vxC (Suc (i_of s) mod length scheme),
                               t * vyC (i_of s) + (1-t) * vyC (Suc (i_of s) mod length scheme))"
              using hedge_k[rule_format, OF ht] False by (by100 simp)
            also have "\<dots> = el_s (1 - t)" unfolding el_s_def by (simp add: algebra_simps)
            also have "\<dots> = top1_path_reverse el_s t"
              unfolding top1_path_reverse_def by (by100 simp)
            finally show "el_k t = top1_path_reverse el_s t" .
          qed
          hence "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_k g}
              = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' (top1_path_reverse el_s) g}"
            using hloop_class_eq_pointwise by (by100 blast)
          \<comment> \<open>By fundamental\_group\_invg\_class: class(reverse f) = invg(class f).\<close>
          also have "\<dots> = top1_fundamental_group_invg A (subspace_topology X TX A) a'
              {g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_s g}"
          proof -
            have hel_s_loop: "top1_is_loop_on A (subspace_topology X TX A) a' el_s"
            proof -
              have "top1_continuous_map_on I_set top1_unit_interval_topology
                  A (subspace_topology X TX A) el_s"
              proof -
                have "top1_continuous_map_on I_set top1_unit_interval_topology
                    A (subspace_topology X TX A)
                    (\<lambda>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                              (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme)))"
                  using hqC_edge_cont hi_s(1) by (by100 blast)
                moreover have "\<And>t. qC ((1-t) * vxC (i_of s) + t * vxC (Suc (i_of s) mod length scheme),
                              (1-t) * vyC (i_of s) + t * vyC (Suc (i_of s) mod length scheme)) = el_s t"
                  unfolding el_s_def by (by100 simp)
                ultimately show ?thesis by (by100 simp)
              qed
              moreover have "el_s 0 = a'"
              proof -
                have "el_s 0 = qC (vxC (i_of s), vyC (i_of s))" unfolding el_s_def by (by100 simp)
                also have "\<dots> = qC (vxC 0, vyC 0)"
                proof -
                  have "0 < length scheme" using hlen by (by100 linarith)
                  thus ?thesis using hvert_C[rule_format, OF hi_s(1) \<open>0 < length scheme\<close>] by (by100 simp)
                qed
                also have "\<dots> = a" using ha_eq by (by100 simp)
                finally show ?thesis
                proof -
                  assume "el_s 0 = a"
                  have "h (1, 0) = qC (vxC 0, vyC 0)"
                  proof -
                    have "0 < length scheme" using hlen by (by100 linarith)
                    moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
                    ultimately have "h (cos (2*pi*(real 0+0)/real (length scheme)),
                        sin (2*pi*(real 0+0)/real (length scheme)))
                      = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod length scheme),
                             (1-0)*vyC 0 + 0*vyC (Suc 0 mod length scheme))"
                      using hh_edge_arc by (by100 blast)
                    thus ?thesis by (by100 simp)
                  qed
                  thus ?thesis unfolding a'_def using \<open>el_s 0 = a\<close> ha_eq by (by100 simp)
                qed
              qed
              moreover have "el_s 1 = a'"
              proof -
                have hn_pos: "length scheme > 0" using hlen by (by100 linarith)
                have hj: "Suc (i_of s) mod length scheme < length scheme"
                  using mod_less_divisor[OF hn_pos] by (by100 simp)
                have "el_s 1 = qC (vxC (Suc (i_of s) mod length scheme),
                    vyC (Suc (i_of s) mod length scheme))"
                  unfolding el_s_def by (by100 simp)
                also have "\<dots> = qC (vxC 0, vyC 0)"
                  using hvert_C[rule_format, OF hj] hn_pos by (by100 force)
                also have "\<dots> = a" using ha_eq by (by100 simp)
                finally show ?thesis
                proof -
                  assume "el_s 1 = a"
                  have "h (1, 0) = qC (vxC 0, vyC 0)"
                  proof -
                    have "0 < length scheme" using hlen by (by100 linarith)
                    moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
                    ultimately have "h (cos (2*pi*(real 0+0)/real (length scheme)),
                        sin (2*pi*(real 0+0)/real (length scheme)))
                      = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod length scheme),
                             (1-0)*vyC 0 + 0*vyC (Suc 0 mod length scheme))"
                      using hh_edge_arc by (by100 blast)
                    thus ?thesis by (by100 simp)
                  qed
                  thus ?thesis unfolding a'_def using \<open>el_s 1 = a\<close> ha_eq by (by100 simp)
                qed
              qed
              ultimately show ?thesis
                unfolding top1_is_loop_on_def top1_is_path_on_def by (by5000 blast)
            qed
            from fundamental_group_invg_class[OF hTA hel_s_loop]
            show ?thesis by (by100 simp)
          qed
          also have "\<dots> = top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F s))"
            using hphi_s by (by100 simp)
          finally show ?thesis using False by (by100 simp)
        qed
        show "let (s', b') = scheme ! k in
          {g. top1_loop_equiv_on A (subspace_topology X TX A) a' el_k g}
          = (if b' then \<phi> (\<iota>F s') else
              top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F s')))"
          unfolding hsb using hclass_eq by (by100 simp)
      qed
      \<comment> \<open>Helper: word\_product in \<pi>_1 = class of foldr path product.
         By induction on the list: each \<pi>_1\_mul step corresponds to a path\_product step
         via top1\_fundamental\_group\_mul\_class.\<close>
      have hword_foldr: "\<And>ws (fs :: nat \<Rightarrow> real \<Rightarrow> 'a).
          (\<forall>k<length ws. top1_is_loop_on A (subspace_topology X TX A) a' (fs k)) \<Longrightarrow>
          (\<forall>k<length ws. {g. top1_loop_equiv_on A (subspace_topology X TX A) a' (fs k) g}
            = (if snd (ws!k) then fst (ws!k)
               else top1_fundamental_group_invg A (subspace_topology X TX A) a' (fst (ws!k)))) \<Longrightarrow>
          top1_group_word_product
            (top1_fundamental_group_mul A (subspace_topology X TX A) a')
            (top1_fundamental_group_id A (subspace_topology X TX A) a')
            (top1_fundamental_group_invg A (subspace_topology X TX A) a')
            ws
          = {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map fs [0..<length ws]) (top1_constant_path a')) g}"
        using word_product_foldr_class[OF hTA] by (by100 blast)
      \<comment> \<open>Assembly: connect loop decomposition with word\_product in \<pi>_1.\<close>
      \<comment> \<open>Step A1: relator\_class = class of \<iota> \<circ> circle.\<close>
      \<comment> \<open>Step A2: [\<iota> \<circ> circle] = [foldr path\_product [sub\_0,...] const]
         (from loop\_split\_at\_vertices + h\_iota\_circle\_edge + reparametrization).\<close>
      \<comment> \<open>Step A3: [foldr path\_product [f\_0,...,f\_{n-1}] const]
         = \<pi>_1\_mul([f\_0], ..., \<pi>_1\_mul([f\_{n-1}], \<pi>_1\_id)...)
         (by induction using top1\_fundamental\_group\_mul\_class).\<close>
      \<comment> \<open>Step A4: Substitute [sub\_k] = \<phi>(\<iota>F(s\_k))^{b\_k} (from hsub\_class).\<close>
      \<comment> \<open>Step A5: The \<pi>_1\_mul product = word\_product\_\<pi>_1 (by definition of word\_product).\<close>
      \<comment> \<open>Apply the helper with ws = map (\<lambda>(s,b). (\<phi>(\<iota>F s), b)) scheme
         and fs k = edge\_loop\_k.\<close>
      define edge_loop_fn where "edge_loop_fn k t =
          qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
              (1-t) * vyC k + t * vyC (Suc k mod ?n))" for k :: nat and t :: real
      have hlen_eq: "length (map (\<lambda>(s,b). (\<phi> (\<iota>F s), b)) scheme) = length scheme"
        by (by100 simp)
      \<comment> \<open>Connect relator\_class with the foldr product via loop\_split\_at\_vertices.\<close>
      have hrel_foldr: "relator_class =
          {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
            (foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a')) g}"
      proof -
        let ?circle = "\<lambda>s::real. (cos (2 * pi * s), sin (2 * pi * s))"
        let ?boundary = "\<lambda>s. \<iota> (?circle s)"
        \<comment> \<open>Step 0 (moved before step 1): ?boundary is a loop at a' in A.\<close>
        have hbdy_loop: "top1_is_loop_on A (subspace_topology X TX A) a' ?boundary"
        proof -
          have hcircle_cont: "top1_continuous_map_on I_set top1_unit_interval_topology
              top1_S1 top1_S1_topology ?circle"
            using standard_S1_loop_is_loop
            unfolding top1_is_loop_on_def top1_is_path_on_def top1_unit_interval_def by (by100 blast)
          have hbdy_cont: "top1_continuous_map_on I_set top1_unit_interval_topology
              A (subspace_topology X TX A) ?boundary"
          proof -
            have "top1_continuous_map_on I_set top1_unit_interval_topology
                A (subspace_topology X TX A) (\<iota> \<circ> ?circle)"
              using top1_continuous_map_on_comp[OF hcircle_cont h\<iota>_cont] .
            moreover have "(\<iota> \<circ> ?circle) = ?boundary" unfolding comp_def by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          have hbdy0: "?boundary 0 = a'"
          proof -
            have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
            hence "\<iota> (1, 0) = h (1, 0)" using h\<iota>_eq by (by100 blast)
            thus ?thesis using ha'_base by (by100 simp)
          qed
          have hbdy1: "?boundary 1 = a'"
          proof -
            have "?circle 1 = (cos (2 * pi), sin (2 * pi))" by (by100 simp)
            also have "\<dots> = (1, 0)" by (by100 simp)
            finally have "?boundary 1 = \<iota> (1, 0)" by (by100 simp)
            also have "\<dots> = h (1, 0)"
            proof -
              have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
              thus ?thesis using h\<iota>_eq by (by100 blast)
            qed
            finally show ?thesis using ha'_base by (by100 simp)
          qed
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hbdy0 hbdy1 hbdy_cont by (by5000 blast)
        qed
        \<comment> \<open>Step 1: relator\_class = class of ?boundary.\<close>
        have hrel_eq: "relator_class = {g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}"
        proof -
          let ?circle_class = "{g'. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?circle g'}"
          have hrel_def: "relator_class = {g. \<exists>f\<in>?circle_class.
              top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> f) g}"
            unfolding relator_class_def top1_fundamental_group_induced_on_def by (by100 simp)
          \<comment> \<open>circle \<in> circle\_class (by reflexivity).\<close>
          have hcircle_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?circle"
            using standard_S1_loop_is_loop .
          have hcircle_in: "?circle \<in> ?circle_class"
            using top1_loop_equiv_on_refl[OF hcircle_loop] by (by100 blast)
          \<comment> \<open>S1 topology.\<close>
          have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis unfolding hrel_def
          proof (rule set_eqI, rule iffI)
            \<comment> \<open>Forward: if \<exists>f\<in>circle\_class. equiv(\<iota>\<circ>f, g), then equiv(\<iota>\<circ>circle, g).\<close>
            fix g assume "g \<in> {g. \<exists>f\<in>?circle_class. top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> f) g}"
            then obtain f where hf_in: "f \<in> ?circle_class"
                and hfg: "top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> f) g" by (by100 blast)
            \<comment> \<open>circle \<simeq> f in S1.\<close>
            have hcf: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?circle f"
              using hf_in by (by100 blast)
            \<comment> \<open>By continuous\_preserves: \<iota>\<circ>circle \<simeq> \<iota>\<circ>f.\<close>
            have hcf_ph: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?circle f"
              using hcf unfolding top1_loop_equiv_on_def by (by100 blast)
            have h\<iota>cf: "top1_path_homotopic_on A (subspace_topology X TX A) (\<iota> (1, 0)) (\<iota> (1, 0))
                (\<iota> \<circ> ?circle) (\<iota> \<circ> f)"
              using continuous_preserves_path_homotopic[OF hS1_top hTA h\<iota>_cont hcf_ph] .
            have h\<iota>10: "\<iota> (1, 0) = a'"
            proof -
              have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
              thus ?thesis using h\<iota>_eq ha'_base by (by100 blast)
            qed
            \<comment> \<open>\<iota> \<circ> circle \<simeq> \<iota> \<circ> f, and \<iota> \<circ> f \<simeq> g, so \<iota> \<circ> circle \<simeq> g.\<close>
            have "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g"
            proof -
              \<comment> \<open>\<iota>\<circ>circle is a loop equiv to \<iota>\<circ>f (from continuous\_preserves + ext).\<close>
              have hext: "?boundary = (\<iota> \<circ> ?circle)"
              proof (rule ext)
                fix s show "?boundary s = (\<iota> \<circ> ?circle) s" unfolding comp_def by (by100 simp)
              qed
              have h\<iota>circle_loop: "top1_is_loop_on A (subspace_topology X TX A) a' (\<iota> \<circ> ?circle)"
                using hbdy_loop unfolding hext[symmetric] .
              have h\<iota>f_loop: "top1_is_loop_on A (subspace_topology X TX A) a' (\<iota> \<circ> f)"
                using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
              have hg_loop: "top1_is_loop_on A (subspace_topology X TX A) a' g"
                using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
              have h\<iota>cf_equiv: "top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> ?circle) (\<iota> \<circ> f)"
                unfolding top1_loop_equiv_on_def
                using h\<iota>circle_loop h\<iota>f_loop h\<iota>cf h\<iota>10 by (by100 blast)
              have hbdy_iof: "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary (\<iota> \<circ> f)"
                using h\<iota>cf_equiv unfolding hext[symmetric] .
              show ?thesis using top1_loop_equiv_on_trans[OF hTA hbdy_iof hfg] .
            qed
            thus "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}" by (by100 blast)
          next
            \<comment> \<open>Backward: if equiv(?boundary, g), take f = circle.\<close>
            fix g assume "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}"
            hence hbg: "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g" by (by100 blast)
            have hext: "?boundary = (\<iota> \<circ> ?circle)"
            proof (rule ext)
              fix s show "?boundary s = (\<iota> \<circ> ?circle) s" unfolding comp_def by (by100 simp)
            qed
            have hbg': "top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> ?circle) g"
              using hbg unfolding hext[symmetric] .
            thus "g \<in> {g. \<exists>f\<in>?circle_class. top1_loop_equiv_on A (subspace_topology X TX A) a' (\<iota> \<circ> f) g}"
              using hcircle_in by (by100 blast)
          qed
        qed
        \<comment> \<open>hbdy\_loop already proved above (moved before hrel\_eq).\<close>
        \<comment> \<open>Step 3: Vertices of ?boundary are a'.\<close>
        have hvertex: "\<forall>k\<le>?n. ?boundary (real k / real ?n) = a'"
        proof (intro allI impI)
          fix k assume hk: "k \<le> ?n"
          \<comment> \<open>?boundary(k/n) = \<iota>(cos(2\<pi>k/n), sin(2\<pi>k/n)).\<close>
          \<comment> \<open>= h(cos(2\<pi>k/n), sin(2\<pi>k/n)) since point is on S1.\<close>
          have h_eq_h: "\<iota> (cos (2*pi*(real k / real ?n)), sin (2*pi*(real k / real ?n)))
              = h (cos (2*pi*(real k / real ?n)), sin (2*pi*(real k / real ?n)))"
          proof -
            have "(cos (2*pi*(real k / real ?n)), sin (2*pi*(real k / real ?n))) \<in> top1_S1"
              unfolding top1_S1_def by (by5000 force)
            thus ?thesis using h\<iota>_eq by (by100 blast)
          qed
          show "?boundary (real k / real ?n) = a'"
          proof (cases "k = ?n")
            case True
            have hn_pos: "real ?n > 0" using hlen by (by100 linarith)
            have hkn: "real k / real ?n = (1::real)"
            proof -
              have "real ?n \<noteq> (0::real)" using hn_pos by (by100 linarith)
              hence "real ?n / real ?n = (1::real)" by (rule divide_self)
              thus ?thesis using True by (by100 simp)
            qed
            have "?boundary (real k / real ?n) = \<iota> (cos (2*pi), sin (2*pi))" using hkn by (by100 simp)
            also have "\<dots> = \<iota> (1, 0)" by (by100 simp)
            also have "\<dots> = h (1, 0)"
            proof -
              have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
              thus ?thesis using h\<iota>_eq by (by100 blast)
            qed
            finally show ?thesis using ha'_base by (by100 simp)
          next
            case False
            hence hk': "k < ?n" using hk by (by100 linarith)
            \<comment> \<open>From hh\_edge\_arc at t=0: h(cos(2\<pi>k/n), sin(2\<pi>k/n)) = qC(vxC k, vyC k).\<close>
            have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
            have hh_val: "h (cos (2*pi*(real k+0)/real ?n), sin (2*pi*(real k+0)/real ?n))
                = qC ((1-0)*vxC k + 0*vxC (Suc k mod ?n), (1-0)*vyC k + 0*vyC (Suc k mod ?n))"
              using hh_edge_arc[rule_format, OF hk' h0] .
            hence "h (cos (2*pi*real k/real ?n), sin (2*pi*real k/real ?n)) = qC (vxC k, vyC k)"
              by (by100 simp)
            hence "?boundary (real k / real ?n) = qC (vxC k, vyC k)" using h_eq_h by (by100 simp)
            also have "\<dots> = qC (vxC 0, vyC 0)"
            proof -
              have "0 < ?n" using hlen by (by100 linarith)
              thus ?thesis using hvert_C[rule_format, OF hk' \<open>0 < ?n\<close>] by (by100 simp)
            qed
            also have "\<dots> = a" using ha_eq by (by100 simp)
            also have "\<dots> = a'"
            proof -
              have "h (1, 0) = qC (vxC 0, vyC 0)"
              proof -
                have "0 < ?n" using hlen by (by100 linarith)
                moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
                ultimately have "h (cos (2*pi*(real 0+0)/real ?n), sin (2*pi*(real 0+0)/real ?n))
                  = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod ?n), (1-0)*vyC 0 + 0*vyC (Suc 0 mod ?n))"
                  using hh_edge_arc by (by100 blast)
                thus ?thesis by (by100 simp)
              qed
              thus ?thesis unfolding a'_def using ha_eq by (by100 simp)
            qed
            finally show ?thesis .
          qed
        qed
        \<comment> \<open>Step 4: loop\_split\_at\_vertices decomposes ?boundary.\<close>
        define sub where "sub k s = ?boundary ((real k + s) / real ?n)" for k :: nat and s :: real
        have hn_ge1: "?n \<ge> 1" using hlen by (by100 linarith)
        have hbdy_split: "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary
            (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a'))"
        proof -
          from PolygonDisk.loop_split_at_vertices[OF hTA hbdy_loop hn_ge1 hvertex]
          have "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary
              (foldr top1_path_product
                (map (\<lambda>k. \<lambda>s. ?boundary ((real k + s) / real ?n)) [0..<?n])
                (top1_constant_path a'))" .
          moreover have hmap_eq: "map (\<lambda>k. \<lambda>s. ?boundary ((real k + s) / real ?n)) [0..<?n]
              = map sub [0..<?n]"
            unfolding sub_def by (by100 simp)
          ultimately show ?thesis using hmap_eq by (by5000 metis)
        qed
        \<comment> \<open>Step 5: sub k = edge\_loop\_fn k on I\_set (from h\_iota\_circle\_edge via hh\_edge\_arc).\<close>
        have hsub_edge: "\<forall>k<?n. \<forall>t\<in>I_set. sub k t = edge_loop_fn k t"
        proof (intro allI impI ballI)
          fix k :: nat and t :: real assume hk: "k < ?n" and ht: "t \<in> I_set"
          have "sub k t = \<iota> (cos (2*pi*((real k+t)/real ?n)), sin (2*pi*((real k+t)/real ?n)))"
            unfolding sub_def by (by100 simp)
          also have "\<dots> = h (cos (2*pi*((real k+t)/real ?n)), sin (2*pi*((real k+t)/real ?n)))"
          proof -
            have "(cos (2*pi*((real k+t)/real ?n)), sin (2*pi*((real k+t)/real ?n))) \<in> top1_S1"
              unfolding top1_S1_def by (by5000 force)
            thus ?thesis using h\<iota>_eq by (by100 blast)
          qed
          also have "\<dots> = qC ((1-t)*vxC k + t*vxC (Suc k mod ?n), (1-t)*vyC k + t*vyC (Suc k mod ?n))"
          proof -
            have "2*pi*((real k+t)/real ?n) = 2*pi*(real k+t)/real ?n" by (by100 simp)
            thus ?thesis using hh_edge_arc[rule_format, OF hk ht] by (by100 simp)
          qed
          also have "\<dots> = edge_loop_fn k t" unfolding edge_loop_fn_def by (by100 simp)
          finally show "sub k t = edge_loop_fn k t" .
        qed
        \<comment> \<open>Step 6: foldr [sub] and foldr [edge\_loop\_fn] have the same class.\<close>
        have hfoldr_eq: "{g. top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g}
            = {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a')) g}"
        proof -
          \<comment> \<open>The foldr products agree on I\_set because each component agrees on I\_set.
             path\_product f g s = f(2s) for s \<le> 1/2, g(2s-1) for s > 1/2.
             Both 2s and 2s-1 are in I\_set when s \<in> I\_set, so the agreement propagates.\<close>
          have "\<forall>t\<in>I_set. foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a') t
              = foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a') t"
          proof (intro ballI)
            fix t assume ht: "t \<in> I_set"
            \<comment> \<open>Both foldrs agree on I\_set because path\_product preserves
               I\_set-pointwise equality (2s, 2s-1 \<in> I\_set for s \<in> I\_set).\<close>
            show "foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a') t
                = foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a') t"
            proof -
              have "length (map sub [0..<?n]) = length (map edge_loop_fn [0..<?n])" by (by100 simp)
              moreover have "\<forall>k<length (map sub [0..<?n]). \<forall>t\<in>I_set.
                  (map sub [0..<?n] ! k) t = (map edge_loop_fn [0..<?n] ! k) t"
                using hsub_edge by (by100 force)
              ultimately have "\<forall>t\<in>I_set. foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a') t
                  = foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a') t"
                using foldr_path_product_pointwise_eq by (by100 blast)
              thus ?thesis using ht by (by100 blast)
            qed
          qed
          thus ?thesis using hloop_class_eq_pointwise by (by100 blast)
        qed
        \<comment> \<open>Step 7: Combine via equivalence class transitivity.\<close>
        have hbdy_class: "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}
            = {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
                (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g}"
        proof (rule set_eqI, rule iffI)
          fix g assume hg: "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}"
          hence hbg: "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g" by (by100 blast)
          have hfb: "top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) ?boundary"
            by (rule top1_loop_equiv_on_sym[OF hbdy_split])
          have "top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g"
            by (rule top1_loop_equiv_on_trans[OF hTA hfb hbg])
          thus "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g}"
            by (by100 blast)
        next
          fix g assume hg: "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g}"
          hence hfg: "top1_loop_equiv_on A (subspace_topology X TX A) a'
              (foldr top1_path_product (map sub [0..<?n]) (top1_constant_path a')) g"
            by (by100 blast)
          have "top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g"
            by (rule top1_loop_equiv_on_trans[OF hTA hbdy_split hfg])
          thus "g \<in> {g. top1_loop_equiv_on A (subspace_topology X TX A) a' ?boundary g}"
            by (by100 blast)
        qed
        show ?thesis using hrel_eq hbdy_class hfoldr_eq by (by100 simp)
      qed
      \<comment> \<open>Edge loops are loops at a'.\<close>
      have hedge_loops_fn: "\<forall>k<?n. top1_is_loop_on A (subspace_topology X TX A) a' (edge_loop_fn k)"
      proof (intro allI impI)
        fix k assume hk: "k < ?n"
        have hcont: "top1_continuous_map_on I_set top1_unit_interval_topology
            A (subspace_topology X TX A) (edge_loop_fn k)"
        proof -
          have h: "top1_continuous_map_on I_set top1_unit_interval_topology
              A (subspace_topology X TX A) (\<lambda>t. qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
                  (1-t) * vyC k + t * vyC (Suc k mod ?n)))"
            using hqC_edge_cont hk by (by100 blast)
          moreover have "\<And>t. qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
              (1-t) * vyC k + t * vyC (Suc k mod ?n)) = edge_loop_fn k t"
            unfolding edge_loop_fn_def by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have h0: "edge_loop_fn k 0 = a'"
        proof -
          have "edge_loop_fn k 0 = qC (vxC k, vyC k)" unfolding edge_loop_fn_def by (by100 simp)
          also have "\<dots> = qC (vxC 0, vyC 0)"
          proof -
            have "0 < ?n" using hlen by (by100 linarith)
            thus ?thesis using hvert_C[rule_format, OF hk \<open>0 < ?n\<close>] by (by100 simp)
          qed
          also have "\<dots> = a" using ha_eq by (by100 simp)
          finally show ?thesis
          proof -
            assume "edge_loop_fn k 0 = a"
            have "a = a'" proof -
              have "h (1, 0) = qC (vxC 0, vyC 0)"
              proof -
                have "0 < ?n" using hlen by (by100 linarith)
                moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
                ultimately have "h (cos (2*pi*(real 0+0)/real ?n), sin (2*pi*(real 0+0)/real ?n))
                  = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod ?n), (1-0)*vyC 0 + 0*vyC (Suc 0 mod ?n))"
                  using hh_edge_arc by (by100 blast)
                thus ?thesis by (by100 simp)
              qed
              thus ?thesis unfolding a'_def using ha_eq by (by100 simp)
            qed
            thus ?thesis using \<open>edge_loop_fn k 0 = a\<close> by (by100 simp)
          qed
        qed
        have h1: "edge_loop_fn k 1 = a'"
        proof -
          have hn_pos: "?n > 0" using hlen by (by100 linarith)
          have hj: "Suc k mod ?n < ?n" using mod_less_divisor[OF hn_pos] by (by100 simp)
          have "edge_loop_fn k 1 = qC (vxC (Suc k mod ?n), vyC (Suc k mod ?n))"
            unfolding edge_loop_fn_def by (by100 simp)
          also have "\<dots> = qC (vxC 0, vyC 0)"
            using hvert_C[rule_format, OF hj] hn_pos by (by100 force)
          also have "\<dots> = a" using ha_eq by (by100 simp)
          finally show ?thesis
          proof -
            assume "edge_loop_fn k 1 = a"
            have "a = a'" proof -
              have "h (1, 0) = qC (vxC 0, vyC 0)"
              proof -
                have "0 < ?n" using hlen by (by100 linarith)
                moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
                ultimately have "h (cos (2*pi*(real 0+0)/real ?n), sin (2*pi*(real 0+0)/real ?n))
                  = qC ((1-0)*vxC 0 + 0*vxC (Suc 0 mod ?n), (1-0)*vyC 0 + 0*vyC (Suc 0 mod ?n))"
                  using hh_edge_arc by (by100 blast)
                thus ?thesis by (by100 simp)
              qed
              thus ?thesis unfolding a'_def using ha_eq by (by100 simp)
            qed
            thus ?thesis using \<open>edge_loop_fn k 1 = a\<close> by (by100 simp)
          qed
        qed
        show "top1_is_loop_on A (subspace_topology X TX A) a' (edge_loop_fn k)"
          unfolding top1_is_loop_on_def top1_is_path_on_def
          using h0 h1 hcont by (by5000 blast)
      qed
      \<comment> \<open>hsub\_class in terms of edge\_loop\_fn.\<close>
      have hsub_fn: "\<forall>k<?n. {g. top1_loop_equiv_on A (subspace_topology X TX A) a' (edge_loop_fn k) g}
          = (if snd (scheme!k) then \<phi> (\<iota>F (fst (scheme!k)))
             else top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F (fst (scheme!k)))))"
      proof (intro allI impI)
        fix k assume hk: "k < ?n"
        from hsub_class[rule_format, OF hk] obtain s b where
          hsb: "scheme!k = (s, b)" and
          hc: "{g. top1_loop_equiv_on A (subspace_topology X TX A) a'
                (\<lambda>t. qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
                          (1-t) * vyC k + t * vyC (Suc k mod ?n))) g}
              = (if b then \<phi> (\<iota>F s) else
                  top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F s)))"
          by (cases "scheme!k") (by100 force)
        have "edge_loop_fn k = (\<lambda>t. qC ((1-t) * vxC k + t * vxC (Suc k mod ?n),
                                         (1-t) * vyC k + t * vyC (Suc k mod ?n)))"
          unfolding edge_loop_fn_def by (by100 simp)
        thus "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' (edge_loop_fn k) g}
            = (if snd (scheme!k) then \<phi> (\<iota>F (fst (scheme!k)))
               else top1_fundamental_group_invg A (subspace_topology X TX A) a' (\<phi> (\<iota>F (fst (scheme!k)))))"
          using hc hsb by (by100 simp)
      qed
      \<comment> \<open>Apply the helper.\<close>
      have hword_eq: "top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(s,b). (\<phi> (\<iota>F s), b)) scheme)
        = {g. top1_loop_equiv_on A (subspace_topology X TX A) a'
            (foldr top1_path_product (map edge_loop_fn [0..<?n]) (top1_constant_path a')) g}"
      proof -
        let ?ws = "map (\<lambda>(s,b). (\<phi> (\<iota>F s), b)) scheme"
        have hlen_ws: "length ?ws = ?n" by (by100 simp)
        have hloops: "\<forall>k<length ?ws. top1_is_loop_on A (subspace_topology X TX A) a' (edge_loop_fn k)"
          using hedge_loops_fn hlen_ws by (by100 simp)
        have hmatch: "\<forall>k<length ?ws. {g. top1_loop_equiv_on A (subspace_topology X TX A) a' (edge_loop_fn k) g}
            = (if snd (?ws!k) then fst (?ws!k)
               else top1_fundamental_group_invg A (subspace_topology X TX A) a' (fst (?ws!k)))"
        proof (intro allI impI)
          fix k assume hk: "k < length ?ws"
          hence hk': "k < ?n" using hlen_ws by (by100 simp)
          have "?ws!k = (\<lambda>(s,b). (\<phi> (\<iota>F s), b)) (scheme!k)"
            using nth_map[OF hk'] by (by100 blast)
          hence "?ws!k = (\<phi> (\<iota>F (fst (scheme!k))), snd (scheme!k))"
            by (cases "scheme!k") (by100 simp)
          hence "fst (?ws!k) = \<phi> (\<iota>F (fst (scheme!k)))" "snd (?ws!k) = snd (scheme!k)"
            by (by100 simp)+
          thus "{g. top1_loop_equiv_on A (subspace_topology X TX A) a' (edge_loop_fn k) g}
              = (if snd (?ws!k) then fst (?ws!k) else
                  top1_fundamental_group_invg A (subspace_topology X TX A) a' (fst (?ws!k)))"
            using hsub_fn[rule_format, OF hk'] by (by100 simp)
        qed
        from hword_foldr[OF hloops hmatch]
        show ?thesis using hlen_ws by (by100 simp)
      qed
      show ?thesis using hrel_foldr hword_eq by (by100 simp)
    qed
    \<comment> \<open>Step R2: \<phi> is a hom, so \<phi>(word\_product in F) = word\_product in \<pi>_1(A,a').\<close>
    have hphi_word: "\<phi> (top1_group_word_product mulF eF invgF
          (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))
      = top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(s, b). (\<phi> (\<iota>F s), b)) scheme)"
      using hom_word_product[OF _ hpi1_A_grp h\<phi>_hom, of eF invgF
          "map (\<lambda>(s, b). (\<iota>F s, b)) scheme"]
        hfree[unfolded top1_is_free_group_full_on_def]
    proof -
      have hF_grp: "top1_is_group_on F mulF eF invgF"
        using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
      have hgens: "\<forall>i<length (map (\<lambda>(s, b). (\<iota>F s, b)) scheme).
          fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) \<in> F"
      proof (intro allI impI)
        fix i assume hi: "i < length (map (\<lambda>(s, b). (\<iota>F s, b)) scheme)"
        hence hi': "i < length scheme" by (by100 simp)
        have "(map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i = (\<lambda>(s, b). (\<iota>F s, b)) (scheme ! i)"
          using nth_map[OF hi'] by (by100 blast)
        hence "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) = \<iota>F (fst (scheme ! i))"
          by (cases "scheme ! i") (by100 simp)
        moreover have "fst (scheme ! i) \<in> fst ` set scheme" using hi' by (by100 force)
        moreover have "\<iota>F (fst (scheme ! i)) \<in> F"
          using hfree unfolding top1_is_free_group_full_on_def
          using \<open>fst (scheme ! i) \<in> fst ` set scheme\<close> by (by100 blast)
        ultimately show "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) \<in> F"
          by (by100 simp)
      qed
      from hom_word_product[OF hF_grp hpi1_A_grp h\<phi>_hom hgens]
      have "\<phi> (top1_group_word_product mulF eF invgF
          (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))
        = top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(x, b). (\<phi> x, b)) (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))" .
      also have "top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(x, b). (\<phi> x, b)) (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))
        = top1_group_word_product
          (top1_fundamental_group_mul A (subspace_topology X TX A) a')
          (top1_fundamental_group_id A (subspace_topology X TX A) a')
          (top1_fundamental_group_invg A (subspace_topology X TX A) a')
          (map (\<lambda>(s, b). (\<phi> (\<iota>F s), b)) scheme)"
      proof -
        have hmap_eq: "map (\<lambda>(x::int, b::bool). (\<phi> x, b)) (map (\<lambda>(s::nat, b::bool). (\<iota>F s, b)) scheme)
          = map (\<lambda>(s::nat, b::bool). (\<phi> (\<iota>F s), b)) scheme"
          using map_map_pair_compose[of \<phi> \<iota>F scheme] .
        show ?thesis unfolding hmap_eq ..
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>Step R3: combine R1 + R2 + bijectivity of \<phi> to get \<phi>^{-1}(relator).\<close>
    have hrelator_word: "inv_into F \<phi> relator_class =
        top1_group_word_product mulF eF invgF
          (map (\<lambda>(s, b). (\<iota>F s, b)) (map (\<lambda>(s,b). (s, b)) scheme))"
    proof -
      have "map (\<lambda>(s::nat, b::bool). (s, b)) scheme = scheme" by (by100 simp)
      moreover have "relator_class = \<phi> (top1_group_word_product mulF eF invgF
          (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))"
        using hrel_product hphi_word by (by100 simp)
      moreover have hwp_in: "top1_group_word_product mulF eF invgF
          (map (\<lambda>(s, b). (\<iota>F s, b)) scheme) \<in> F"
      proof -
        have hF_grp: "top1_is_group_on F mulF eF invgF"
          using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
        have hgens_in: "\<And>i. i < length (map (\<lambda>(s, b). (\<iota>F s, b)) scheme) \<Longrightarrow>
            fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) \<in> F"
        proof -
          fix i assume hi: "i < length (map (\<lambda>(s, b). (\<iota>F s, b)) scheme)"
          hence hi': "i < length scheme" by (by100 simp)
          have "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) = \<iota>F (fst (scheme ! i))"
          proof -
            have "(map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i = (\<lambda>(s, b). (\<iota>F s, b)) (scheme ! i)"
              using nth_map[OF hi'] by (by100 blast)
            thus ?thesis by (cases "scheme ! i") (by100 simp)
          qed
          moreover have "fst (scheme ! i) \<in> fst ` set scheme"
            using hi' by (by100 force)
          moreover have "\<iota>F (fst (scheme ! i)) \<in> F"
          proof -
            have "\<forall>s \<in> fst ` set scheme. \<iota>F s \<in> F"
              using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
            thus ?thesis using \<open>fst (scheme ! i) \<in> fst ` set scheme\<close> by (by100 blast)
          qed
          ultimately show "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) \<in> F"
            by (by100 simp)
        qed
        have hgens_in_all: "\<forall>i<length (map (\<lambda>(s, b). (\<iota>F s, b)) scheme).
            fst ((map (\<lambda>(s, b). (\<iota>F s, b)) scheme) ! i) \<in> F"
          using hgens_in by (by100 blast)
        thus ?thesis using word_product_in_group[OF hF_grp hgens_in_all] by (by100 simp)
      qed
      ultimately show ?thesis
      proof -
        assume hmap: "map (\<lambda>(s::nat, b::bool). (s, b)) scheme = scheme"
        assume hrel_eq: "relator_class = \<phi> (top1_group_word_product mulF eF invgF
            (map (\<lambda>(s, b). (\<iota>F s, b)) scheme))"
        have "inv_into F \<phi> (\<phi> (top1_group_word_product mulF eF invgF
            (map (\<lambda>(s, b). (\<iota>F s, b)) scheme)))
          = top1_group_word_product mulF eF invgF
            (map (\<lambda>(s, b). (\<iota>F s, b)) scheme)"
        proof -
          have "inj_on \<phi> F" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
          thus ?thesis using inv_into_f_f[OF _ hwp_in] by (by100 blast)
        qed
        thus ?thesis using hrel_eq hmap by (by100 simp)
      qed
    qed
    \<comment> \<open>From hrelator\_word + first\_isomorphism\_theorem + h\<iota>\_iso:
       F / N(scheme\_word\_in\_F) \<cong> Q \<cong> \<pi>_1(X,a').
       This gives the presentation.\<close>
    \<comment> \<open>Q is presented by (S, {scheme}).
       Use proj \<circ> \<phi> as the surjective hom from F to Q.
       ker = {f \<in> F. \<phi> f \<in> N} = N(scheme word) (from hrelator\_word).\<close>
    define eQ where "eQ = top1_group_coset_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
        (top1_fundamental_group_id A (subspace_topology X TX A) a')"
    define invgQ where "invgQ C = top1_group_coset_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') N
        (top1_fundamental_group_invg A (subspace_topology X TX A) a'
          (SOME g. g \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) a' \<and>
                   C = top1_group_coset_on
                     (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
                     (top1_fundamental_group_mul A (subspace_topology X TX A) a') N g))" for C
    have hQ_grp: "top1_is_group_on Q mulQ eQ invgQ"
      using quotient_group_is_group[OF hpi1_A_grp hN_normal]
        unfolding Q_def mulQ_def eQ_def invgQ_def by (by100 simp)
    \<comment> \<open>Combine: from hrel\_product + hphi\_word + hrelator\_word + first iso theorem:
       Q is presented by (S, {scheme}) and Q \<cong> \<pi>_1(X,a').
       Use presentation\_from\_free\_quotient helper (proved separately).\<close>
    \<comment> \<open>Final assembly: Q is presented and Q \<cong> \<pi>_1(X,a').\<close>
    have hQ_iso_pi1: "top1_groups_isomorphic_on Q mulQ
        (top1_fundamental_group_carrier X TX a')
        (top1_fundamental_group_mul X TX a')"
      using top1_groups_isomorphic_on_sym[OF h\<iota>_iso' hpi1_X_grp hQ_grp] .
    \<comment> \<open>Q is presented by (S, {scheme}).
       Use presentation\_from\_free\_quotient helper.\<close>
    have h\<phi>_iso: "top1_group_iso_on F mulF
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a')
        (top1_fundamental_group_mul A (subspace_topology X TX A) a') \<phi>"
      using h\<phi>_hom h\<phi>_bij unfolding top1_group_iso_on_def by (by100 blast)
    have hw_valid: "\<forall>i<length (map (\<lambda>(s::nat,b::bool). (s, b)) scheme).
        fst ((map (\<lambda>(s,b). (s, b)) scheme) ! i) \<in> fst ` set scheme"
      by (by100 force)
    have hproj_ker': "top1_group_kernel_on
        (top1_fundamental_group_carrier A (subspace_topology X TX A) a') eQ proj = N"
      using hproj_ker unfolding eQ_def by (by100 simp)
    have hpfq: "top1_group_presented_by_on Q mulQ eQ invgQ
        (fst ` set scheme) { map (\<lambda>(s,b). (s, b)) scheme }
      \<and> top1_groups_isomorphic_on Q mulQ
          (top1_fundamental_group_carrier X TX a')
          (top1_fundamental_group_mul X TX a')"
      using presentation_from_free_quotient[OF hfree hpi1_A_grp hpi1_X_grp h\<phi>_iso
          hproj_hom hproj_surj hproj_ker' hQ_grp h\<iota>_iso' hrelator_word hrel_in N_def hw_valid] .
    from hpfq have hpres: "top1_group_presented_by_on Q mulQ eQ invgQ
        (fst ` set scheme) { map (\<lambda>(s,b). (s, b)) scheme }" by (by100 blast)
    from hpfq have hiso: "top1_groups_isomorphic_on Q mulQ
        (top1_fundamental_group_carrier X TX a')
        (top1_fundamental_group_mul X TX a')" by (by100 blast)
    have hconj: "top1_group_presented_by_on Q mulQ eQ invgQ (fst ` set scheme)
          { map (\<lambda>(s,b). (s, b)) scheme }
        \<and> top1_groups_isomorphic_on Q mulQ
            (top1_fundamental_group_carrier X TX a')
            (top1_fundamental_group_mul X TX a')"
      using hpres hiso by (by100 blast)
    from hconj show ?thesis
      by - (rule exI, rule exI, rule exI, rule exI, assumption)
  qed
  \<comment> \<open>Step (iv): Transfer a' \<rightarrow> a via basepoint change.\<close>
  have hThm72_a: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set scheme)
        { map (\<lambda>(s,b). (s, b)) scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX a)
          (top1_fundamental_group_mul X TX a)"
  proof -
    from hThm72_a' obtain G0 :: "(real \<Rightarrow> 'a) set set set" and mul0 e0 invg0 where
      hpres: "top1_group_presented_by_on G0 mul0 e0 invg0 (fst ` set scheme)
          { map (\<lambda>(s,b). (s, b)) scheme }" and
      hiso_a': "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX a')
          (top1_fundamental_group_mul X TX a')"
      by (by5000 blast)
    \<comment> \<open>Basepoint change: \<pi>_1(X, a') \<cong> \<pi>_1(X, a) since X path-connected.\<close>
    have hTX: "is_topology_on X TX"
      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
    have ha_X: "a \<in> X"
    proof -
      have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      thus ?thesis using ha_A by (by100 blast)
    qed
    have ha'_X: "a' \<in> X"
    proof -
      have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      thus ?thesis using ha'_A by (by100 blast)
    qed
    have hiso_change: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX a')
        (top1_fundamental_group_mul X TX a')
        (top1_fundamental_group_carrier X TX a)
        (top1_fundamental_group_mul X TX a)"
    proof -
      have hX_pc_loc: "top1_path_connected_on X TX"
      proof -
        have hP_pc_l: "top1_path_connected_on P ?TP"
        proof -
          have hTP_l: "is_topology_on P ?TP"
            using hq unfolding top1_quotient_map_on_def by (by100 blast)
          show ?thesis unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on P ?TP" by (rule hTP_l)
          next
            fix x y assume "x \<in> P" "y \<in> P"
            define \<gamma> where "\<gamma> t = ((1-t)*fst x + t*fst y, (1-t)*snd x + t*snd y)" for t
            have "\<forall>t\<in>I_set. \<gamma> t \<in> P"
              using polygonal_region_convex_combo[OF hPoly hlen \<open>x \<in> P\<close> \<open>y \<in> P\<close>]
              unfolding \<gamma>_def top1_unit_interval_def by (by100 auto)
            moreover have "top1_continuous_map_on I_set I_top P ?TP \<gamma>"
            proof -
              have "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y \<gamma>"
                using R2_straight_line_path[of x y] unfolding \<gamma>_def by (by100 simp)
              hence "top1_continuous_map_on I_set I_top UNIV
                  (product_topology_on top1_open_sets top1_open_sets) \<gamma>"
                unfolding top1_is_path_on_def by (by100 blast)
              thus ?thesis using \<open>\<forall>t\<in>I_set. \<gamma> t \<in> P\<close>
                by (rule continuous_map_restrict_codomain) (by100 blast)
            qed
            moreover have "\<gamma> 0 = x" "\<gamma> 1 = y" unfolding \<gamma>_def by (by100 simp)+
            ultimately show "\<exists>f. top1_is_path_on P ?TP x y f"
              unfolding top1_is_path_on_def by (by100 blast)
          qed
        qed
        have hq_cont_l: "top1_continuous_map_on P ?TP X TX q"
          using hq unfolding top1_quotient_map_on_def by (by100 blast)
        have hq_maps_l: "\<forall>x\<in>P. q x \<in> X"
          using hq_cont_l unfolding top1_continuous_map_on_def by (by5000 blast)
        have hq_surj_l: "q ` P = X"
          using hq unfolding top1_quotient_map_on_def by (by5000 blast)
        have hsubself: "subspace_topology X TX X = TX"
        proof -
          have "\<forall>U\<in>TX. U \<subseteq> X" using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
          thus ?thesis by (rule subspace_topology_self)
        qed
        have "X \<subseteq> X" by (by100 blast)
        have "TX = subspace_topology X TX X" using hsubself by (by100 simp)
        from top1_path_connected_continuous_image[OF hP_pc_l hq_cont_l hq_maps_l hq_surj_l
            \<open>X \<subseteq> X\<close> this hTX]
        show ?thesis .
      qed
      from Theorem_52_1_iso[OF hTX hX_pc_loc ha'_X ha_X] show ?thesis .
    qed
    have "top1_groups_isomorphic_on G0 mul0
        (top1_fundamental_group_carrier X TX a)
        (top1_fundamental_group_mul X TX a)"
      by (rule groups_isomorphic_trans_fwd[OF hiso_a' hiso_change])
    hence hpres_iso_a: "top1_group_presented_by_on G0 mul0 e0 invg0 (fst ` set scheme)
          { map (\<lambda>(s,b). (s, b)) scheme }
        \<and> top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX a)
          (top1_fundamental_group_mul X TX a)"
      using hpres by (by100 blast)
    show ?thesis using hpres_iso_a
      apply -
      apply (rule exI[of _ G0])
      apply (rule exI[of _ mul0])
      apply (rule exI[of _ e0])
      apply (rule exI[of _ invg0])
      apply assumption
      done
  qed
  \<comment> \<open>Transfer from basepoint a to basepoint x0 using path-connectivity.\<close>
  have hX_pc: "top1_path_connected_on X TX"
  proof -
    \<comment> \<open>P is path-connected (convex polygon). q is continuous surjection. X = q(P) path-connected.\<close>
    have hP_pc: "top1_path_connected_on P ?TP"
    proof -
      \<comment> \<open>Convex set: for any a, b \<in> P, the line segment from a to b is in P.
         The straight line path is a path in P (from R2\_straight\_line\_path + restrict).\<close>
      have hTP_loc: "is_topology_on P ?TP"
        using hq unfolding top1_quotient_map_on_def by (by100 blast)
      have hR2_top: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on top1_open_sets top1_open_sets)"
        using top1_R2_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
      show ?thesis unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on P ?TP" by (rule hTP_loc)
      next
        fix x y assume hx: "x \<in> P" and hy: "y \<in> P"
        \<comment> \<open>Line segment from x to y: \<gamma>(t) = (1-t)*x + t*y lies in P (convexity).\<close>
        define \<gamma> where "\<gamma> t = ((1-t)*fst x + t*fst y, (1-t)*snd x + t*snd y)" for t
        have himg: "\<forall>t\<in>I_set. \<gamma> t \<in> P"
          using polygonal_region_convex_combo[OF hPoly hlen hx hy]
          unfolding \<gamma>_def top1_unit_interval_def by (by100 auto)
        have hR2_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets)
            x y \<gamma>"
          using R2_straight_line_path[of x y] unfolding \<gamma>_def by (by100 simp)
        have hcont: "top1_continuous_map_on I_set I_top UNIV
            (product_topology_on top1_open_sets top1_open_sets) \<gamma>"
          using hR2_path unfolding top1_is_path_on_def by (by100 blast)
        have "top1_continuous_map_on I_set I_top P ?TP \<gamma>"
          by (rule continuous_map_restrict_codomain[OF hcont himg]) (by100 blast)
        moreover have "\<gamma> 0 = x" unfolding \<gamma>_def by (by100 simp)
        moreover have "\<gamma> 1 = y" unfolding \<gamma>_def by (by100 simp)
        ultimately have "top1_is_path_on P ?TP x y \<gamma>"
          unfolding top1_is_path_on_def by (by100 blast)
        thus "\<exists>f. top1_is_path_on P ?TP x y f" by (by100 blast)
      qed
    qed
    have hq_cont_loc: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    have hq_maps: "\<forall>x\<in>P. q x \<in> X"
      using hq_cont_loc unfolding top1_continuous_map_on_def by (by5000 blast)
    have hq_surj: "q ` P = X"
      using hq unfolding top1_quotient_map_on_def by (by5000 blast)
    have "X \<subseteq> X" by (by100 blast)
    have "subspace_topology X TX X = TX"
    proof -
      have "\<forall>U\<in>TX. U \<subseteq> X" using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_self)
    qed
    have hTX_loc: "is_topology_on X TX"
      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
    from top1_path_connected_continuous_image[OF hP_pc hq_cont_loc hq_maps hq_surj
        _ _ hTX_loc, of TX]
    show ?thesis using \<open>subspace_topology X TX X = TX\<close> by (by100 simp)
  qed
  have hTX: "is_topology_on X TX"
    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
  have ha_X: "a \<in> X"
  proof -
    have "A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
    thus ?thesis using ha_A by (by100 blast)
  qed
  have hpi1_base_change: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a)
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    by (rule Theorem_52_1_iso[OF hTX hX_pc ha_X hx0])
  \<comment> \<open>Compose: G \<cong> \<pi>_1(X, a) \<cong> \<pi>_1(X, x0).\<close>
  show ?thesis
  proof -
    from hThm72_a obtain G0 :: "(real \<Rightarrow> 'a) set set set" and mul0 e0 invg0 where
      hpres0: "top1_group_presented_by_on G0 mul0 e0 invg0 (fst ` set scheme)
          { map (\<lambda>(s,b). (s, b)) scheme }" and
      hiso0: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a)"
      by (by5000 blast)
    have hiso_x0: "top1_groups_isomorphic_on G0 mul0
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
      by (rule groups_isomorphic_trans_fwd[OF hiso0 hpi1_base_change])
    have hresult: "top1_group_presented_by_on G0 mul0 e0 invg0 (fst ` set scheme)
          { map (\<lambda>(s,b). (s, b)) scheme }
        \<and> top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
      using hpres0 hiso_x0 by (by100 blast)
    from hresult show ?thesis
      by - (rule exI, rule exI, rule exI, rule exI, assumption)
  qed
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
  shows "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
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
      \<and> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. q (vx i, vy i) = q (vx j, vy j))
      \<and> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
               (1-t) * vy i + t * vy (Suc i mod length ?scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length ?scheme),
               (1-s) * vy j + s * vy (Suc j mod length ?scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (?scheme!i) = fst (?scheme!j) \<and>
               (if snd (?scheme!i) = snd (?scheme!j) then s = t else s = 1 - t)))"
  proof -
    \<comment> \<open>Extract (P, q, vx, vy) from the torus scheme definition.\<close>
    obtain P q vx vy where
      hP: "top1_is_polygonal_region_on P (length ?scheme)" and
      hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
      hlen3: "length ?scheme \<ge> 3" and
      hverts: "\<forall>i<length ?scheme. (vx i, vy i) \<in> P" and
      hP_hull_loc: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length ?scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length ?scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length ?scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length ?scheme. coeffs i * vy i)}" and
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
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')" and
      hno_extra_loc: "\<forall>i<length ?scheme. \<forall>j<length ?scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
               (1-t) * vy i + t * vy (Suc i mod length ?scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length ?scheme),
               (1-s) * vy j + s * vy (Suc j mod length ?scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (?scheme!i) = fst (?scheme!j) \<and>
               (if snd (?scheme!i) = snd (?scheme!j) then s = t else s = 1 - t))"
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
    show ?thesis
      apply (rule exI[of _ P], rule exI[of _ q], rule exI[of _ vx], rule exI[of _ vy])
      apply (intro conjI)
      using hP apply (by100 blast)
      using hq apply (by100 blast)
      using hverts apply (by100 blast)
      using hvert_ident apply (by100 blast)
      using hno_extra_loc apply (by100 blast)
      done
  qed
  \<comment> \<open>Apply Theorem 74.2.\<close>
  have h742: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set ?scheme)
        { map (\<lambda>(s,b). (s, b)) ?scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)"
  proof -
    have hvc: "\<forall>q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
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
      using torus_scheme_vertex_connectivity[of n]
        unfolding top1_n_torus_scheme_def by (by5000 simp)
    have htd: "\<forall>\<alpha>\<in>fst ` set ?scheme.
        \<exists>i<length ?scheme. fst (?scheme!i) = \<alpha> \<and> snd (?scheme!i) = True"
    proof (intro ballI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> fst ` set ?scheme"
      \<comment> \<open>Each label \<alpha> in the torus scheme has (\<alpha>, True) \<in> set scheme.\<close>
      have "(\<alpha>, True) \<in> set ?scheme"
      proof -
        from h\<alpha> obtain x where "x \<in> set ?scheme" "fst x = \<alpha>" by (by100 blast)
        then obtain k where hk: "k < n" and "x \<in> set [(2*k, True), (2*k+1, True), (2*k, False), (2*k+1, False)]"
          unfolding top1_n_torus_scheme_def by (by5000 auto)
        hence "\<alpha> = 2*k \<or> \<alpha> = 2*k+1" using \<open>fst x = \<alpha>\<close> by (by100 auto)
        moreover have "(2*k, True) \<in> set ?scheme"
          unfolding top1_n_torus_scheme_def using hk by (by5000 auto)
        moreover have "(2*k+1, True) \<in> set ?scheme"
          unfolding top1_n_torus_scheme_def using hk by (by5000 auto)
        ultimately show ?thesis by (by100 blast)
      qed
      then obtain i where "i < length ?scheme" "?scheme!i = (\<alpha>, True)"
        using in_set_conv_nth by (by5000 metis)
      thus "\<exists>i<length ?scheme. fst (?scheme!i) = \<alpha> \<and> snd (?scheme!i) = True"
        by (by100 force)
    qed
    from Theorem_74_2_scheme_presentation[OF hscheme assms(2) hlen hvert htd hvc]
    show ?thesis .
  qed
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
      and hcomm: "\<And>(F::int set) mulF eF invgF \<iota> \<pi>.
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
  shows "\<exists>(H :: (real \<Rightarrow> 'a) set set set set) mulH eH invgH \<iota>_S \<phi>.
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
  have h_presentation: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg ({..<2*n}::nat set)
        { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    using Theorem_74_3_fund_group_n_torus[OF assms] by (by100 simp)
  \<comment> \<open>Step 2: Abelianize. The presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩ abelianizes to
     the free abelian group on 2n generators (commutator relator becomes trivial).\<close>
  \<comment> \<open>Step 2: Apply presented\_comm\_relator\_abelianization + abelianization\_transfer\_iso.\<close>
  from h_presentation obtain G0 :: "(real \<Rightarrow> 'a) set set set" and mul0 e0 invg0
    where hpres0: "top1_group_presented_by_on G0 mul0 e0 invg0 ({..<2*n}::nat set)
        { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                              (2*i, False), (2*i+1, False)]) [0..<n]) }"
      and hiso0: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    by (by100 auto)
  \<comment> \<open>Abelianize the presented group G0: Abel(G0) is free abelian on {..<2n}.\<close>
  have habel0: "\<exists>(H :: (real \<Rightarrow> 'a) set set set set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G0 mul0 e0 invg0 \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H ({..<2*n}::nat set)"
    using hpres0[unfolded top1_group_presented_by_on_def]
    apply (elim conjE exE)
    apply (frule torus_relator_commutator, assumption+)
    apply (drule(4) abelianization_of_presented_group)
    apply (by100 blast)
    done
  \<comment> \<open>Extract the abelianization witnesses.\<close>
  from habel0 obtain H0 :: "(real \<Rightarrow> 'a) set set set set" and mulH0 eH0 invgH0 \<phi>0 \<iota>H0
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

section \<open>\<S>73 Fundamental Groups of the Torus and the Dunce Cap\<close>

text \<open>Helper: centralizer of an element is a subgroup.\<close>
lemma centralizer_is_subgroup:
  assumes hG: "top1_is_group_on G mul e invg" and ha: "a \<in> G"
  shows "top1_is_group_on {g \<in> G. mul a g = mul g a} mul e invg"
proof -
  let ?C = "{g \<in> G. mul a g = mul g a}"
  have hmul_cl: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y \<in> G"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hinv_cl: "\<And>x. x \<in> G \<Longrightarrow> invg x \<in> G"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hid_l: "\<And>x. x \<in> G \<Longrightarrow> mul e x = x"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hid_r: "\<And>x. x \<in> G \<Longrightarrow> mul x e = x"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hinv_l: "\<And>x. x \<in> G \<Longrightarrow> mul (invg x) x = e"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have hinv_r: "\<And>x. x \<in> G \<Longrightarrow> mul x (invg x) = e"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have he: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
  show ?thesis unfolding top1_is_group_on_def
  proof (intro conjI ballI)
    have "mul a e = a" using hid_r[OF ha] by (by100 blast)
    moreover have "mul e a = a" using hid_l[OF ha] by (by100 blast)
    ultimately show "e \<in> ?C" using he by (by100 auto)
  next
    fix x y assume hx: "x \<in> ?C" and hy: "y \<in> ?C"
    hence hxG: "x \<in> G" and hyG: "y \<in> G" and hax: "mul a x = mul x a" and hay: "mul a y = mul y a"
      by (by100 auto)+
    have hxyG: "mul x y \<in> G" using hmul_cl[OF hxG hyG] by (by100 blast)
    have "mul a (mul x y) = mul (mul a x) y" using hassoc ha hxG hyG by (by5000 metis)
    also have "\<dots> = mul (mul x a) y" using hax by (by100 simp)
    also have "\<dots> = mul x (mul a y)" using hassoc hxG ha hyG by (by5000 metis)
    also have "\<dots> = mul x (mul y a)" using hay by (by100 simp)
    also have "\<dots> = mul (mul x y) a" using hassoc hxG hyG ha by (by5000 metis)
    finally show "mul x y \<in> ?C" using hxyG by (by100 blast)
  next
    fix x assume hx: "x \<in> ?C"
    hence hxG: "x \<in> G" and hax: "mul a x = mul x a" by (by100 auto)+
    have hixG: "invg x \<in> G" using hinv_cl[OF hxG] by (by100 blast)
    \<comment> \<open>From ax = xa, derive a(x\<inverse>) = (x\<inverse>)a by left-cancellation.
       x \<cdot> (a \<cdot> x\<inverse>) = (xa) \<cdot> x\<inverse> = (ax) \<cdot> x\<inverse> = a \<cdot> (x \<cdot> x\<inverse>) = a \<cdot> e = a.
       x \<cdot> (x\<inverse> \<cdot> a) = (x \<cdot> x\<inverse>) \<cdot> a = e \<cdot> a = a.
       So x \<cdot> (a \<cdot> x\<inverse>) = x \<cdot> (x\<inverse> \<cdot> a), hence a \<cdot> x\<inverse> = x\<inverse> \<cdot> a.\<close>
    have h1: "mul x (mul a (invg x)) = a"
    proof -
      have "mul x (mul a (invg x)) = mul (mul x a) (invg x)"
        using hassoc hxG ha hixG by (by5000 metis)
      also have "\<dots> = mul (mul a x) (invg x)" using hax by (by100 simp)
      also have "\<dots> = mul a (mul x (invg x))" using hassoc ha hxG hixG by (by5000 metis)
      also have "\<dots> = mul a e" using hinv_r[OF hxG] by (by100 simp)
      also have "\<dots> = a" using hid_r[OF ha] by (by100 blast)
      finally show ?thesis .
    qed
    have h2: "mul x (mul (invg x) a) = a"
    proof -
      have "mul x (mul (invg x) a) = mul (mul x (invg x)) a"
        using hassoc hxG hixG ha by (by5000 metis)
      also have "\<dots> = mul e a" using hinv_r[OF hxG] by (by100 simp)
      also have "\<dots> = a" using hid_l[OF ha] by (by100 blast)
      finally show ?thesis .
    qed
    have "mul a (invg x) = mul (invg x) a"
    proof -
      from h1 h2 have "mul x (mul a (invg x)) = mul x (mul (invg x) a)" by (by100 simp)
      \<comment> \<open>Left cancellation: mul x u = mul x v \<Rightarrow> u = v.\<close>
      hence "mul (invg x) (mul x (mul a (invg x))) = mul (invg x) (mul x (mul (invg x) a))"
        by (by100 simp)
      hence "mul (mul (invg x) x) (mul a (invg x)) = mul (mul (invg x) x) (mul (invg x) a)"
        using hassoc hixG hxG hmul_cl[OF ha hixG] hmul_cl[OF hixG ha] by (by5000 metis)
      hence "mul e (mul a (invg x)) = mul e (mul (invg x) a)"
        using hinv_l[OF hxG] by (by100 simp)
      thus ?thesis using hid_l hmul_cl[OF ha hixG] hmul_cl[OF hixG ha] by (by5000 metis)
    qed
    thus "invg x \<in> ?C" using hixG by (by100 blast)
  next
    fix x y z assume "x \<in> ?C" "y \<in> ?C" "z \<in> ?C"
    thus "mul (mul x y) z = mul x (mul y z)" using hassoc by (by100 auto)
  next
    fix x assume "x \<in> ?C" thus "mul e x = x" using hid_l by (by100 auto)
  next
    fix x assume "x \<in> ?C" thus "mul x e = x" using hid_r by (by100 auto)
  next
    fix x assume "x \<in> ?C" thus "mul (invg x) x = e" using hinv_l by (by100 auto)
  next
    fix x assume "x \<in> ?C" thus "mul x (invg x) = e" using hinv_r by (by100 auto)
  qed
qed

text \<open>Helper: surjective hom preserves generation.\<close>
lemma surjective_hom_preserves_generation:
  assumes hF_grp: "top1_is_group_on F mulF eF invgF"
    and hG_grp: "top1_is_group_on G mul e invg"
    and hF_gen: "F = top1_subgroup_generated_on F mulF eF invgF S"
    and hhom: "top1_group_hom_on F mulF G mul \<pi>"
    and hsurj: "\<pi> ` F = G"
    and hS_sub: "S \<subseteq> F"
  shows "G = top1_subgroup_generated_on G mul e invg (\<pi> ` S)"
proof
  show "top1_subgroup_generated_on G mul e invg (\<pi> ` S) \<subseteq> G"
    by (rule subgroup_generated_subset[OF hG_grp])
       (use hhom hS_sub in \<open>unfold top1_group_hom_on_def, by100 blast\<close>)
next
  show "G \<subseteq> top1_subgroup_generated_on G mul e invg (\<pi> ` S)"
  proof
    fix g assume "g \<in> G"
    then obtain f where hf: "f \<in> F" "\<pi> f = g" using hsurj by (by100 blast)
    let ?H = "top1_subgroup_generated_on G mul e invg (\<pi> ` S)"
    let ?H' = "{f \<in> F. \<pi> f \<in> ?H}"
    have hH_grp: "top1_is_group_on ?H mul e invg"
      by (rule intersection_of_subgroups_is_group[OF hG_grp])
         (use hhom hS_sub in \<open>unfold top1_group_hom_on_def, by100 blast\<close>)
    have hH'_sub: "?H' \<subseteq> F" by (by100 blast)
    have h\<pi>S_sub_G: "\<pi> ` S \<subseteq> G"
      using hhom hS_sub unfolding top1_group_hom_on_def by (by100 blast)
    have hS_in_H': "S \<subseteq> ?H'"
    proof
      fix s assume hs: "s \<in> S"
      hence "s \<in> F" using hS_sub by (by100 blast)
      have "\<pi> s \<in> \<pi> ` S" using hs by (by100 blast)
      hence "\<pi> s \<in> ?H"
        using subgroup_generated_contains[OF hG_grp h\<pi>S_sub_G] by (by100 blast)
      thus "s \<in> ?H'" using \<open>s \<in> F\<close> by (by100 blast)
    qed
    have hH'_grp: "top1_is_group_on ?H' mulF eF invgF"
      unfolding top1_is_group_on_def
    proof (intro conjI ballI)
      have "\<pi> eF = e" by (rule hom_preserves_id[OF hF_grp hG_grp hhom])
      moreover have "e \<in> ?H" using hH_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "eF \<in> F" using hF_grp unfolding top1_is_group_on_def by (by100 blast)
      ultimately show "eF \<in> ?H'" by (by100 blast)
    next
      fix x y assume "x \<in> ?H'" "y \<in> ?H'"
      hence hxF: "x \<in> F" and hyF: "y \<in> F" and hxH: "\<pi> x \<in> ?H" and hyH: "\<pi> y \<in> ?H"
        by (by100 auto)+
      have hmxy: "mulF x y \<in> F" using hF_grp hxF hyF unfolding top1_is_group_on_def by (by100 blast)
      have "\<pi> (mulF x y) = mul (\<pi> x) (\<pi> y)"
        using hhom hxF hyF unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "mul (\<pi> x) (\<pi> y) \<in> ?H"
        using hH_grp hxH hyH unfolding top1_is_group_on_def by (by100 blast)
      ultimately have "\<pi> (mulF x y) \<in> ?H" by (by100 simp)
      thus "mulF x y \<in> ?H'" using hmxy by (by100 blast)
    next
      fix x assume "x \<in> ?H'"
      hence hxF: "x \<in> F" and hxH: "\<pi> x \<in> ?H" by (by100 auto)+
      have hixF: "invgF x \<in> F" using hF_grp hxF unfolding top1_is_group_on_def by (by100 blast)
      have "\<pi> (invgF x) = invg (\<pi> x)"
        by (rule hom_preserves_inv[OF hF_grp hG_grp hhom hxF])
      moreover have "invg (\<pi> x) \<in> ?H"
        using hH_grp hxH unfolding top1_is_group_on_def by (by100 blast)
      ultimately have "\<pi> (invgF x) \<in> ?H" by (by100 simp)
      thus "invgF x \<in> ?H'" using hixF by (by100 blast)
    next
      fix x y z assume "x \<in> ?H'" "y \<in> ?H'" "z \<in> ?H'"
      thus "mulF (mulF x y) z = mulF x (mulF y z)"
        using hF_grp unfolding top1_is_group_on_def by (by100 auto)
    next
      fix x assume "x \<in> ?H'" thus "mulF eF x = x"
        using hF_grp unfolding top1_is_group_on_def by (by100 auto)
    next
      fix x assume "x \<in> ?H'" thus "mulF x eF = x"
        using hF_grp unfolding top1_is_group_on_def by (by100 auto)
    next
      fix x assume "x \<in> ?H'" thus "mulF (invgF x) x = eF"
        using hF_grp unfolding top1_is_group_on_def by (by100 auto)
    next
      fix x assume "x \<in> ?H'" thus "mulF x (invgF x) = eF"
        using hF_grp unfolding top1_is_group_on_def by (by100 auto)
    qed
    have "top1_subgroup_generated_on F mulF eF invgF S \<subseteq> ?H'"
      by (rule subgroup_generated_minimal[OF hS_in_H' hH'_sub hH'_grp])
    hence "F \<subseteq> ?H'" using hF_gen by (by100 simp)
    hence "f \<in> ?H'" using hf(1) by (by100 blast)
    thus "g \<in> ?H" using hf(2) by (by100 blast)
  qed
qed

text \<open>Helper: group with commutator relators covering all pairs is abelian.
  Book: Corollary 73.2 — "αβα⁻¹β⁻¹ = 1 means αβ = βα, so the group is abelian."\<close>
lemma presented_by_commutators_abelian:
  assumes hpres: "top1_group_presented_by_on G mul e invg S R"
    and hcovers: "\<forall>s1\<in>S. \<forall>s2\<in>S. s1 \<noteq> s2 \<longrightarrow>
        (\<exists>w\<in>R. w = [(s1, True), (s2, True), (s1, False), (s2, False)]
              \<or> w = [(s2, True), (s1, True), (s2, False), (s1, False)])"
  shows "top1_is_abelian_group_on G mul e invg"
proof -
  \<comment> \<open>Extract free group F, gen map \<iota>, projection \<pi>.\<close>
  have hG_grp: "top1_is_group_on G mul e invg"
    using hpres unfolding top1_group_presented_by_on_def by (by100 blast)
  from hpres obtain F :: "int set" and mulF eF invgF and \<iota> :: "'b \<Rightarrow> int" and \<pi> where
    hF_free: "top1_is_free_group_full_on F mulF eF invgF \<iota> S" and
    hpi_hom: "top1_group_hom_on F mulF G mul \<pi>" and
    hpi_surj: "\<pi> ` F = G" and
    hpi_ker: "top1_group_kernel_on F e \<pi> = top1_normal_subgroup_generated_on F mulF eF invgF
        {r. \<exists>w\<in>R. r = top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w)}"
    unfolding top1_group_presented_by_on_def by (by5000 auto)
  \<comment> \<open>Each relator w \<in> R maps to commutator \<iota>(s1)\<iota>(s2)\<iota>(s1)\<inverse>\<iota>(s2)\<inverse> in F.
     Under \<pi>: \<pi>(\<iota>(s1))\<pi>(\<iota>(s2))\<pi>(\<iota>(s1))\<inverse>\<pi>(\<iota>(s2))\<inverse> = e in G.
     So \<pi>(\<iota>(s1)) and \<pi>(\<iota>(s2)) commute in G for all s1,s2 \<in> S.\<close>
  \<comment> \<open>Since \<pi>(\<iota>(S)) generates G (via \<pi> surjective), all elements commute.\<close>
  \<comment> \<open>Key: each relator gives π(ι(s1))π(ι(s2))π(ι(s1))⁻¹π(ι(s2))⁻¹ = e in G,
     i.e., generators π(ι(s1)) and π(ι(s2)) commute.
     If all generator pairs commute, G is abelian.\<close>
  \<comment> \<open>Step 1: relators in ker(π) \<Rightarrow> generators commute in G.\<close>
  have hgens_commute: "\<forall>w\<in>R. \<forall>s1\<in>S. \<forall>s2\<in>S.
      w = [(s1, True), (s2, True), (s1, False), (s2, False)] \<longrightarrow>
      mul (\<pi> (\<iota> s1)) (\<pi> (\<iota> s2)) = mul (\<pi> (\<iota> s2)) (\<pi> (\<iota> s1))"
  proof (intro ballI impI)
    fix w s1 s2
    assume hw: "w \<in> R" and hs1: "s1 \<in> S" and hs2: "s2 \<in> S"
      and heq: "w = [(s1, True), (s2, True), (s1, False), (s2, False)]"
    \<comment> \<open>The word product of w in F is \<iota>(s1)\<cdot>\<iota>(s2)\<cdot>\<iota>(s1)\<inverse>\<cdot>\<iota>(s2)\<inverse>.\<close>
    let ?r = "top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w)"
    have "?r \<in> {r. \<exists>w'\<in>R. r = top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w')}"
      using hw by (by100 blast)
    hence "?r \<in> top1_normal_subgroup_generated_on F mulF eF invgF
        {r. \<exists>w'\<in>R. r = top1_group_word_product mulF eF invgF (map (\<lambda>(s,b). (\<iota> s, b)) w')}"
      unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
    hence "?r \<in> top1_group_kernel_on F e \<pi>" using hpi_ker by (by100 simp)
    hence hr_in_ker: "\<pi> ?r = e"
      unfolding top1_group_kernel_on_def by (by100 blast)
    \<comment> \<open>Expand: ?r = word\_product of [(s1,T),(s2,T),(s1,F),(s2,F)] under \<iota>.
       = mulF(\<iota> s1, mulF(\<iota> s2, mulF(invgF(\<iota> s1), invgF(\<iota> s2)))).
       \<pi>(?r) = mul(\<pi>(\<iota> s1), mul(\<pi>(\<iota> s2), mul(invg(\<pi>(\<iota> s1)), invg(\<pi>(\<iota> s2))))) = e.\<close>
    have hr_expand: "?r = mulF (\<iota> s1) (mulF (\<iota> s2) (mulF (invgF (\<iota> s1)) (invgF (\<iota> s2))))"
    proof -
      have "map (\<lambda>(s,b). (\<iota> s, b)) w = [(\<iota> s1, True), (\<iota> s2, True), (\<iota> s1, False), (\<iota> s2, False)]"
        unfolding heq by (by100 simp)
      hence "?r = top1_group_word_product mulF eF invgF
          [(\<iota> s1, True), (\<iota> s2, True), (\<iota> s1, False), (\<iota> s2, False)]"
        by (by100 simp)
      also have "\<dots> = mulF (\<iota> s1) (top1_group_word_product mulF eF invgF
          [(\<iota> s2, True), (\<iota> s1, False), (\<iota> s2, False)])"
        by (by100 simp)
      also have "\<dots> = mulF (\<iota> s1) (mulF (\<iota> s2) (top1_group_word_product mulF eF invgF
          [(\<iota> s1, False), (\<iota> s2, False)]))"
        by (by100 simp)
      also have "\<dots> = mulF (\<iota> s1) (mulF (\<iota> s2) (mulF (invgF (\<iota> s1))
          (top1_group_word_product mulF eF invgF [(\<iota> s2, False)])))"
        by (by100 simp)
      also have "\<dots> = mulF (\<iota> s1) (mulF (\<iota> s2) (mulF (invgF (\<iota> s1))
          (mulF (invgF (\<iota> s2)) eF)))"
        by (by100 simp)
      also have "\<dots> = mulF (\<iota> s1) (mulF (\<iota> s2) (mulF (invgF (\<iota> s1)) (invgF (\<iota> s2))))"
      proof -
        have "invgF (\<iota> s2) \<in> F"
          using hF_free hs2 unfolding top1_is_free_group_full_on_def top1_is_group_on_def
          by (by5000 blast)
        hence "mulF (invgF (\<iota> s2)) eF = invgF (\<iota> s2)"
          using hF_free unfolding top1_is_free_group_full_on_def top1_is_group_on_def
          by (by5000 blast)
        thus ?thesis by (by100 simp)
      qed
      finally show ?thesis .
    qed
    let ?a = "\<pi> (\<iota> s1)" and ?b = "\<pi> (\<iota> s2)"
    have hF_grp: "top1_is_group_on F mulF eF invgF"
      using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
    have hs1F: "\<iota> s1 \<in> F" using hF_free hs1 unfolding top1_is_free_group_full_on_def
      by (by100 blast)
    have hs2F: "\<iota> s2 \<in> F" using hF_free hs2 unfolding top1_is_free_group_full_on_def
      by (by100 blast)
    have haG: "?a \<in> G" using hpi_hom hs1F unfolding top1_group_hom_on_def by (by100 blast)
    have hbG: "?b \<in> G" using hpi_hom hs2F unfolding top1_group_hom_on_def by (by100 blast)
    have hpi_r_eq: "\<pi> ?r = mul ?a (mul ?b (mul (invg ?a) (invg ?b)))"
    proof -
      have hpi_mul: "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> \<pi> (mulF x y) = mul (\<pi> x) (\<pi> y)"
        using hpi_hom unfolding top1_group_hom_on_def by (by100 blast)
      have hinvF1: "invgF (\<iota> s1) \<in> F"
        using hF_grp hs1F unfolding top1_is_group_on_def by (by100 blast)
      have hinvF2: "invgF (\<iota> s2) \<in> F"
        using hF_grp hs2F unfolding top1_is_group_on_def by (by100 blast)
      have hpi_inv1: "\<pi> (invgF (\<iota> s1)) = invg (\<pi> (\<iota> s1))"
        using hom_preserves_inv[OF hF_grp hG_grp hpi_hom hs1F] by (by100 blast)
      have hpi_inv2: "\<pi> (invgF (\<iota> s2)) = invg (\<pi> (\<iota> s2))"
        using hom_preserves_inv[OF hF_grp hG_grp hpi_hom hs2F] by (by100 blast)
      have hmulF_cl: "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> mulF x y \<in> F"
        using hF_grp unfolding top1_is_group_on_def by (by100 blast)
      show ?thesis unfolding hr_expand
        using hpi_mul[OF hs1F] hpi_mul[OF hs2F] hpi_mul[OF hinvF1 hinvF2]
              hpi_mul hmulF_cl hs1F hs2F hinvF1 hinvF2 hpi_inv1 hpi_inv2
        by (by5000 metis)
    qed
    hence "mul ?a (mul ?b (mul (invg ?a) (invg ?b))) = e" using hr_in_ker by (by100 simp)
    show "mul ?a ?b = mul ?b ?a"
    proof -
      have hmul_cl: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hinv_cl: "\<forall>x\<in>G. invg x \<in> G"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hassoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hinv_r: "\<forall>x\<in>G. mul x (invg x) = e"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hinv_l: "\<forall>x\<in>G. mul (invg x) x = e"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hid_r: "\<forall>x\<in>G. mul x e = x"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hid_l: "\<forall>x\<in>G. mul e x = x"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      note hcomm_e = \<open>mul ?a (mul ?b (mul (invg ?a) (invg ?b))) = e\<close>
      have hiaG: "invg ?a \<in> G" using hinv_cl haG by (by100 blast)
      have hibG: "invg ?b \<in> G" using hinv_cl hbG by (by100 blast)
      \<comment> \<open>Multiply on right by b: aba\<inverse>b\<inverse>b = b, i.e. aba\<inverse> = b... no.
         Actually: from aba\<inverse>b\<inverse> = e, multiply on RIGHT by (ba):
         aba\<inverse>b\<inverse>(ba) = ba. LHS = ab(a\<inverse>(b\<inverse>(ba))) = ab(a\<inverse>(e·a))...
         Simpler: aba\<inverse>b\<inverse> = e \<Rightarrow> ab = (aba\<inverse>b\<inverse>)\<inverse>\<inverse> ...
         Just: aba\<inverse>b\<inverse> = e \<Rightarrow> ab = (b\<inverse>)\<inverse>(a\<inverse>)\<inverse> = ba. Wait, that's not right.
         aba\<inverse>b\<inverse> = e \<Rightarrow> ab = (a\<inverse>b\<inverse>)\<inverse> = ba. No.
         aba\<inverse>b\<inverse> = e. Multiply right by b: aba\<inverse> = b. Multiply right by a: ab = ba. \<close>
      \<comment> \<open>Step 1: aba\<inverse>b\<inverse> = e \<Rightarrow> aba\<inverse>b\<inverse>b = eb = b \<Rightarrow> aba\<inverse> = b.\<close>
      have h1: "mul (mul ?a (mul ?b (mul (invg ?a) (invg ?b)))) ?b = mul e ?b"
        using hcomm_e by (by100 simp)
      have habG: "mul ?a ?b \<in> G" using hmul_cl haG hbG by (by100 blast)
      have "mul (mul ?a (mul ?b (mul (invg ?a) (invg ?b)))) ?b
          = mul ?a (mul ?b (mul (invg ?a) (mul (invg ?b) ?b)))"
        using hassoc haG hbG hiaG hibG hmul_cl by (by5000 metis)
      also have "mul (invg ?b) ?b = e" using hinv_l hbG by (by100 blast)
      finally have "mul ?a (mul ?b (mul (invg ?a) e)) = ?b"
        using h1 hid_l hbG by (by5000 metis)
      hence h2: "mul ?a (mul ?b (invg ?a)) = ?b"
        using hid_r hiaG by (by5000 metis)
      \<comment> \<open>Step 2: aba\<inverse> = b \<Rightarrow> aba\<inverse>a = ba \<Rightarrow> ab = ba.\<close>
      have "mul (mul ?a (mul ?b (invg ?a))) ?a = mul ?b ?a"
        using h2 by (by100 simp)
      have "mul ?a (mul ?b (mul (invg ?a) ?a)) = mul ?b ?a"
        using \<open>mul (mul ?a (mul ?b (invg ?a))) ?a = mul ?b ?a\<close>
              hassoc haG hbG hiaG hmul_cl by (by5000 metis)
      hence "mul ?a (mul ?b e) = mul ?b ?a"
        using hinv_l haG by (by5000 metis)
      thus ?thesis using hid_r hbG by (by5000 metis)
    qed
  qed
  \<comment> \<open>Step 2: Derive ALL generator pairs commute from hcovers + hgens\_commute.\<close>
  have hall_commute: "\<forall>s1\<in>S. \<forall>s2\<in>S.
      mul (\<pi> (\<iota> s1)) (\<pi> (\<iota> s2)) = mul (\<pi> (\<iota> s2)) (\<pi> (\<iota> s1))"
  proof (intro ballI)
    fix s1 s2 assume hs1: "s1 \<in> S" and hs2: "s2 \<in> S"
    show "mul (\<pi> (\<iota> s1)) (\<pi> (\<iota> s2)) = mul (\<pi> (\<iota> s2)) (\<pi> (\<iota> s1))"
    proof (cases "s1 = s2")
      case True thus ?thesis by (by100 simp)
    next
      case False
      from hcovers hs1 hs2 False obtain w where hw: "w \<in> R" and
        hdisj: "w = [(s1, True), (s2, True), (s1, False), (s2, False)]
              \<or> w = [(s2, True), (s1, True), (s2, False), (s1, False)]"
        by (by100 blast)
      from hdisj show ?thesis
      proof
        assume "w = [(s1, True), (s2, True), (s1, False), (s2, False)]"
        thus ?thesis using hgens_commute hw hs1 hs2 by (by100 blast)
      next
        assume hw2: "w = [(s2, True), (s1, True), (s2, False), (s1, False)]"
        \<comment> \<open>This is commutator(s2,s1). Apply hgens\_commute with s1'=s2, s2'=s1.\<close>
        have "mul (\<pi> (\<iota> s2)) (\<pi> (\<iota> s1)) = mul (\<pi> (\<iota> s1)) (\<pi> (\<iota> s2))"
          using hgens_commute hw hs1 hs2 hw2 by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
    qed
  qed
  \<comment> \<open>Step 3: G is generated by generator images \<pi>(\<iota>(S)).\<close>
  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  have h\<iota>_sub: "\<iota> ` S \<subseteq> F"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hF_gen: "F = top1_subgroup_generated_on F mulF eF invgF (\<iota> ` S)"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?gens = "(\<lambda>s. \<pi> (\<iota> s)) ` S"
  have hgens_eq: "?gens = \<pi> ` (\<iota> ` S)" by (by100 auto)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg ?gens"
    using surjective_hom_preserves_generation[OF hF_grp hG_grp hF_gen hpi_hom hpi_surj h\<iota>_sub]
    unfolding hgens_eq by (by100 blast)
  \<comment> \<open>Step 4: Centralizer argument. Each generator commutes with all of G.\<close>
  have hgens_sub_G: "?gens \<subseteq> G"
    using hpi_hom h\<iota>_sub unfolding top1_group_hom_on_def by (by100 blast)
  have hgens_central: "\<forall>s\<in>S. \<forall>g\<in>G. mul (\<pi> (\<iota> s)) g = mul g (\<pi> (\<iota> s))"
  proof (intro ballI)
    fix s g assume hs: "s \<in> S" and hg: "g \<in> G"
    let ?a = "\<pi> (\<iota> s)"
    have haG: "?a \<in> G" using hgens_sub_G hs by (by100 blast)
    let ?C = "{h \<in> G. mul ?a h = mul h ?a}"
    have hC_grp: "top1_is_group_on ?C mul e invg"
      by (rule centralizer_is_subgroup[OF hG_grp haG])
    have hC_sub: "?C \<subseteq> G" by (by100 blast)
    have hgens_in_C: "?gens \<subseteq> ?C"
    proof
      fix x assume "x \<in> ?gens"
      then obtain s' where hs': "s' \<in> S" and hx: "x = \<pi> (\<iota> s')" by (by100 blast)
      have hxG: "x \<in> G" using hgens_sub_G \<open>x \<in> ?gens\<close> by (by100 blast)
      have "mul ?a x = mul x ?a"
        using hall_commute hs hs' unfolding hx by (by100 blast)
      thus "x \<in> ?C" using hxG by (by100 blast)
    qed
    have "top1_subgroup_generated_on G mul e invg ?gens \<subseteq> ?C"
      by (rule subgroup_generated_minimal[OF hgens_in_C hC_sub hC_grp])
    hence "G \<subseteq> ?C" using hG_gen by (by100 simp)
    thus "mul ?a g = mul g ?a" using hg by (by100 blast)
  qed
  \<comment> \<open>Step 5: For any x \<in> G, the centralizer C(x) contains all generators, hence G. So G is abelian.\<close>
  show ?thesis unfolding top1_is_abelian_group_on_def
  proof (intro conjI ballI)
    show "top1_is_group_on G mul e invg" by (rule hG_grp)
  next
    fix x y assume hx: "x \<in> G" and hy: "y \<in> G"
    let ?C = "{h \<in> G. mul x h = mul h x}"
    have hC_grp: "top1_is_group_on ?C mul e invg"
      by (rule centralizer_is_subgroup[OF hG_grp hx])
    have hC_sub: "?C \<subseteq> G" by (by100 blast)
    have hgens_in_C: "?gens \<subseteq> ?C"
    proof
      fix g assume "g \<in> ?gens"
      then obtain s where hs: "s \<in> S" and hg: "g = \<pi> (\<iota> s)" by (by100 blast)
      have hgG: "g \<in> G" using hgens_sub_G \<open>g \<in> ?gens\<close> by (by100 blast)
      have "mul x g = mul g x"
        using hgens_central hs hx unfolding hg by (by5000 metis)
      thus "g \<in> ?C" using hgG by (by100 blast)
    qed
    have "top1_subgroup_generated_on G mul e invg ?gens \<subseteq> ?C"
      by (rule subgroup_generated_minimal[OF hgens_in_C hC_sub hC_grp])
    hence "G \<subseteq> ?C" using hG_gen by (by100 simp)
    thus "mul x y = mul y x" using hy by (by100 blast)
  qed
qed

text \<open>Helper: abelian group has trivial commutator subgroup.\<close>
lemma abelian_commutator_trivial:
  assumes hG: "top1_is_group_on G mul e invg"
    and hab: "top1_is_abelian_group_on G mul e invg"
  shows "top1_commutator_subgroup_on G mul e invg = {e}"
proof -
  \<comment> \<open>Use Lemma\_69\_3 with h = id: G \<rightarrow> G. Since G is abelian, [G,G] \<subseteq> ker(id) = {e}.\<close>
  have hid_hom: "top1_group_hom_on G mul G mul id"
    using group_hom_id[OF hG] by (by100 blast)
  have hcomm_sub_ker: "top1_commutator_subgroup_on G mul e invg
      \<subseteq> top1_group_kernel_on G e id"
    using Lemma_69_3_commutator_in_kernel[OF hG hab hid_hom] by (by100 blast)
  have he_in_G: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
  have hker_id: "top1_group_kernel_on G e id = {e}"
    unfolding top1_group_kernel_on_def using he_in_G by (by100 auto)
  have hcomm_sub_e: "top1_commutator_subgroup_on G mul e invg \<subseteq> {e}"
    using hcomm_sub_ker hker_id by (by100 blast)
  \<comment> \<open>Also e \<in> [G,G] (identity in any subgroup).\<close>
  have he_in_comm: "e \<in> top1_commutator_subgroup_on G mul e invg"
  proof -
    have he_in_G: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
    have "top1_group_commutator_on mul invg e e = e"
      unfolding top1_group_commutator_on_def
      using hG he_in_G unfolding top1_is_group_on_def by (by5000 metis)
    hence "e \<in> {top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G}"
      using he_in_G by (by5000 force)
    have hcomm_set_sub: "{top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G} \<subseteq> G"
    proof
      fix x assume "x \<in> {top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G}"
      then obtain a b where "a \<in> G" "b \<in> G" "x = top1_group_commutator_on mul invg a b"
        by (by100 blast)
      thus "x \<in> G" unfolding top1_group_commutator_on_def
        using hG \<open>a \<in> G\<close> \<open>b \<in> G\<close> unfolding top1_is_group_on_def by (by5000 metis)
    qed
    thus ?thesis unfolding top1_commutator_subgroup_on_def
      using subgroup_generated_contains[OF hG hcomm_set_sub]
      \<open>e \<in> {top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G}\<close>
      by (by100 blast)
  qed
  show ?thesis using hcomm_sub_e he_in_comm by (by100 blast)
qed

text \<open>Helper: trivial kernel implies injective for group hom.\<close>
lemma trivial_kernel_injective:
  assumes hG: "top1_is_group_on G mulG eG invgG"
    and hH: "top1_is_group_on H mulH eH invgH"
    and hf: "top1_group_hom_on G mulG H mulH f"
    and hker: "top1_group_kernel_on G eH f = {eG}"
  shows "inj_on f G"
proof (rule inj_onI)
  fix x y assume hx: "x \<in> G" and hy: "y \<in> G" and heq: "f x = f y"
  \<comment> \<open>x * y\<inverse> \<in> ker(f) = {eG}.\<close>
  have hinvy: "invgG y \<in> G" using hG hy unfolding top1_is_group_on_def by (by100 blast)
  have hxy: "mulG x (invgG y) \<in> G"
    using hG hx hinvy unfolding top1_is_group_on_def by (by100 blast)
  have "f (mulG x (invgG y)) = mulH (f x) (f (invgG y))"
    using hf hx hinvy unfolding top1_group_hom_on_def by (by100 blast)
  also have "f (invgG y) = invgH (f y)"
    using hom_preserves_inv[OF hG hH hf hy] by (by100 blast)
  also have "mulH (f x) (invgH (f y)) = mulH (f x) (invgH (f x))"
    using heq by (by100 simp)
  also have "\<dots> = eH"
  proof -
    have "f x \<in> H" using hf hx unfolding top1_group_hom_on_def by (by100 blast)
    thus ?thesis using hH unfolding top1_is_group_on_def by (by100 blast)
  qed
  finally have "f (mulG x (invgG y)) = eH" .
  hence "mulG x (invgG y) \<in> top1_group_kernel_on G eH f"
    using hxy unfolding top1_group_kernel_on_def by (by100 blast)
  hence "mulG x (invgG y) = eG" using hker by (by100 blast)
  \<comment> \<open>x * y\<inverse> = eG \<Rightarrow> x = y.\<close>
  hence "mulG (mulG x (invgG y)) y = mulG eG y" by (by100 simp)
  hence "mulG x (mulG (invgG y) y) = y"
    using hG hx hinvy hy unfolding top1_is_group_on_def by (by5000 metis)
  hence "mulG x eG = y"
    using hG hy unfolding top1_is_group_on_def by (by5000 metis)
  thus "x = y" using hG hx unfolding top1_is_group_on_def by (by5000 metis)
qed

\<comment> \<open>free\_abelian\_2\_iso\_ZZ no longer needed: Theorem\_73\_2 uses free\_abelian\_invariant\_under\_iso directly.\<close>

(** from \<S>73 Theorem 73.1: \<pi>_1(torus) has presentation <\<alpha>, \<beta> | \<alpha>\<beta>\<alpha>^{-1}\<beta>^{-1}>,
    i.e. is isomorphic to the free abelian group Z \<times> Z on 2 generators. **)
text \<open>Corollary 73.2: The fundamental group of the torus is a free abelian group of rank 2.\<close>
theorem Theorem_73_2_torus_free_abelian:
  fixes T_torus :: "'a set" and TT :: "'a set set" and x0 :: 'a
  assumes "top1_is_torus_on T_torus TT"
      and "x0 \<in> T_torus"
  shows "\<exists>(H :: (real \<Rightarrow> 'a) set set set set) mulH eH invgH iotaH phi.
    top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set) \<and>
    top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
proof -
  \<comment> \<open>Route via Theorem\_75\_3: H\_1(T) free abelian on 2 generators.
     Since torus has commutator relator, \<pi>\_1(T) is abelian, so \<pi>\_1 = H\_1 = Z\<times>Z.\<close>
  \<comment> \<open>Step 1: T = 1-fold torus.\<close>
  have h1fold: "top1_is_n_fold_torus_on T_torus TT 1"
    using assms(1) unfolding top1_is_torus_on_def by (by100 blast)
  \<comment> \<open>Step 2: Theorem\_75\_3 gives H\_1(T) free abelian on {..<2}.\<close>
  note hThm753 = Theorem_75_3_H1_n_torus[OF h1fold assms(2)]
  from hThm753 obtain H :: "(real \<Rightarrow> 'a) set set set set"
    and mulH eH invgH iota_S phi where
    habel: "top1_is_abelianization_of H mulH eH invgH
        (top1_fundamental_group_carrier T_torus TT x0)
        (top1_fundamental_group_mul T_torus TT x0)
        (top1_fundamental_group_id T_torus TT x0)
        (top1_fundamental_group_invg T_torus TT x0) phi" and
    hfree_ab: "top1_is_free_abelian_group_full_on H mulH eH invgH iota_S ({..<2}::nat set)"
    by (by5000 auto)
  \<comment> \<open>Step 3: The torus \<pi>\_1 is abelian (commutator relator aba\<inverse>b\<inverse>=1 means ab=ba).
     Therefore the abelianization map phi is an isomorphism.
     Step 4: H\_1(T) free abelian on {0,1} \<cong> Z \<times> Z.
     Step 5: Compose: \<pi>\_1(T) \<cong> H\_1(T) \<cong> Z \<times> Z.\<close>
  \<comment> \<open>Step 3: \<pi>\_1(T) is abelian (from Theorem\_74\_3: commutator relator).
     Therefore ker(phi) = [G,G] = {e}, so phi is injective.\<close>
  have hpi1_abelian: "top1_is_abelian_group_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0)
      (top1_fundamental_group_id T_torus TT x0)
      (top1_fundamental_group_invg T_torus TT x0)"
  proof -
    \<comment> \<open>Theorem\_74\_3 for n=1: \<pi>\_1(T) has presentation \<langle>{0,1} | [(0,T)(1,T)(0,F)(1,F)]\<rangle>.\<close>
    from Theorem_74_3_fund_group_n_torus[OF h1fold assms(2)]
    obtain G :: "(real \<Rightarrow> 'a) set set set" and mulG eG invgG where
      hpres: "top1_group_presented_by_on G mulG eG invgG ({..<2*1}::nat set)
        {concat (map (\<lambda>i. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]) [0..<1])}" and
      hiso_pi1: "top1_groups_isomorphic_on G mulG
        (top1_fundamental_group_carrier T_torus TT x0)
        (top1_fundamental_group_mul T_torus TT x0)"
      by (by5000 auto)
    \<comment> \<open>Every distinct generator pair has a commutator relator (or its reverse).\<close>
    have hcovers: "\<forall>s1\<in>{..<2*1::nat}. \<forall>s2\<in>{..<2*1::nat}. s1 \<noteq> s2 \<longrightarrow>
        (\<exists>w\<in>{concat (map (\<lambda>i. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]) [0..<1])}.
            w = [(s1, True), (s2, True), (s1, False), (s2, False)]
          \<or> w = [(s2, True), (s1, True), (s2, False), (s1, False)])"
      by (by5000 auto)
    \<comment> \<open>So G is abelian by presented\_by\_commutators\_abelian.\<close>
    have hG_abelian: "top1_is_abelian_group_on G mulG eG invgG"
      using presented_by_commutators_abelian[OF hpres hcovers] by (by100 blast)
    \<comment> \<open>Transfer: G abelian + G \<cong> \<pi>\_1(T) \<Rightarrow> \<pi>\_1(T) abelian.\<close>
    \<comment> \<open>Iso preserves abelian: G abelian + G \<cong> H \<Rightarrow> H abelian.\<close>
    from hiso_pi1 obtain f where hf_iso: "top1_group_iso_on G mulG
        (top1_fundamental_group_carrier T_torus TT x0)
        (top1_fundamental_group_mul T_torus TT x0) f"
      unfolding top1_groups_isomorphic_on_def by (by100 blast)
    show ?thesis unfolding top1_is_abelian_group_on_def
    proof (intro conjI ballI)
      have hTT: "is_topology_on T_torus TT"
      proof -
        have "top1_quotient_of_scheme_on T_torus TT (top1_n_torus_scheme 1)"
          using h1fold unfolding top1_is_n_fold_torus_on_def by (by100 blast)
        hence "is_topology_on_strict T_torus TT"
          unfolding top1_quotient_of_scheme_on_def by (by100 blast)
        thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
      qed
      have hpi1_grp: "top1_is_group_on
          (top1_fundamental_group_carrier T_torus TT x0)
          (top1_fundamental_group_mul T_torus TT x0)
          (top1_fundamental_group_id T_torus TT x0)
          (top1_fundamental_group_invg T_torus TT x0)"
        using top1_fundamental_group_is_group[OF hTT assms(2)] by (by100 blast)
      show "top1_is_group_on
          (top1_fundamental_group_carrier T_torus TT x0)
          (top1_fundamental_group_mul T_torus TT x0)
          (top1_fundamental_group_id T_torus TT x0)
          (top1_fundamental_group_invg T_torus TT x0)"
        by (rule hpi1_grp)
    next
      fix x y
      assume hx: "x \<in> top1_fundamental_group_carrier T_torus TT x0"
         and hy: "y \<in> top1_fundamental_group_carrier T_torus TT x0"
      show "top1_fundamental_group_mul T_torus TT x0 x y =
            top1_fundamental_group_mul T_torus TT x0 y x"
      proof -
        let ?pi1 = "top1_fundamental_group_carrier T_torus TT x0"
        let ?mulpi = "top1_fundamental_group_mul T_torus TT x0"
        have hf_bij: "bij_betw f G ?pi1"
          using hf_iso unfolding top1_group_iso_on_def by (by100 blast)
        have hf_hom: "top1_group_hom_on G mulG ?pi1 ?mulpi f"
          using hf_iso unfolding top1_group_iso_on_def by (by100 blast)
        have hf_surj: "f ` G = ?pi1" using hf_bij unfolding bij_betw_def by (by100 blast)
        have "x \<in> f ` G" using hf_surj hx by (by100 blast)
        then obtain a where "a \<in> G" "f a = x" by (by100 blast)
        have "y \<in> f ` G" using hf_surj hy by (by100 blast)
        then obtain b where "b \<in> G" "f b = y" by (by100 blast)
        have "?mulpi x y = ?mulpi (f a) (f b)" using \<open>f a = x\<close> \<open>f b = y\<close> by (by100 simp)
        also have "\<dots> = f (mulG a b)"
          using hf_hom \<open>a \<in> G\<close> \<open>b \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
        also have "mulG a b = mulG b a"
          using hG_abelian \<open>a \<in> G\<close> \<open>b \<in> G\<close> unfolding top1_is_abelian_group_on_def by (by100 blast)
        also have "f (mulG b a) = ?mulpi (f b) (f a)"
          using hf_hom \<open>a \<in> G\<close> \<open>b \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
        also have "\<dots> = ?mulpi y x" using \<open>f a = x\<close> \<open>f b = y\<close> by (by100 simp)
        finally show ?thesis .
      qed
    qed
  qed
  \<comment> \<open>Step 4: phi bijective (abelian \<Rightarrow> ker = {e} \<Rightarrow> injective + surjective = bijective).\<close>
  have hphi_bij: "bij_betw phi
      (top1_fundamental_group_carrier T_torus TT x0) H"
  proof -
    let ?G = "top1_fundamental_group_carrier T_torus TT x0"
    let ?mulG = "top1_fundamental_group_mul T_torus TT x0"
    let ?eG = "top1_fundamental_group_id T_torus TT x0"
    let ?invG = "top1_fundamental_group_invg T_torus TT x0"
    \<comment> \<open>phi is surjective.\<close>
    have hsurj: "phi ` ?G = H"
      using habel unfolding top1_is_abelianization_of_def by (by100 blast)
    \<comment> \<open>ker(phi) = [G,G] = {eG} since G is abelian.\<close>
    have hker: "top1_group_kernel_on ?G eH phi = top1_commutator_subgroup_on ?G ?mulG ?eG ?invG"
      using habel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hG_grp: "top1_is_group_on ?G ?mulG ?eG ?invG"
      using habel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hcomm_trivial: "top1_commutator_subgroup_on ?G ?mulG ?eG ?invG = {?eG}"
      using abelian_commutator_trivial[OF hG_grp hpi1_abelian] by (by100 blast)
    have hker_trivial: "top1_group_kernel_on ?G eH phi = {?eG}"
      using hker hcomm_trivial by (by100 simp)
    \<comment> \<open>Trivial kernel + surjective = bijective.\<close>
    have hH_grp: "top1_is_group_on H mulH eH invgH"
      using habel unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def by (by100 blast)
    have hphi_hom: "top1_group_hom_on ?G ?mulG H mulH phi"
      using habel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hinj: "inj_on phi ?G"
      using trivial_kernel_injective[OF hG_grp hH_grp hphi_hom hker_trivial] by (by100 blast)
    show ?thesis unfolding bij_betw_def using hinj hsurj by (by100 blast)
  qed
  \<comment> \<open>Step 5: phi is a group iso \<pi>\_1(T) \<rightarrow> H.\<close>
  have hphi_iso: "top1_group_iso_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) H mulH phi"
    unfolding top1_group_iso_on_def using habel hphi_bij
    unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Step 6: phi\<inverse>: H \<rightarrow> \<pi>\_1(T) is also an iso.\<close>
  have hphi_inv_iso: "top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) (inv_into (top1_fundamental_group_carrier T_torus TT x0) phi)"
  proof -
    have hG_grp: "top1_is_group_on
        (top1_fundamental_group_carrier T_torus TT x0)
        (top1_fundamental_group_mul T_torus TT x0)
        (top1_fundamental_group_id T_torus TT x0)
        (top1_fundamental_group_invg T_torus TT x0)"
      using habel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hH_grp: "top1_is_group_on H mulH eH invgH"
      using habel unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def by (by100 blast)
    show ?thesis using group_iso_on_inverse[OF hphi_iso hG_grp hH_grp] by (by100 blast)
  qed
  \<comment> \<open>Step 7: Package result.\<close>
  have "\<exists>phi. top1_is_free_abelian_group_full_on H mulH eH invgH iota_S ({..<2}::nat set)
    \<and> top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    using hfree_ab hphi_inv_iso by (by100 blast)
  hence "\<exists>iotaH phi. top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set)
    \<and> top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    by (by100 blast)
  hence "\<exists>invgH iotaH phi. top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set)
    \<and> top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    by (by100 blast)
  hence "\<exists>eH invgH iotaH phi. top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set)
    \<and> top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    by (by100 blast)
  hence "\<exists>mulH eH invgH iotaH phi. top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set)
    \<and> top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    by (by100 blast)
  hence "\<exists>(H :: (real \<Rightarrow> 'a) set set set set) mulH eH invgH iotaH phi.
    top1_is_free_abelian_group_full_on H mulH eH invgH iotaH ({..<2}::nat set) \<and>
    top1_group_iso_on H mulH
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0) phi"
    by (by100 blast)
  thus ?thesis .
qed

(** from \<S>73 Theorem 73.4: the n-fold dunce cap has fundamental group Z/nZ.
    Book proof (Munkres): Let h = quotient map, A = h(S¹), a = h(1,0).
    h maps arc C from p=(1,0) to r(p) onto A, injective except at endpoints.
    So A \<cong> S¹. The loop f that generates \<pi>_1(S¹,p) maps to \<alpha>^n under h.
    By Theorem 72.1: \<pi>_1(X,a) \<cong> \<pi>_1(A,a)/\<langle>\<langle>\<alpha>^n\<rangle>\<rangle> = Z/nZ. **)
theorem Theorem_73_4_dunce_cap:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "n > 0"
      and "top1_is_dunce_cap_on X TX n"
      and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_Zn_group n)
           (top1_Zn_mul n)
       \<and> (\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<1}::nat set)
             { replicate n (0::nat, True) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0))"
proof -
  \<comment> \<open>Step 0: Extract quotient map q from dunce cap definition.\<close>
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
  have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  have hX_strict: "is_topology_on_strict X TX"
    using assms(2) unfolding top1_is_dunce_cap_on_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hq_surj: "q ` top1_B2 = X"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  \<comment> \<open>Step 1: Set base point a = q(1,0) \<in> A = q(S¹). Following the book proof.\<close>
  let ?a = "q (1::real, 0::real)"
  have h10_S1: "(1::real, 0::real) \<in> top1_S1"
    unfolding top1_S1_def by (by100 simp)
  have h10_B2: "(1::real, 0::real) \<in> top1_B2"
    unfolding top1_B2_def by (by100 simp)
  have ha_X: "?a \<in> X" using hq_surj h10_B2 by (by100 blast)
  let ?A = "q ` top1_S1"
  have ha_A: "?a \<in> ?A" using h10_S1 by (by100 blast)
  have hA_sub: "?A \<subseteq> X" using hq_surj
  proof -
    have "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
    thus ?thesis using hq_surj by (by100 blast)
  qed
  \<comment> \<open>Step 3: X is Hausdorff. Book proof: (1) q is a closed map (rotation saturation argument),
     then (2) Lemma 73.3: closed quotient of normal space is normal (hence Hausdorff).\<close>
  \<comment> \<open>Step 3a: q is a closed map. For any closed C \<subseteq> B², q\<inverse>(q(C)) = C \<union> \<Union>_{k<n} r^k(C\<inter>S¹).
     Each r^k(C\<inter>S¹) is closed (rotation is continuous on compact S¹). Finite union closed.\<close>
  have hq_closed_map: "top1_closed_map_on top1_B2 top1_B2_topology X TX q"
    unfolding top1_closed_map_on_def
  proof (intro conjI ballI allI impI)
    fix z assume "z \<in> top1_B2" thus "q z \<in> X" using hq_surj by (by100 blast)
  next
    fix C assume hC: "closedin_on top1_B2 top1_B2_topology C"
    \<comment> \<open>Book proof: q(C) is closed iff q\<inverse>(q(C)) is closed in B² (quotient property).
       q\<inverse>(q(C)) = C \<union> \<Union>{r^k(C\<inter>S¹) | k < n}. Each r^k(C\<inter>S¹) is closed.\<close>
    \<comment> \<open>To show q(C) is closed in X: show X - q(C) is open, i.e., X - q(C) \<in> TX.
       By quotient property: {z \<in> B². q z \<in> X - q(C)} \<in> B²_top, i.e., B² - q\<inverse>(q(C)) is open.\<close>
    have hC_sub: "C \<subseteq> top1_B2" using hC unfolding closedin_on_def by (by100 blast)
    \<comment> \<open>Define the saturation: q\<inverse>(q(C)) = {z \<in> B². q z \<in> q ` C}.\<close>
    let ?sat = "{z \<in> top1_B2. q z \<in> q ` C}"
    \<comment> \<open>q\<inverse>(q(C)) \<subseteq> C \<union> \<Union>_{k<n} r^k(C \<inter> S¹).\<close>
    \<comment> \<open>For z \<in> B² with q(z) \<in> q(C): either z \<in> C, or z \<in> S¹ and some c \<in> C \<inter> S¹ with q(z)=q(c).\<close>
    have hsat_closed: "closedin_on top1_B2 top1_B2_topology ?sat"
    proof -
      \<comment> \<open>?sat = C \<union> {z \<in> S¹. \<exists>c \<in> C \<inter> S¹. q z = q c}.\<close>
      \<comment> \<open>The S¹ part = \<Union>_{k<n} r^k(C \<inter> S¹), each r^k(C\<inter>S¹) is closed.\<close>
      let ?C0 = "C \<inter> top1_S1"
      let ?rot = "\<lambda>(k::nat) z. (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
                                 sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z)"
      have hS1_B2: "top1_S1 \<subseteq> top1_B2"
        unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hsat_eq: "?sat = C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
      proof
        \<comment> \<open>Forward: z \<in> sat \<Rightarrow> z \<in> C or z \<in> some rot\_k(C\<inter>S¹).\<close>
        show "?sat \<subseteq> C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
        proof
          fix z assume hz: "z \<in> ?sat"
          hence hzB: "z \<in> top1_B2" and "\<exists>c\<in>C. q z = q c" by (by100 blast)+
          then obtain c where hcC: "c \<in> C" and hqeq: "q z = q c" by (by100 blast)
          have hcB: "c \<in> top1_B2" using hcC hC_sub by (by100 blast)
          show "z \<in> C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
          proof (cases "z \<in> top1_S1")
            case False
            hence hzInt: "z \<in> top1_B2 - top1_S1" using hzB by (by100 blast)
            \<comment> \<open>c must also be in B²-S¹ (if c \<in> S¹, separation gives contradiction).\<close>
            have "c \<notin> top1_S1"
            proof
              assume "c \<in> top1_S1"
              hence "q z \<noteq> q c" using hq_sep hzInt by (by5000 metis)
              thus False using hqeq by (by100 simp)
            qed
            hence "c \<in> top1_B2 - top1_S1" using hcB by (by100 blast)
            hence "z = c" using hq_inj hzInt hqeq unfolding inj_on_def by (by5000 metis)
            thus ?thesis using hcC by (by100 blast)
          next
            case True
            hence hzS1: "z \<in> top1_S1" .
            have "c \<in> top1_S1"
            proof (rule ccontr)
              assume "c \<notin> top1_S1"
              hence "c \<in> top1_B2 - top1_S1" using hcB by (by100 blast)
              hence "q c \<noteq> q z" using hq_sep hzS1 by (by5000 metis)
              thus False using hqeq by (by100 simp)
            qed
            hence hcS1: "c \<in> top1_S1" .
            from hq_S1[rule_format, OF hcS1 hzS1]
            have "q c = q z \<longleftrightarrow>
                (\<exists>k::nat. k < n \<and> z = ?rot k c)" by (by5000 blast)
            hence "\<exists>k<n. z = ?rot k c" using hqeq by (by100 simp)
            then obtain k where "k < n" "z = ?rot k c" by (by100 blast)
            hence "z \<in> ?rot k ` ?C0" using hcC hcS1 by (by100 blast)
            thus ?thesis using \<open>k < n\<close> by (by100 blast)
          qed
        qed
      next
        \<comment> \<open>Backward: C \<union> rot images \<subseteq> sat.\<close>
        show "C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0) \<subseteq> ?sat"
        proof
          fix z assume "z \<in> C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
          thus "z \<in> ?sat"
          proof
            assume "z \<in> C"
            hence "z \<in> top1_B2" using hC_sub by (by100 blast)
            moreover have "q z \<in> q ` C" using \<open>z \<in> C\<close> by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          next
            assume "z \<in> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
            then obtain k c where hk: "k < n" and hcC0: "c \<in> ?C0" and hzeq: "z = ?rot k c"
              by (by100 blast)
            hence hcS1: "c \<in> top1_S1" by (by100 blast)
            have hcC': "c \<in> C" using hcC0 by (by100 blast)
            \<comment> \<open>z = rot\_k(c) \<in> S¹ (rotation preserves S¹).\<close>
            have hzS1: "z \<in> top1_S1"
            proof -
              have "(fst c)^2 + (snd c)^2 = 1" using hcS1 unfolding top1_S1_def by (by100 simp)
              hence "(fst z)^2 + (snd z)^2 = 1"
              proof -
                let ?\<theta> = "2*pi*real k/real n"
                assume h1: "(fst c)^2 + (snd c)^2 = 1"
                have hident: "\<And>co si x y :: real. (co*x - si*y)^2 + (si*x + co*y)^2
                    = (co^2 + si^2) * (x^2 + y^2)"
                  by (simp add: power2_eq_square algebra_simps)
                have "fst z = cos ?\<theta> * fst c - sin ?\<theta> * snd c"
                  unfolding hzeq by (by100 simp)
                moreover have "snd z = sin ?\<theta> * fst c + cos ?\<theta> * snd c"
                  unfolding hzeq by (by100 simp)
                ultimately have "(fst z)^2 + (snd z)^2
                    = (cos ?\<theta> * fst c - sin ?\<theta> * snd c)^2 + (sin ?\<theta> * fst c + cos ?\<theta> * snd c)^2"
                  by (by100 simp)
                also have "\<dots> = ((cos ?\<theta>)^2 + (sin ?\<theta>)^2) * ((fst c)^2 + (snd c)^2)"
                  by (rule hident)
                also have "\<dots> = 1" using sin_cos_squared_add[of ?\<theta>] h1 by (by100 simp)
                finally show ?thesis .
              qed
              thus ?thesis unfolding top1_S1_def by (by100 simp)
            qed
            have hzB: "z \<in> top1_B2" using hzS1 hS1_B2 by (by100 blast)
            \<comment> \<open>q(z) = q(c) by hq\_S1.\<close>
            from hq_S1[rule_format, OF hcS1 hzS1]
            have "q c = q z \<longleftrightarrow>
                (\<exists>j::nat. j < n \<and> z = ?rot j c)" by (by5000 blast)
            hence "q c = q z" using hk hzeq by (by100 blast)
            hence "q z = q c" by (by100 simp)
            moreover have "q c \<in> q ` C" using hcC' by (by100 blast)
            ultimately have "q z \<in> q ` C" by (by100 simp)
            thus ?thesis using hzB by (by100 blast)
          qed
        qed
      qed
      moreover have "closedin_on top1_B2 top1_B2_topology (C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0))"
      proof -
        \<comment> \<open>Each r^k(C\<inter>S¹) is closed: continuous image of compact subset of Hausdorff.\<close>
        have hC0_closed_S1: "closedin_on top1_S1 top1_S1_topology ?C0"
        proof -
          \<comment> \<open>S¹ topology = subspace of B² topology (by transitivity of subspace).\<close>
          have hS1_B2_loc: "top1_S1 \<subseteq> top1_B2"
            unfolding top1_S1_def top1_B2_def by (by100 auto)
          have hS1_eq: "top1_S1_topology = subspace_topology top1_B2 top1_B2_topology top1_S1"
            unfolding top1_B2_topology_def top1_S1_topology_def
            using subspace_topology_trans[OF hS1_B2_loc] by (by100 simp)
          have "is_topology_on top1_B2 top1_B2_topology"
            using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
          from Theorem_17_2[OF this hS1_B2_loc]
          have "closedin_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) ?C0 \<longleftrightarrow>
              (\<exists>D. closedin_on top1_B2 top1_B2_topology D \<and> ?C0 = D \<inter> top1_S1)"
            by (by100 blast)
          hence "closedin_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) ?C0"
            using hC by (by100 blast)
          thus ?thesis using hS1_eq by (by100 simp)
        qed
        have "\<And>k. k < n \<Longrightarrow> closedin_on top1_B2 top1_B2_topology (?rot k ` ?C0)"
        proof -
          fix k :: nat assume hk: "k < n"
          \<comment> \<open>r^k(C\<inter>S¹) \<subseteq> S¹ (rotation maps S¹ to S¹ — proved in saturation equality).\<close>
          have hrot_S1: "?rot k ` top1_S1 \<subseteq> top1_S1"
          proof
            fix z assume "z \<in> ?rot k ` top1_S1"
            then obtain w where hw: "w \<in> top1_S1" and hz: "z = ?rot k w" by (by100 blast)
            have "(fst w)^2 + (snd w)^2 = 1" using hw unfolding top1_S1_def by (by100 simp)
            hence "(fst z)^2 + (snd z)^2 = 1"
            proof -
              let ?\<theta> = "2*pi*real k/real n"
              assume h1: "(fst w)^2 + (snd w)^2 = 1"
              have hident: "\<And>co si x y :: real. (co*x - si*y)^2 + (si*x + co*y)^2
                  = (co^2 + si^2) * (x^2 + y^2)"
                by (simp add: power2_eq_square algebra_simps)
              have "fst z = cos ?\<theta> * fst w - sin ?\<theta> * snd w" unfolding hz by (by100 simp)
              moreover have "snd z = sin ?\<theta> * fst w + cos ?\<theta> * snd w" unfolding hz by (by100 simp)
              ultimately have "(fst z)^2 + (snd z)^2
                  = (cos ?\<theta> * fst w - sin ?\<theta> * snd w)^2 + (sin ?\<theta> * fst w + cos ?\<theta> * snd w)^2"
                by (by100 simp)
              also have "\<dots> = ((cos ?\<theta>)^2 + (sin ?\<theta>)^2) * ((fst w)^2 + (snd w)^2)" by (rule hident)
              also have "\<dots> = 1" using sin_cos_squared_add[of ?\<theta>] h1 by (by100 simp)
              finally show ?thesis .
            qed
            thus "z \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
          qed
          hence hrot_C0_S1: "?rot k ` ?C0 \<subseteq> top1_S1" by (by100 blast)
          \<comment> \<open>r^k is continuous on S¹ (restriction of continuous linear map on R²).\<close>
          have hrot_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?rot k)"
          proof -
            \<comment> \<open>Rotation is continuous on UNIV (linear map = polynomial = continuous).\<close>
            have hrot_cont_R2: "continuous_on UNIV (?rot k)"
              by (intro continuous_intros)
            \<comment> \<open>Rotation maps S¹ to S¹ (proved above).\<close>
            have hrot_maps: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?rot k p \<in> top1_S1"
              using hrot_S1 by (by100 blast)
            \<comment> \<open>By top1_continuous_map_on_real2_subspace: continuous from S¹ to S¹.\<close>
            from top1_continuous_map_on_real2_subspace[OF hrot_maps hrot_cont_R2]
            show ?thesis unfolding top1_S1_topology_def .
          qed
          \<comment> \<open>S¹ is compact and Hausdorff \<Rightarrow> closed map.\<close>
          have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
          proof -
            have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
              using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
            have hR_haus: "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
              using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq .
            have "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
                (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
              using conjunct1[OF conjunct2[OF Theorem_17_11]] hR_haus by (by100 blast)
            hence "is_hausdorff_on (UNIV::(real\<times>real) set)
                (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
            thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]]
              unfolding top1_S1_topology_def by (by100 blast)
          qed
          \<comment> \<open>C\<inter>S¹ is closed in compact S¹, rotation continuous S¹\<rightarrow>Hausdorff S¹ \<Rightarrow> image closed.\<close>
          have "closedin_on top1_S1 top1_S1_topology (?rot k ` ?C0)"
            by (rule compact_hausdorff_continuous_closed_map[OF S1_compact hS1_haus hrot_cont hC0_closed_S1])
          \<comment> \<open>Closed in S¹ + S¹ closed in B² \<Rightarrow> closed in B².\<close>
          thus "closedin_on top1_B2 top1_B2_topology (?rot k ` ?C0)"
          proof -
            assume hcl_S1: "closedin_on top1_S1 top1_S1_topology (?rot k ` ?C0)"
            have hS1_eq: "top1_S1_topology = subspace_topology top1_B2 top1_B2_topology top1_S1"
              unfolding top1_B2_topology_def top1_S1_topology_def
              using subspace_topology_trans[OF hS1_B2] by (by100 simp)
            have hB2_top_l: "is_topology_on top1_B2 top1_B2_topology"
              using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
            from Theorem_17_2[OF hB2_top_l hS1_B2]
            have "closedin_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (?rot k ` ?C0)
                \<longleftrightarrow> (\<exists>D. closedin_on top1_B2 top1_B2_topology D \<and> ?rot k ` ?C0 = D \<inter> top1_S1)"
              by (by100 blast)
            hence "\<exists>D. closedin_on top1_B2 top1_B2_topology D \<and> ?rot k ` ?C0 = D \<inter> top1_S1"
              using hcl_S1 hS1_eq by (by100 simp)
            then obtain D where hD: "closedin_on top1_B2 top1_B2_topology D"
                and hD_eq: "?rot k ` ?C0 = D \<inter> top1_S1" by (by100 blast)
            \<comment> \<open>rot\_k(C\<inter>S¹) = D \<inter> S¹. Since S¹ is closed in B², D \<inter> S¹ is closed in B².\<close>
            have "closedin_on top1_B2 top1_B2_topology (D \<inter> top1_S1)"
            proof -
              have hB2_t: "is_topology_on top1_B2 top1_B2_topology"
                using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
              \<comment> \<open>S¹ is closed in B² (same proof as outer hS1\_closed).\<close>
              have hS1_cl: "closedin_on top1_B2 top1_B2_topology top1_S1"
              proof (rule closedin_intro[OF hS1_B2])
                have hopen_disk: "open {z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}"
                proof -
                  have hcont_nsq: "continuous_on UNIV (\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2)"
                    by (intro continuous_intros)
                  have "open ({..<1::real})" by (by100 simp)
                  hence "open {t::real. t < 1}"
                  proof -
                    have "{..<1::real} = {t. t < 1}" by (by100 auto)
                    thus ?thesis using \<open>open ({..<1::real})\<close> by (by100 simp)
                  qed
                  hence "open ((\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV)"
                    using continuous_on_open_vimage[of "UNIV::(real\<times>real) set"
                          "\<lambda>z. (fst z)^2 + (snd z)^2"] hcont_nsq by (by5000 auto)
                  moreover have "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
                      = (\<lambda>z. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV" by (by100 auto)
                  ultimately show ?thesis by (by100 simp)
                qed
                have "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
                    \<in> product_topology_on top1_open_sets top1_open_sets"
                  using hopen_disk product_topology_on_open_sets_real2 unfolding top1_open_sets_def
                  by (by100 blast)
                moreover have "top1_B2 - top1_S1 = top1_B2 \<inter> {z. (fst z)^2 + (snd z)^2 < 1}"
                  unfolding top1_B2_def top1_S1_def by (by100 auto)
                ultimately show "top1_B2 - top1_S1 \<in> top1_B2_topology"
                  unfolding top1_B2_topology_def subspace_topology_def by (by100 blast)
              qed
              \<comment> \<open>Intersection of D and S¹ (both closed in B²) is closed.\<close>
              have "{D, top1_S1} \<noteq> ({}::(real\<times>real) set set)" by (by100 simp)
              moreover have "\<forall>A\<in>{D, top1_S1}. closedin_on top1_B2 top1_B2_topology A"
                using hD hS1_cl by (by100 blast)
              ultimately have "closedin_on top1_B2 top1_B2_topology (\<Inter>{D, top1_S1})"
                by (rule closedin_Inter[OF hB2_t])
              moreover have "\<Inter>{D, top1_S1} = D \<inter> top1_S1" by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            thus ?thesis using hD_eq by (by100 simp)
          qed
        qed
        hence "closedin_on top1_B2 top1_B2_topology (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
        proof -
          have hB2_top_loc: "is_topology_on top1_B2 top1_B2_topology"
            using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
          have hfin: "finite ((\<lambda>k. ?rot k ` ?C0) ` {..<n})" by (by100 simp)
          assume "\<And>k. k < n \<Longrightarrow> closedin_on top1_B2 top1_B2_topology (?rot k ` ?C0)"
          hence hall: "\<forall>A\<in>((\<lambda>k. ?rot k ` ?C0) ` {..<n}). closedin_on top1_B2 top1_B2_topology A"
            by (by100 blast)
          have "closedin_on top1_B2 top1_B2_topology (\<Union>((\<lambda>k. ?rot k ` ?C0) ` {..<n}))"
            by (rule closedin_Union_finite[OF hB2_top_loc hfin hall])
          moreover have "\<Union>((\<lambda>k. ?rot k ` ?C0) ` {..<n}) = (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
            by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis
        proof -
          assume hrot_cl: "closedin_on top1_B2 top1_B2_topology (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
          have "closedin_on top1_B2 top1_B2_topology (C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0))"
          proof -
            have hB2_t: "is_topology_on top1_B2 top1_B2_topology"
              using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
            have hfin: "finite {C, \<Union>k\<in>{..<n}. ?rot k ` ?C0}" by (by100 simp)
            have hall: "\<forall>A\<in>{C, \<Union>k\<in>{..<n}. ?rot k ` ?C0}. closedin_on top1_B2 top1_B2_topology A"
              using hC hrot_cl by (by100 blast)
            have "closedin_on top1_B2 top1_B2_topology (\<Union>{C, \<Union>k\<in>{..<n}. ?rot k ` ?C0})"
              by (rule closedin_Union_finite[OF hB2_t hfin hall])
            moreover have "\<Union>{C, \<Union>k\<in>{..<n}. ?rot k ` ?C0} = C \<union> (\<Union>k\<in>{..<n}. ?rot k ` ?C0)"
              by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis .
        qed
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>By quotient property: sat closed in B² \<Rightarrow> q(C) closed in X.\<close>
    show "closedin_on X TX (q ` C)"
    proof -
      have "q ` C \<subseteq> X" using hC_sub hq_surj by (by100 blast)
      moreover have "X - q ` C \<in> TX"
      proof -
        have "{z \<in> top1_B2. q z \<in> X - q ` C} = top1_B2 - ?sat"
          using hq_surj by (by5000 blast)
        moreover have "top1_B2 - ?sat \<in> top1_B2_topology"
          using hsat_closed unfolding closedin_on_def by (by100 blast)
        ultimately have "{z \<in> top1_B2. q z \<in> X - q ` C} \<in> top1_B2_topology" by (by100 simp)
        moreover have "X - q ` C \<subseteq> X" by (by100 blast)
        ultimately show ?thesis using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
      qed
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3b: B² is compact Hausdorff, hence normal.\<close>
  have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
    using top1_B2_path_connected unfolding top1_path_connected_on_def by (by100 blast)
  have hB2_haus: "is_hausdorff_on top1_B2 top1_B2_topology"
  proof -
    have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
      using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
    have hR_haus: "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
      using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq .
    have "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
        (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
      using conjunct1[OF conjunct2[OF Theorem_17_11]] hR_haus by (by100 blast)
    hence hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
    thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]]
      unfolding top1_B2_topology_def by (by100 blast)
  qed
  have hB2_compact: "top1_compact_on top1_B2 top1_B2_topology"
  proof -
    have hB2_sub: "top1_B2 \<subseteq> {-1..1} \<times> {-1..1::real}"
    proof
      fix p :: "real \<times> real" assume "p \<in> top1_B2"
      hence h: "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
      have "0 \<le> snd p ^ 2" by (by100 simp)
      hence "fst p ^ 2 \<le> 1" using h by (by100 linarith)
      hence "\<bar>fst p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>fst p\<bar>" 1] by (by100 simp)
      moreover have "0 \<le> fst p ^ 2" by (by100 simp)
      moreover have "snd p ^ 2 \<le> 1" using h calculation by (by100 linarith)
      hence "\<bar>snd p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>snd p\<bar>" 1] by (by100 simp)
      hence "- 1 \<le> snd p \<and> snd p \<le> 1" by (by100 linarith)
      moreover from \<open>\<bar>fst p\<bar> \<le> 1\<close> have "- 1 \<le> fst p \<and> fst p \<le> 1" by (by100 linarith)
      ultimately have "fst p \<in> {-1..1} \<and> snd p \<in> {-1..1}" by (by100 simp)
      thus "p \<in> {-1..1} \<times> {-1..1}" by (simp add: mem_Times_iff)
    qed
    have "closed top1_B2"
    proof -
      have "top1_B2 = (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1}"
        unfolding top1_B2_def by (by100 auto)
      moreover have "continuous_on UNIV (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2)"
        by (intro continuous_intros)
      hence "closed ((\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1})"
        by (intro closed_vimage closed_atMost) (simp add: continuous_on_eq_continuous_at open_UNIV)
      ultimately show ?thesis by (by100 simp)
    qed
    hence "compact top1_B2"
      using closed_subset_compact[OF compact_Icc_Times _ hB2_sub] by (by100 blast)
    have "top1_B2_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
      unfolding top1_B2_topology_def ..
    hence "top1_B2_topology = subspace_topology (UNIV::((real\<times>real) set)) (top1_open_sets::((real\<times>real) set set)) top1_B2"
      using product_topology_on_open_sets[where 'a=real and 'b=real] by simp
    hence "top1_compact_on top1_B2 top1_B2_topology \<longleftrightarrow> compact top1_B2"
      using top1_compact_on_subspace_UNIV_iff_compact[of top1_B2] by simp
    thus ?thesis using \<open>compact top1_B2\<close> by (by100 simp)
  qed
  have hB2_normal: "top1_normal_on top1_B2 top1_B2_topology"
    by (rule Theorem_32_3[OF hB2_compact hB2_haus])
  \<comment> \<open>Step 3c: Lemma 73.3 specialized to Hausdorff: closed quotient map from normal space
     gives Hausdorff target. For distinct x, y \<in> X: {x}, {y} are closed (closed map from T1).
     q\<inverse>({x}), q\<inverse>({y}) disjoint closed in B². B² normal \<Rightarrow> separated by open U, V.
     Then X - q(B²-U) and X - q(B²-V) are disjoint open neighborhoods of x, y.\<close>
  have hX_haus: "is_hausdorff_on X TX"
    by (rule dunce_cap_hausdorff[OF assms(2)])
  \<comment> \<open>Step 3b: S¹ \<subseteq> B² and S¹ is closed in B² (needed for Step 4).\<close>
  have hS1_sub_B2: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by (by100 auto)
  have hS1_closed: "closedin_on top1_B2 top1_B2_topology top1_S1"
  proof (rule closedin_intro[OF hS1_sub_B2])
    have hopen_disk: "open {z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}"
    proof -
      have hcont_nsq: "continuous_on UNIV (\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2)"
        by (intro continuous_intros)
      have hopen_lt1: "open {t::real. t < 1}"
      proof -
        have "{t::real. t < 1} = {..<1}" by (by100 auto)
        moreover have "open ({..<1}::real set)" by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      have heq: "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
          = (\<lambda>z. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV"
        by (by100 auto)
      have "open ((\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV)"
        using continuous_on_open_vimage[of "UNIV::((real\<times>real) set)"
              "\<lambda>z. (fst z)^2 + (snd z)^2"] hcont_nsq hopen_lt1
        by (by5000 auto)
      thus ?thesis using heq by (by100 simp)
    qed
    have hdisk_in_PT: "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
        \<in> product_topology_on top1_open_sets top1_open_sets"
      using hopen_disk product_topology_on_open_sets_real2 unfolding top1_open_sets_def
      by (by100 blast)
    have hdiff_eq: "top1_B2 - top1_S1 = top1_B2 \<inter> {z. (fst z)^2 + (snd z)^2 < 1}"
      unfolding top1_B2_def top1_S1_def by (by100 auto)
    show "top1_B2 - top1_S1 \<in> top1_B2_topology"
      unfolding top1_B2_topology_def subspace_topology_def
      using hdisk_in_PT hdiff_eq by (by100 blast)
  qed
  \<comment> \<open>Step 4: A is closed in X (image of compact S¹ under quotient map to Hausdorff X).\<close>
  have hA_cl: "closedin_on X TX ?A"
    by (rule compact_hausdorff_continuous_closed_map[OF hB2_compact hX_haus hq_cont hS1_closed])
  \<comment> \<open>Step 2: A = q(S¹) is homeomorphic to S¹.
     Book: h maps arc C from (1,0) to r(1,0) onto A, injective except at endpoints.
     The quotient of S¹ by n-fold rotation is again a circle.\<close>
  have hA_circle: "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
           ?A (subspace_topology X TX ?A) f
         \<and> f (1, 0) = ?a
         \<and> (\<forall>t\<in>top1_unit_interval. f (top1_R_to_S1 t) = q (cos (2*pi*t/real n), sin (2*pi*t/real n)))"
  proof -
    \<comment> \<open>Book: q maps arc C from (1,0) to r(1,0) onto A, injective except at endpoints.
       Proof: define g: [0,1] \<rightarrow> A by g(t) = q(cos(2\<pi>t/n), sin(2\<pi>t/n)).
       g(0) = g(1) = a (q identifies rotation by 2\<pi>/n).
       g is injective on (0,1) (different t give non-equivalent angles).
       So g and R\_to\_S1 identify the same pairs on [0,1]: only {0,1}.
       By the universal property of the quotient R\_to\_S1: [0,1] \<rightarrow> S¹,
       there exists continuous \<phi>: S¹ \<rightarrow> A with \<phi> \<circ> R\_to\_S1 = g.
       \<phi> is bijective, S¹ compact, A Hausdorff \<Rightarrow> \<phi> is a homeomorphism.\<close>
    let ?g = "\<lambda>t. q (cos (2*pi*t / real n), sin (2*pi*t / real n))"
    \<comment> \<open>Step A: g maps into X (via S¹ \<subseteq> B² \<subseteq> domain of q).\<close>
    \<comment> \<open>Step B: g maps into A = q(S¹).\<close>
    have hg_img: "\<And>t. (cos (2*pi*t / real n), sin (2*pi*t / real n)) \<in> top1_S1"
      unfolding top1_S1_def using sin_cos_squared_add by (by100 simp)
    hence hg_in_A: "\<And>t. ?g t \<in> ?A" by (by100 blast)
    \<comment> \<open>Step C: g(0) = g(1) = a.\<close>
    have hg0: "?g 0 = ?a"
      by (by100 simp)
    have hg1: "?g 1 = ?a"
    proof -
      have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      have hrot: "(cos (2*pi / real n), sin (2*pi / real n)) \<in> top1_S1"
        unfolding top1_S1_def using sin_cos_squared_add by (by100 simp)
      \<comment> \<open>q(1,0) = q(cos(2\<pi>/n), sin(2\<pi>/n)) because the latter is rotation by 2\<pi>/n of (1,0).\<close>
      have "q (1, 0) = q (cos (2*pi / real n), sin (2*pi / real n))"
      proof -
        from hq_S1[rule_format, OF h10 hrot]
        have hiff: "q (1, 0) = q (cos (2*pi / real n), sin (2*pi / real n)) \<longleftrightarrow>
            (\<exists>k::nat. k < n \<and> (cos (2*pi / real n), sin (2*pi / real n)) =
              (cos (2*pi*real k/real n) * fst (1::real, 0::real) - sin (2*pi*real k/real n) * snd (1::real, 0::real),
               sin (2*pi*real k/real n) * fst (1::real, 0::real) + cos (2*pi*real k/real n) * snd (1::real, 0::real)))"
          by (by5000 blast)
        \<comment> \<open>For n \<ge> 2: use k=1, rotation by 2\<pi>/n. For n=1: use k=0, identity.\<close>
        have "(\<exists>k::nat. k < n \<and> (cos (2*pi / real n), sin (2*pi / real n)) =
              (cos (2*pi*real k/real n) * 1 - sin (2*pi*real k/real n) * 0,
               sin (2*pi*real k/real n) * 1 + cos (2*pi*real k/real n) * 0))"
        proof (cases "n = 1")
          case True
          show ?thesis
          proof (rule exI[of _ 0], intro conjI)
            show "(0::nat) < n" using assms(1) by (by100 simp)
            show "(cos (2*pi / real n), sin (2*pi / real n)) =
                (cos (2*pi*real 0/real n) * 1 - sin (2*pi*real 0/real n) * 0,
                 sin (2*pi*real 0/real n) * 1 + cos (2*pi*real 0/real n) * 0)"
              using True by (by100 simp)
          qed
        next
          case False hence "n \<ge> 2" using assms(1) by (by100 simp)
          show ?thesis
          proof (rule exI[of _ 1], intro conjI)
            show "(1::nat) < n" using \<open>n \<ge> 2\<close> by (by100 simp)
            show "(cos (2*pi / real n), sin (2*pi / real n)) =
                (cos (2*pi*real 1/real n) * 1 - sin (2*pi*real 1/real n) * 0,
                 sin (2*pi*real 1/real n) * 1 + cos (2*pi*real 1/real n) * 0)"
              by (by100 simp)
          qed
        qed
        thus ?thesis using hiff by (by100 simp)
      qed
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step D: Apply Theorem\_22\_2 (quotient universal property) with
       p = R\_to\_S1|[0,1]: [0,1] \<rightarrow> S¹ (quotient map), g: [0,1] \<rightarrow> A.
       g constant on fibers of p (both identify only {0,1}).
       Gets continuous \<phi>: S¹ \<rightarrow> A with \<phi>(R\_to\_S1(t)) = g(t).\<close>
    \<comment> \<open>Step D1: g is continuous [0,1] \<rightarrow> A (in our topology framework).\<close>
    have hg_cont_top: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        ?A (subspace_topology X TX ?A) ?g"
    proof -
      let ?h = "\<lambda>t. (cos (2*pi*t / real n), sin (2*pi*t / real n))"
      \<comment> \<open>h: R \<rightarrow> S¹ continuous (polynomial \<Rightarrow> continuous\_on UNIV, bridge to top1).\<close>
      have hn_ne: "real n \<noteq> (0::real)" using assms(1) by (by100 simp)
      have hh_cont_on: "continuous_on UNIV ?h"
        by (intro continuous_intros) (simp add: assms)+
      have hh_img: "\<And>t. ?h t \<in> top1_B2"
      proof -
        fix t :: real
        have "(fst (?h t))^2 + (snd (?h t))^2 = 1"
          using sin_cos_squared_add[of "2*pi*t/real n"] by (by100 simp)
        thus "?h t \<in> top1_B2" unfolding top1_B2_def by (by100 simp)
      qed
      have hh_top1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
          top1_B2 top1_B2_topology ?h"
      proof -
        have "top1_continuous_map_on (UNIV::real set) top1_open_sets
            top1_B2 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2) ?h"
          by (rule top1_continuous_map_on_R_to_R2_subspace[OF hh_img hh_cont_on])
        thus ?thesis unfolding top1_B2_topology_def by (by100 blast)
      qed
      \<comment> \<open>Restrict h to [0,1].\<close>
      have hh_I: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_B2 top1_B2_topology ?h"
      proof -
        have hI_sub: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
        have "top1_continuous_map_on top1_unit_interval
            (subspace_topology UNIV top1_open_sets top1_unit_interval)
            top1_B2 top1_B2_topology ?h"
          by (rule top1_continuous_map_on_subspace_restrict[OF hh_top1 hI_sub])
        moreover have "subspace_topology UNIV top1_open_sets top1_unit_interval
            = top1_unit_interval_topology"
          unfolding top1_unit_interval_topology_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>g = q \<circ> h: [0,1] \<rightarrow> X continuous.\<close>
      have hg_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX ?g"
      proof -
        have hcomp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (q \<circ> ?h)"
          by (rule top1_continuous_map_on_comp[OF hh_I hq_cont])
        have "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> (q \<circ> ?h) t = ?g t" by (by100 simp)
        hence "{t \<in> top1_unit_interval. (q \<circ> ?h) t \<in> V} = {t \<in> top1_unit_interval. ?g t \<in> V}" for V
          by (by100 auto)
        thus ?thesis using hcomp unfolding top1_continuous_map_on_def by (by5000 auto)
      qed
      \<comment> \<open>Shrink codomain to A.\<close>
      have hg_img: "?g ` top1_unit_interval \<subseteq> ?A" using hg_in_A by (by100 blast)
      show ?thesis
        using top1_continuous_map_on_codomain_shrink[OF hg_X hg_img hA_sub] by (by100 blast)
    qed
    \<comment> \<open>Step D2: g constant on fibers of R\_to\_S1: if R\_to\_S1(t)=R\_to\_S1(t') then g(t)=g(t').\<close>
    have hg_const_fibers: "\<forall>t\<in>top1_unit_interval. \<forall>t'\<in>top1_unit_interval.
        top1_R_to_S1 t = top1_R_to_S1 t' \<longrightarrow> ?g t = ?g t'"
    proof (intro ballI impI)
      fix t t' assume ht: "t \<in> top1_unit_interval" and ht': "t' \<in> top1_unit_interval"
        and heq: "top1_R_to_S1 t = top1_R_to_S1 t'"
      \<comment> \<open>R\_to\_S1(t) = R\_to\_S1(t') with t, t' \<in> [0,1] means t = t' or {t,t'} = {0,1}.\<close>
      have "t = t' \<or> (t = 0 \<and> t' = 1) \<or> (t = 1 \<and> t' = 0)"
      proof -
        from heq have "cos (2*pi*t) = cos (2*pi*t') \<and> sin (2*pi*t) = sin (2*pi*t')"
          unfolding top1_R_to_S1_def by (by100 auto)
        hence "\<exists>k::int. 2*pi*t - 2*pi*t' = real_of_int k * 2 * pi"
          using cos_sin_eq_imp by (by100 blast)
        then obtain k :: int where hk: "2*pi*t - 2*pi*t' = real_of_int k * 2 * pi"
          by (by100 blast)
        have htk: "t - t' = real_of_int k"
        proof -
          from hk have "2*pi*t - 2*pi*t' - real_of_int k * 2 * pi = 0"
            by (by100 linarith)
          hence "2*pi*(t - t') - real_of_int k * (2 * pi) = 0"
            by (simp add: algebra_simps)
          hence "(t - t' - real_of_int k) * (2 * pi) = 0"
            by (simp add: algebra_simps)
          moreover have "(2 * pi :: real) \<noteq> 0" using pi_gt_zero by (by100 linarith)
          ultimately have "t - t' - real_of_int k = 0" by (by100 simp)
          thus ?thesis by (by100 linarith)
        qed
        have "t \<in> {0..1}" and "t' \<in> {0..1}"
          using ht ht' unfolding top1_unit_interval_def by (by100 auto)+
        hence "0 \<le> t" "t \<le> 1" "0 \<le> t'" "t' \<le> 1" by (by100 auto)+
        have "-1 \<le> t - t'" using \<open>0 \<le> t\<close> \<open>t' \<le> 1\<close> by (by100 linarith)
        have "t - t' \<le> 1" using \<open>t \<le> 1\<close> \<open>0 \<le> t'\<close> by (by100 linarith)
        have "-1 \<le> real_of_int k" using htk \<open>-1 \<le> t - t'\<close> by (by100 linarith)
        have "real_of_int k \<le> 1" using htk \<open>t - t' \<le> 1\<close> by (by100 linarith)
        hence "k \<ge> -1" and "k \<le> 1"
          using \<open>-1 \<le> real_of_int k\<close> \<open>real_of_int k \<le> 1\<close> by (by100 linarith)+
        hence "k \<in> {-1, 0, 1}" by (by100 auto)
        thus ?thesis using htk \<open>t \<in> {0..1}\<close> \<open>t' \<in> {0..1}\<close>
          by (by5000 force)
      qed
      thus "?g t = ?g t'"
      proof (elim disjE conjE)
        assume "t = t'" thus ?thesis by (by100 simp)
      next
        assume "t = 0" "t' = 1" thus ?thesis using hg0 hg1 by (by100 simp)
      next
        assume "t = 1" "t' = 0" thus ?thesis using hg0 hg1 by (by100 simp)
      qed
    qed
    \<comment> \<open>Step D3: R\_to\_S1|[0,1] is a quotient map.\<close>
    have hR_quot: "top1_quotient_map_on top1_unit_interval top1_unit_interval_topology
        top1_S1 top1_S1_topology top1_R_to_S1"
    proof -
      \<comment> \<open>[0,1] compact, S¹ Hausdorff, R\_to\_S1 continuous surjective.
         Continuous from compact to Hausdorff is closed map.
         Closed continuous surjection is quotient map.\<close>
      have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hTS1_loc: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by (by100 simp)
        thus ?thesis unfolding top1_S1_topology_def
          by (rule subspace_topology_is_topology_on) (by100 simp)
      qed
      \<comment> \<open>R\_to\_S1 continuous [0,1] \<rightarrow> S¹.\<close>
      have hR_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_S1 top1_S1_topology top1_R_to_S1"
      proof -
        have "top1_continuous_map_on (UNIV::real set) top1_open_sets
            top1_S1 top1_S1_topology top1_R_to_S1"
          using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
        from top1_continuous_map_on_subspace_restrict[OF this]
        show ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      \<comment> \<open>R\_to\_S1 surjective [0,1] \<rightarrow> S¹.\<close>
      have hR_surj_loc: "top1_R_to_S1 ` top1_unit_interval = top1_S1"
      proof
        \<comment> \<open>R\_to\_S1([0,1]) \<subseteq> S¹: trivial (R\_to\_S1 maps to S¹).\<close>
        show "top1_R_to_S1 ` top1_unit_interval \<subseteq> top1_S1"
        proof
          fix z assume "z \<in> top1_R_to_S1 ` top1_unit_interval"
          then obtain t where "z = top1_R_to_S1 t" by (by100 blast)
          thus "z \<in> top1_S1" unfolding top1_R_to_S1_def top1_S1_def
            using sin_cos_squared_add by (by100 simp)
        qed
      next
        \<comment> \<open>S¹ \<subseteq> R\_to\_S1([0,1]): for any (cos \<alpha>, sin \<alpha>) \<in> S¹, take \<theta> = \<alpha>/(2\<pi>) mod 1.\<close>
        show "top1_S1 \<subseteq> top1_R_to_S1 ` top1_unit_interval"
        proof
          fix p assume hp: "p \<in> top1_S1"
          hence h_norm: "(fst p)^2 + (snd p)^2 = 1" unfolding top1_S1_def by (by100 simp)
          \<comment> \<open>Use S1\_point\_to\_angle or direct Arg construction.\<close>
          from S1_point_to_angle[OF hp]
          obtain \<theta> :: real where h\<theta>: "top1_R_to_S1 \<theta> = p" by (by100 blast)
          let ?\<theta>' = "\<theta> - of_int (floor \<theta>)"
          have "?\<theta>' \<in> top1_unit_interval" unfolding top1_unit_interval_def
          proof -
            have "0 \<le> ?\<theta>'" by (by100 linarith)
            moreover have "?\<theta>' < 1" by (by100 linarith)
            hence "?\<theta>' \<le> 1" by (by100 linarith)
            ultimately show "?\<theta>' \<in> {0..1}" by (by100 auto)
          qed
          moreover have "top1_R_to_S1 ?\<theta>' = p"
            using h\<theta> top1_R_to_S1_int_shift[of ?\<theta>' "floor \<theta>"] by (by100 simp)
          ultimately show "p \<in> top1_R_to_S1 ` top1_unit_interval" by (by100 blast)
        qed
      qed
      \<comment> \<open>[0,1] is compact.\<close>
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "compact (top1_unit_interval :: real set)" unfolding top1_unit_interval_def
          by (rule compact_Icc)
        thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact
          unfolding top1_unit_interval_topology_def by (by100 blast)
      qed
      \<comment> \<open>S¹ Hausdorff.\<close>
      have hS1_haus_loc: "is_hausdorff_on top1_S1 top1_S1_topology"
      proof -
        have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
          using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
        have hR_haus: "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
          using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq .
        have "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
            (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
          using conjunct1[OF conjunct2[OF Theorem_17_11]] hR_haus by (by100 blast)
        hence "is_hausdorff_on (UNIV::(real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
        thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]]
          unfolding top1_S1_topology_def by (by100 blast)
      qed
      \<comment> \<open>Quotient map property: for V \<subseteq> S¹, if preimage open then V open.\<close>
      show ?thesis unfolding top1_quotient_map_on_def
      proof (intro conjI)
        show "is_topology_on top1_unit_interval top1_unit_interval_topology" by (rule hI_top)
        show "is_topology_on top1_S1 top1_S1_topology" by (rule hTS1_loc)
        show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_S1 top1_S1_topology top1_R_to_S1" by (rule hR_cont)
        show "top1_R_to_S1 ` top1_unit_interval = top1_S1" by (rule hR_surj_loc)
        \<comment> \<open>Quotient property: if preimage of V is open in [0,1] then V is open in S¹.
           Proof: complement of V has closed preimage (in compact [0,1]).
           Closed map: image of closed = closed. So S¹ - V = image of closed = closed.
           Hence V is open.\<close>
        show "\<forall>V. V \<subseteq> top1_S1 \<longrightarrow>
            ({x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V} \<in> top1_unit_interval_topology
                \<longrightarrow> V \<in> top1_S1_topology)"
        proof (intro allI impI)
          fix V assume hV: "V \<subseteq> top1_S1"
              and hpre: "{x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V} \<in> top1_unit_interval_topology"
          \<comment> \<open>Complement: {x \<in> I. R\_to\_S1 x \<notin> V} is closed in [0,1].\<close>
          have hcompl_cl: "closedin_on top1_unit_interval top1_unit_interval_topology
              {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
          proof -
            have hcl_sub: "{x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V} \<subseteq> top1_unit_interval"
              by (by100 blast)
            have hcl_compl: "top1_unit_interval - {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}
                = {x \<in> top1_unit_interval. top1_R_to_S1 x \<in> V}" by (by100 blast)
            have hcl_open: "top1_unit_interval - {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}
                \<in> top1_unit_interval_topology" using hcl_compl hpre by (by100 simp)
            show ?thesis using closedin_intro[OF hcl_sub hcl_open] by (by100 blast)
          qed
          \<comment> \<open>Image: R\_to\_S1({x | x \<in> I, R\_to\_S1 x \<notin> V}) = S¹ - V (surjectivity).\<close>
          have himg_eq: "top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V} = top1_S1 - V"
          proof
            show "top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V} \<subseteq> top1_S1 - V"
            proof
              fix z assume "z \<in> top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
              then obtain t where "t \<in> top1_unit_interval" "top1_R_to_S1 t \<notin> V" "z = top1_R_to_S1 t"
                by (by100 blast)
              moreover have "z \<in> top1_S1" using hR_surj_loc \<open>t \<in> top1_unit_interval\<close> \<open>z = _\<close>
                by (by100 blast)
              ultimately show "z \<in> top1_S1 - V" by (by100 blast)
            qed
          next
            show "top1_S1 - V \<subseteq> top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
            proof
              fix z assume "z \<in> top1_S1 - V"
              hence hzS1: "z \<in> top1_S1" and hzV: "z \<notin> V" by (by100 blast)+
              have "z \<in> top1_R_to_S1 ` top1_unit_interval" using hR_surj_loc hzS1 by (by100 blast)
              then obtain t where "t \<in> top1_unit_interval" "top1_R_to_S1 t = z" by (by100 blast)
              hence "t \<in> {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}" using hzV by (by100 blast)
              thus "z \<in> top1_R_to_S1 ` {x \<in> top1_unit_interval. top1_R_to_S1 x \<notin> V}"
                using \<open>top1_R_to_S1 t = z\<close> by (by100 blast)
            qed
          qed
          \<comment> \<open>Closed map: image of closed is closed in S¹.\<close>
          have "closedin_on top1_S1 top1_S1_topology (top1_S1 - V)"
            using compact_hausdorff_continuous_closed_map[OF hI_compact hS1_haus_loc hR_cont hcompl_cl]
                  himg_eq by (by100 simp)
          \<comment> \<open>S¹ - V closed \<Rightarrow> V open.\<close>
          hence "top1_S1 - (top1_S1 - V) \<in> top1_S1_topology"
            unfolding closedin_on_def by (by100 blast)
          moreover have "top1_S1 - (top1_S1 - V) = V \<inter> top1_S1" by (by100 blast)
          ultimately have "(V \<inter> top1_S1) \<in> top1_S1_topology" by (by100 simp)
          moreover have "V \<inter> top1_S1 = V" using hV by (by100 blast)
          ultimately show "V \<in> top1_S1_topology" by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Step D4: Apply Theorem\_22\_2 to get continuous \<phi>: S¹ \<rightarrow> A.\<close>
    let ?TA = "subspace_topology X TX ?A"
    from Theorem_22_2[OF hR_quot _ hg_const_fibers, of ?A ?TA]
    obtain \<phi> where h\<phi>_map: "\<forall>y\<in>top1_S1. \<phi> y \<in> ?A"
        and h\<phi>_eq: "\<forall>t\<in>top1_unit_interval. \<phi> (top1_R_to_S1 t) = ?g t"
        and h\<phi>_cont_iff: "(top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA \<phi>) \<longleftrightarrow>
            (top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA ?g)"
      using hg_in_A by (by5000 auto)
    have h\<phi>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA \<phi>"
      using h\<phi>_cont_iff hg_cont_top by (by100 blast)
    \<comment> \<open>Step D5: \<phi> is bijective.\<close>
    have h\<phi>_bij: "bij_betw \<phi> top1_S1 ?A"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on \<phi> top1_S1"
      proof (rule inj_onI)
        fix z z' assume hz: "z \<in> top1_S1" and hz': "z' \<in> top1_S1" and heq: "\<phi> z = \<phi> z'"
        have hR_surj: "top1_R_to_S1 ` top1_unit_interval = top1_S1"
          using hR_quot unfolding top1_quotient_map_on_def by (by100 blast)
        have "z \<in> top1_R_to_S1 ` top1_unit_interval" using hz hR_surj by (by100 blast)
        then obtain t where ht: "t \<in> top1_unit_interval" "top1_R_to_S1 t = z" by (by100 blast)
        have "z' \<in> top1_R_to_S1 ` top1_unit_interval" using hz' hR_surj by (by100 blast)
        then obtain t' where ht': "t' \<in> top1_unit_interval" "top1_R_to_S1 t' = z'" by (by100 blast)
        have "\<phi> z = ?g t" using h\<phi>_eq[rule_format, OF ht(1)] ht(2) by (by100 simp)
        moreover have "\<phi> z' = ?g t'" using h\<phi>_eq[rule_format, OF ht'(1)] ht'(2) by (by100 simp)
        ultimately have hgt: "?g t = ?g t'" using heq by (by100 simp)
        \<comment> \<open>g(t) = g(t') implies R\_to\_S1(t) = R\_to\_S1(t') by hg\_const\_fibers logic.\<close>
        have "top1_R_to_S1 t = top1_R_to_S1 t'"
        proof -
          have "t = t' \<or> (t = 0 \<and> t' = 1) \<or> (t = 1 \<and> t' = 0)"
          proof -
            \<comment> \<open>g(t) = g(t') means q identifies the two points on S¹. By hq\_S1, they are
               rotation-equivalent. This gives an integer relation on t, t'. On [0,1]
               the only possibilities are t=t' or {t,t'}={0,1}.\<close>
            have hS1_t: "(cos (2*pi*t/real n), sin (2*pi*t/real n)) \<in> top1_S1"
              using hg_img by (by100 blast)
            have hS1_t': "(cos (2*pi*t'/real n), sin (2*pi*t'/real n)) \<in> top1_S1"
              using hg_img by (by100 blast)
            \<comment> \<open>hq\_S1 gives rotation identification. Simplify fst/snd before applying.\<close>
            have hq_iff: "?g t = ?g t' \<longleftrightarrow>
                (\<exists>k::nat. k < n \<and> (cos (2*pi*t'/real n), sin (2*pi*t'/real n)) =
                (cos (2*pi*real k/real n) * cos (2*pi*t/real n) - sin (2*pi*real k/real n) * sin (2*pi*t/real n),
                 sin (2*pi*real k/real n) * cos (2*pi*t/real n) + cos (2*pi*real k/real n) * sin (2*pi*t/real n)))"
              using hq_S1[rule_format, OF hS1_t hS1_t'] by (by100 simp)
            from hq_iff hgt
            have "\<exists>k::nat. k < n \<and> (cos (2*pi*t'/real n), sin (2*pi*t'/real n)) =
                (cos (2*pi*real k/real n) * cos (2*pi*t/real n) - sin (2*pi*real k/real n) * sin (2*pi*t/real n),
                 sin (2*pi*real k/real n) * cos (2*pi*t/real n) + cos (2*pi*real k/real n) * sin (2*pi*t/real n))"
              by (by100 blast)
            then obtain k :: nat where hk: "k < n"
                and hpair: "(cos (2*pi*t'/real n), sin (2*pi*t'/real n)) =
                  (cos (2*pi*real k/real n) * cos (2*pi*t/real n) - sin (2*pi*real k/real n) * sin (2*pi*t/real n),
                   sin (2*pi*real k/real n) * cos (2*pi*t/real n) + cos (2*pi*real k/real n) * sin (2*pi*t/real n))"
              by (by100 blast)
            have hcos_eq: "cos (2*pi*t'/real n) = cos (2*pi*real k/real n + 2*pi*t/real n)"
              using hpair cos_add[of "2*pi*real k/real n" "2*pi*t/real n"] by (by5000 simp)
            have hsin_eq: "sin (2*pi*t'/real n) = sin (2*pi*real k/real n + 2*pi*t/real n)"
              using hpair sin_add[of "2*pi*real k/real n" "2*pi*t/real n"] by (by5000 simp)
            \<comment> \<open>cos\_sin\_eq\_imp: angle difference is integer multiple of 2\<pi>.\<close>
            from cos_sin_eq_imp[OF hcos_eq hsin_eq]
            obtain j :: int where hj: "2*pi*t'/real n - (2*pi*real k/real n + 2*pi*t/real n)
                = real_of_int j * 2 * pi" by (by100 blast)
            \<comment> \<open>Divide by 2\<pi>, multiply by n: t' = t + k + j*n.\<close>
            have hn_ne: "real n \<noteq> (0::real)" using assms(1) by (by100 simp)
            have "t' - t = real k + real_of_int j * real n"
            proof -
              have hpi_ne: "(2*pi :: real) \<noteq> 0" using pi_gt_zero by (by100 linarith)
              from hj have "t'/real n - real k/real n - t/real n = real_of_int j"
                using hn_ne hpi_ne by (by5000 algebra)
              hence "(t' - real k - t) / real n = real_of_int j"
                by (by5000 argo)
              thus ?thesis using hn_ne
                by (metis add.commute diff_add_cancel diff_right_commute mult.commute
                    nonzero_mult_div_cancel_left times_divide_eq_right)
            qed
            \<comment> \<open>With t, t' \<in> [0,1] and k \<in> {0,...,n-1}: integer k + j*n \<in> [-1,1].\<close>
            have "0 \<le> t" "t \<le> 1" "0 \<le> t'" "t' \<le> 1"
              using ht(1) ht'(1) unfolding top1_unit_interval_def by (by100 auto)+
            hence "-1 \<le> t' - t" "t' - t \<le> 1" by (by100 linarith)+
            hence "-1 \<le> real k + real_of_int j * real n"
                  "real k + real_of_int j * real n \<le> 1"
              using \<open>t' - t = real k + real_of_int j * real n\<close> by (by100 linarith)+
            \<comment> \<open>real k + real_of_int j * real n ∈ {-1, 0, 1} since integers in [-1,1].\<close>
            have "real k + real_of_int j * real n \<in> {-1, 0, 1}"
            proof -
              have hri: "real k + real_of_int j * real n = real_of_int (int k + j * int n)"
                by (by100 simp)
              have "int k + j * int n \<ge> -1" "int k + j * int n \<le> 1"
                using \<open>-1 \<le> real k + real_of_int j * real n\<close>
                      \<open>real k + real_of_int j * real n \<le> 1\<close> hri
                by (by5000 linarith)+
              hence "int k + j * int n \<in> {-1, 0, 1}" by (by5000 auto)
              thus ?thesis using hri by (by100 force)
            qed
            hence "t' - t \<in> {-1, 0, 1}"
              using \<open>t' - t = real k + real_of_int j * real n\<close> by (by100 simp)
            thus ?thesis using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> t'\<close> \<open>t' \<le> 1\<close>
              by (by5000 auto)
          qed
          thus ?thesis
          proof (elim disjE conjE)
            assume "t = t'" thus ?thesis by (by100 simp)
          next
            assume "t = 0" "t' = 1"
            thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
          next
            assume "t = 1" "t' = 0"
            thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
          qed
        qed
        thus "z = z'" using ht(2) ht'(2) by (by100 simp)
      qed
    next
      show "\<phi> ` top1_S1 = ?A"
      proof
        show "\<phi> ` top1_S1 \<subseteq> ?A" using h\<phi>_map by (by100 blast)
      next
        show "?A \<subseteq> \<phi> ` top1_S1"
        proof
          fix a assume "a \<in> ?A"
          then obtain s where hs: "s \<in> top1_S1" and ha: "a = q s" by (by100 blast)
          have hR_surj2: "top1_R_to_S1 ` top1_unit_interval = top1_S1"
            using hR_quot unfolding top1_quotient_map_on_def by (by100 blast)
          have "s \<in> top1_R_to_S1 ` top1_unit_interval" using hs hR_surj2 by (by100 blast)
          then obtain \<theta> where h\<theta>: "\<theta> \<in> top1_unit_interval" "top1_R_to_S1 \<theta> = s" by (by100 blast)
          \<comment> \<open>Need t \<in> [0,1] with g(t) = a = q(s). Since s = R\_to\_S1(\<theta>) = (cos 2\<pi>\<theta>, sin 2\<pi>\<theta>),
             and g(t) = q(cos(2\<pi>t/n), sin(2\<pi>t/n)), we need q(cos(2\<pi>t/n),...) = q(cos 2\<pi>\<theta>,...).
             This holds when 2\<pi>t/n \<equiv> 2\<pi>\<theta> mod 2\<pi>/n, i.e., t = n\<theta> + k for integer k.
             Take t = n\<theta> mod 1.\<close>
          let ?t = "real n * \<theta> - of_int (floor (real n * \<theta>))"
          have h_t_I: "?t \<in> top1_unit_interval" unfolding top1_unit_interval_def
          proof -
            have "0 \<le> ?t" by (by100 linarith)
            moreover have "?t < 1" by (by100 linarith)
            hence "?t \<le> 1" by (by100 linarith)
            ultimately show "?t \<in> {0..1}" by (by100 auto)
          qed
          have "?g ?t = a"
          proof -
            let ?m = "floor (real n * \<theta>)"
            \<comment> \<open>2\<pi>?t/n = 2\<pi>\<theta> - 2\<pi>?m/n. The point (cos(2\<pi>?t/n), sin(2\<pi>?t/n)) is a rotation
               of s = (cos(2\<pi>\<theta>), sin(2\<pi>\<theta>)) by angle -2\<pi>?m/n.
               By hq\_S1, q identifies rotations by 2\<pi>k/n. Need k \<in> {0,...,n-1}.\<close>
            have hn_pos: "real n > 0" using assms(1) by (by100 simp)
            have hn_ne: "real n \<noteq> (0::real)" using hn_pos by (by100 linarith)
            have h_angle: "2*pi*?t / real n = 2*pi*\<theta> - 2*pi * real_of_int ?m / real n"
              using hn_ne by (simp add: diff_divide_eq_iff right_diff_distrib')
            \<comment> \<open>s is on S¹.\<close>
            have hs_S1: "s \<in> top1_S1" by (rule hs)
            have hs_eq: "s = (cos (2*pi*\<theta>), sin (2*pi*\<theta>))"
              using h\<theta>(2) unfolding top1_R_to_S1_def by (by100 simp)
            \<comment> \<open>The g-image point is on S¹.\<close>
            have hgt_S1: "(cos (2*pi*?t / real n), sin (2*pi*?t / real n)) \<in> top1_S1"
              using hg_img by (by100 blast)
            \<comment> \<open>Use hq\_S1: q(s) = q(gt\_point) iff gt\_point is a rotation of s.\<close>
            from hq_S1[rule_format, OF hs_S1 hgt_S1]
            have hq_iff: "q s = q (cos (2*pi*?t / real n), sin (2*pi*?t / real n)) \<longleftrightarrow>
                (\<exists>k::nat. k < n \<and> (cos (2*pi*?t / real n), sin (2*pi*?t / real n)) =
                  (cos (2*pi*real k/real n) * fst s - sin (2*pi*real k/real n) * snd s,
                   sin (2*pi*real k/real n) * fst s + cos (2*pi*real k/real n) * snd s))"
              by (by5000 blast)
            \<comment> \<open>We need to find k. Using addition formulas:
               cos(2\<pi>\<theta> - 2\<pi>m/n) = cos(2\<pi>\<theta>)cos(2\<pi>m/n) + sin(2\<pi>\<theta>)sin(2\<pi>m/n)
               This equals cos(-2\<pi>m/n)*cos(2\<pi>\<theta>) - sin(-2\<pi>m/n)*sin(2\<pi>\<theta>)
               = cos(2\<pi>m/n)*cos(2\<pi>\<theta>) + sin(2\<pi>m/n)*sin(2\<pi>\<theta>)
               The rotation formula: rot\_k(s) = (cos(2\<pi>k/n)*fst s - sin(2\<pi>k/n)*snd s, ...)
               We need k such that rot\_k reverses the -2\<pi>m/n rotation.
               Take k = nat((-?m) mod int n). This works modulo n.\<close>
            let ?k = "nat ((-?m) mod int n)"
            have hk_lt: "?k < n"
            proof -
              have "int n > 0" using assms(1) by (by100 simp)
              hence "(-?m) mod int n \<ge> 0 \<and> (-?m) mod int n < int n" by (by100 simp)
              thus ?thesis by (by100 auto)
            qed
            \<comment> \<open>The angle 2\<pi>?t/n + 2\<pi>?k/n = 2\<pi>\<theta> + 2\<pi>(-?m + ?k)/n = 2\<pi>\<theta> + integer * 2\<pi>.\<close>
            \<comment> \<open>Key: 2\<pi>?t/n = 2\<pi>?k/n + 2\<pi>\<theta> - 2\<pi>j for integer j = (?m+?k)/n.
               Since k = nat((-?m) mod n): ?m + int ?k = ?m + (-?m) mod n \<equiv> 0 (mod n).
               So (?m + int ?k)/n is an integer. Then cos/sin periodicity gives the result.\<close>
            have hmod0: "(?m + int ?k) mod int n = 0"
            proof -
              have hint_n: "int n > 0" using assms(1) by (by100 simp)
              have "int ?k = (-?m) mod int n"
                using hint_n by (by100 simp)
              hence "(?m + int ?k) mod int n = (?m + (-?m) mod int n) mod int n"
                by (by100 simp)
              also have "\<dots> = (?m + (-?m)) mod int n"
                using mod_add_right_eq[of ?m "(-?m)" "int n"] by (by100 simp)
              also have "\<dots> = 0" by (by100 simp)
              finally show ?thesis .
            qed
            let ?j = "(?m + int ?k) div int n"
            have hj_eq: "?m + int ?k = ?j * int n" using hmod0 by (by100 auto)
            \<comment> \<open>2\<pi>?t/n = 2\<pi>?k/n + 2\<pi>\<theta> - 2\<pi>?j (where j is an integer).\<close>
            have h_angle2: "2*pi*?t/real n = 2*pi*real ?k/real n + 2*pi*\<theta> - real_of_int ?j * (2*pi)"
            proof -
              \<comment> \<open>From hj_eq: m + k = j*n, so m = j*n - k.\<close>
              from hj_eq have hm_rel: "?m = ?j * int n - int ?k" by (by100 linarith)
              \<comment> \<open>real_of_int m = real_of_int j * real n - real k.\<close>
              have hint_n: "int n > 0" using assms(1) by (by100 simp)
              have hk_nn: "int ?k \<ge> 0" using hint_n by (by100 simp)
              have "real_of_int (int ?k) = real ?k" using hk_nn by (by100 simp)
              have hm_real: "real_of_int ?m = real_of_int ?j * real n - real ?k"
              proof -
                from hm_rel have "real_of_int ?m = real_of_int (?j * int n - int ?k)" by (by100 simp)
                also have "\<dots> = real_of_int (?j * int n) - real_of_int (int ?k)" by (by100 simp)
                also have "real_of_int (?j * int n) = real_of_int ?j * real n" by (by100 simp)
                also have "real_of_int (int ?k) = real ?k" using hk_nn by (by100 simp)
                finally show ?thesis by (by100 linarith)
              qed
              \<comment> \<open>So 2*pi*m/n = 2*pi*(j*n - k)/n = 2*pi*j - 2*pi*k/n.\<close>
              have "2*pi * real_of_int ?m / real n = 2*pi * real_of_int ?j - 2*pi * real ?k / real n"
                using hm_real hn_ne by (simp add: diff_divide_eq_iff right_diff_distrib')
              \<comment> \<open>h_angle gives 2*pi*t/n = 2*pi*theta - 2*pi*m/n.\<close>
              hence "2*pi*?t/real n = 2*pi*\<theta> - (2*pi * real_of_int ?j - 2*pi * real ?k / real n)"
                using h_angle by (by100 linarith)
              hence "2*pi*?t/real n = 2*pi * real ?k / real n + 2*pi*\<theta> - 2*pi * real_of_int ?j"
                by (by100 linarith)
              thus ?thesis by (by5000 simp)
            qed
            \<comment> \<open>cos/sin at angle 2\<pi>?t/n = cos/sin at angle 2\<pi>?k/n + 2\<pi>\<theta> (periodicity).\<close>
            \<comment> \<open>cos/sin periodicity via R\_to\_S1\_int\_shift: t/n = k/n + \<theta> - j.\<close>
            \<comment> \<open>From h_angle2 + R_to_S1_int_shift: cos/sin at 2πt/n = cos/sin at 2πk/n+2πθ.\<close>
            have hcos_eq: "cos (2*pi*?t/real n) = cos (2*pi*real ?k/real n + 2*pi*\<theta>)"
            proof -
              let ?x = "2*pi*real ?k/real n + 2*pi*\<theta>"
              from h_angle2 have "2*pi*?t/real n = ?x - real_of_int ?j * (2*pi)"
                by (by100 blast)
              hence "cos (2*pi*?t/real n) = cos (?x - real_of_int ?j * (2*pi))"
                by (by100 simp)
              also have "\<dots> = cos ?x * cos (real_of_int ?j * (2*pi))
                  + sin ?x * sin (real_of_int ?j * (2*pi))"
                by (rule cos_diff)
              also have "cos (real_of_int ?j * (2*pi)) = 1"
                using cos_int_2pin[of ?j] by (metis mult.commute)
              also have "sin (real_of_int ?j * (2*pi)) = 0"
                using sin_int_2pin[of ?j] by (metis mult.commute)
              finally show ?thesis by (by100 simp)
            qed
            have hsin_eq: "sin (2*pi*?t/real n) = sin (2*pi*real ?k/real n + 2*pi*\<theta>)"
              using h_angle2 by (metis diff_add_cancel mult.commute sin_cos_eq_iff)
            \<comment> \<open>Addition formulas: rotation = cos/sin of sum.\<close>
            have "(cos (2*pi*?t / real n), sin (2*pi*?t / real n)) =
                (cos (2*pi*real ?k/real n) * fst s - sin (2*pi*real ?k/real n) * snd s,
                 sin (2*pi*real ?k/real n) * fst s + cos (2*pi*real ?k/real n) * snd s)"
            proof -
              have "cos (2*pi*?t/real n) = cos (2*pi*real ?k/real n + 2*pi*\<theta>)" by (rule hcos_eq)
              also have "\<dots> = cos (2*pi*real ?k/real n) * cos (2*pi*\<theta>)
                  - sin (2*pi*real ?k/real n) * sin (2*pi*\<theta>)" by (rule cos_add)
              finally have hc: "cos (2*pi*?t/real n) = cos (2*pi*real ?k/real n) * cos (2*pi*\<theta>)
                  - sin (2*pi*real ?k/real n) * sin (2*pi*\<theta>)" .
              have "sin (2*pi*?t/real n) = sin (2*pi*real ?k/real n + 2*pi*\<theta>)" by (rule hsin_eq)
              also have "\<dots> = sin (2*pi*real ?k/real n) * cos (2*pi*\<theta>)
                  + cos (2*pi*real ?k/real n) * sin (2*pi*\<theta>)" by (rule sin_add)
              finally have hs: "sin (2*pi*?t/real n) = sin (2*pi*real ?k/real n) * cos (2*pi*\<theta>)
                  + cos (2*pi*real ?k/real n) * sin (2*pi*\<theta>)" .
              show ?thesis using hc hs hs_eq by (by100 simp)
            qed
            hence "q s = q (cos (2*pi*?t / real n), sin (2*pi*?t / real n))"
              using hq_iff hk_lt by (by100 blast)
            thus "?g ?t = a" using ha by (by100 simp)
          qed
          hence "\<phi> (top1_R_to_S1 ?t) = a" using h\<phi>_eq h_t_I by (by100 simp)
          moreover have "top1_R_to_S1 ?t \<in> top1_S1" using hR_surj2 h_t_I by (by100 blast)
          ultimately show "a \<in> \<phi> ` top1_S1" by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>Step D6: Theorem\_26\_6: compact S¹ \<rightarrow> Hausdorff A = homeomorphism.\<close>
    have hTA_top: "is_topology_on ?A ?TA"
      by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    have hA_haus: "is_hausdorff_on ?A ?TA"
      using conjunct2[OF conjunct2[OF Theorem_17_11]] hX_haus hA_sub by (by100 blast)
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      thus ?thesis unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have hhomeo: "top1_homeomorphism_on top1_S1 top1_S1_topology ?A ?TA \<phi>"
      by (rule Theorem_26_6[OF hTS1 hTA_top S1_compact hA_haus h\<phi>_cont h\<phi>_bij])
    moreover have "\<phi> (1, 0) = ?a"
    proof -
      have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
      hence "\<phi> (top1_R_to_S1 0) = ?g 0" using h\<phi>_eq by (by100 blast)
      thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
    qed
    moreover have "\<forall>t\<in>top1_unit_interval. \<phi> (top1_R_to_S1 t) = q (cos (2*pi*t/real n), sin (2*pi*t/real n))"
      using h\<phi>_eq by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 5: q restricted to Int(B²) = B² - S¹ is a homeomorphism onto X - A.
     Proof: B² - S¹ is open and saturated in B², so by Thm 22.1 the restriction
     is a quotient map. Since it's also bijective, it's a homeomorphism.\<close>
  have hintB2_sub: "top1_B2 - top1_S1 \<subseteq> top1_B2" by (by100 blast)
  have hintB2_open: "openin_on top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
    using hS1_closed unfolding openin_on_def closedin_on_def by (by100 blast)
  \<comment> \<open>B² - S¹ is saturated: each fiber q⁻¹(q(z)) for z ∈ B²-S¹ is {z} (by inj + sep).\<close>
  have hintB2_sat: "top1_saturated_with_respect_to_on top1_B2 q (top1_B2 - top1_S1)"
    unfolding top1_saturated_with_respect_to_on_def
  proof (intro conjI ballI impI)
    show "top1_B2 - top1_S1 \<subseteq> top1_B2" by (by100 blast)
  next
    fix x y assume hx: "x \<in> top1_B2 - top1_S1" and hy: "y \<in> top1_B2" and hqeq: "q y = q x"
    show "y \<in> top1_B2 - top1_S1"
    proof (rule ccontr)
      assume "y \<notin> top1_B2 - top1_S1"
      hence "y \<in> top1_S1" using hy by (by100 blast)
      hence "q x \<noteq> q y" using hq_sep hx by (by5000 metis)
      thus False using hqeq by (by100 simp)
    qed
  qed
  \<comment> \<open>q(B² - S¹) = X - A: surjectivity of q + separation.\<close>
  have hq_intB2_img: "q ` (top1_B2 - top1_S1) = X - ?A"
  proof
    show "q ` (top1_B2 - top1_S1) \<subseteq> X - ?A"
    proof
      fix y assume "y \<in> q ` (top1_B2 - top1_S1)"
      then obtain z where hz: "z \<in> top1_B2 - top1_S1" and hy: "y = q z" by (by100 blast)
      have "y \<in> X" using hq_surj hz hy by (by100 blast)
      moreover have "y \<notin> ?A"
      proof
        assume "y \<in> ?A"
        then obtain s where hs: "s \<in> top1_S1" and hqs: "y = q s" by (by100 blast)
        have "q z = q s" using hy hqs by (by100 simp)
        thus False using hq_sep hz hs by (by5000 metis)
      qed
      ultimately show "y \<in> X - ?A" by (by100 blast)
    qed
  next
    show "X - ?A \<subseteq> q ` (top1_B2 - top1_S1)"
    proof
      fix y assume "y \<in> X - ?A"
      hence hyX: "y \<in> X" and hyA: "y \<notin> ?A" by (by100 blast)+
      from hyX obtain z where hz: "z \<in> top1_B2" and hy: "y = q z" using hq_surj by (by100 blast)
      have "z \<notin> top1_S1"
      proof
        assume "z \<in> top1_S1" hence "y \<in> ?A" using hy by (by100 blast)
        thus False using hyA by (by100 blast)
      qed
      hence "z \<in> top1_B2 - top1_S1" using hz by (by100 blast)
      thus "y \<in> q ` (top1_B2 - top1_S1)" using hy by (by100 blast)
    qed
  qed
  \<comment> \<open>By Theorem 22.1: q restricted to B²-S¹ is a quotient map onto X-A.\<close>
  have hq_restricted_quot: "top1_quotient_map_on (top1_B2 - top1_S1)
      (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
      (X - ?A)
      (subspace_topology X TX (X - ?A)) q"
  proof -
    have "openin_on top1_B2 top1_B2_topology (top1_B2 - top1_S1) \<or>
          closedin_on top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
      using hintB2_open by (by100 blast)
    hence "top1_quotient_map_on (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        (q ` (top1_B2 - top1_S1))
        (subspace_topology X TX (q ` (top1_B2 - top1_S1))) q"
      using Theorem_22_1(1)[OF hq_quot hintB2_sat] by (by100 blast)
    thus ?thesis using hq_intB2_img by (by100 simp)
  qed
  \<comment> \<open>q restricted to B²-S¹ is bijective onto X-A.\<close>
  have hq_bij: "bij_betw q (top1_B2 - top1_S1) (X - ?A)"
  proof -
    have hinj: "inj_on q (top1_B2 - top1_S1)" using hq_inj by (by100 blast)
    have hsurj: "q ` (top1_B2 - top1_S1) = X - ?A" by (rule hq_intB2_img)
    show ?thesis unfolding bij_betw_def using hinj hsurj by (by100 blast)
  qed
  \<comment> \<open>Bijective quotient map is homeomorphism.\<close>
  have hq_int_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
      (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
      (X - ?A)
      (subspace_topology X TX (X - ?A)) q"
    by (rule top1_bij_quotient_map_on_imp_homeomorphism_on[OF hq_restricted_quot hq_bij])
  \<comment> \<open>Step 6: q(S¹) \<subseteq> A and q(1,0) = a (trivially).\<close>
  have hq_S1_A: "q ` top1_S1 \<subseteq> ?A" by (by100 blast)
  have hq_10: "q (1, 0) = ?a" by (by100 simp)
  \<comment> \<open>Step 7: \<pi>_1(A, a) \<cong> Z (since A \<cong> S¹).\<close>
  have hA_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?A (subspace_topology X TX ?A) ?a)
      (top1_fundamental_group_mul ?A (subspace_topology X TX ?A) ?a)
      top1_Z_group top1_Z_mul"
  proof -
    let ?TA = "subspace_topology X TX ?A"
    obtain h_circ where h_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology ?A ?TA h_circ"
      using hA_circle by (by100 blast)
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA_top: "is_topology_on ?A ?TA"
      by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    have hS1_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>Homeomorphism gives iso at base points.\<close>
    have hS1_A_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier ?A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul ?A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTA_top h_homeo h10_S1]) (by100 simp)
    have hA_hc_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul ?A ?TA (h_circ (1, 0)))
        top1_Z_group top1_Z_mul"
    proof -
      have hgrpS1: "top1_is_group_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
        by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
      have hhc_A: "h_circ (1, 0) \<in> ?A"
        using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hgrpA: "top1_is_group_on
          (top1_fundamental_group_carrier ?A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_mul ?A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_id ?A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_invg ?A ?TA (h_circ (1, 0)))"
        by (rule top1_fundamental_group_is_group[OF hTA_top hhc_A])
      have "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier ?A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_mul ?A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
        by (rule top1_groups_isomorphic_on_sym[OF hS1_A_iso hgrpS1 hgrpA])
      thus ?thesis by (rule groups_isomorphic_trans_fwd[OF _ hS1_Z])
    qed
    \<comment> \<open>Base change within A: \<pi>_1(A, a) \<cong> \<pi>_1(A, h_circ(1,0)) (A path-connected).\<close>
    have hA_pc: "top1_path_connected_on ?A ?TA"
    proof -
      have "top1_path_connected_on top1_S1 top1_S1_topology" by (rule S1_path_connected)
      thus ?thesis by (rule homeomorphism_preserves_path_connected[OF h_homeo])
    qed
    have hhc_A: "h_circ (1, 0) \<in> ?A"
      using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hA_bc: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?A ?TA ?a)
        (top1_fundamental_group_mul ?A ?TA ?a)
        (top1_fundamental_group_carrier ?A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul ?A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_2_basepoint_independent[OF hA_pc ha_A hhc_A])
    show ?thesis by (rule groups_isomorphic_trans_fwd[OF hA_bc hA_hc_Z])
  qed
  \<comment> \<open>Step 8: A path-connected (for Theorem 72.1).\<close>
  let ?TA = "subspace_topology X TX ?A"
  have hTA_top: "is_topology_on ?A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
  have hA_pc: "top1_path_connected_on ?A ?TA"
  proof -
    obtain h_circ where hhc: "top1_homeomorphism_on top1_S1 top1_S1_topology ?A ?TA h_circ"
      using hA_circle by (by100 blast)
    have "top1_path_connected_on top1_S1 top1_S1_topology" by (rule S1_path_connected)
    thus ?thesis by (rule homeomorphism_preserves_path_connected[OF hhc])
  qed
  \<comment> \<open>Step 9: Apply Theorem 72.1 with base point a = q(1,0).\<close>
  from Theorem_72_1_attaching_two_cell[OF hX_strict hX_haus hA_cl hA_pc
      hq_cont ha_A hq_int_homeo hq_S1_A hq_10]
  obtain \<iota> where h\<iota>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA \<iota>"
      and h\<iota>_eq: "\<forall>z\<in>top1_S1. \<iota> z = q z"
      and h72_iso: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier X TX ?a)
          (top1_fundamental_group_mul X TX ?a)
          (top1_quotient_group_carrier_on
             (top1_fundamental_group_carrier ?A ?TA ?a)
             (top1_fundamental_group_mul ?A ?TA ?a)
             (top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier ?A ?TA ?a)
                (top1_fundamental_group_mul ?A ?TA ?a)
                (top1_fundamental_group_id ?A ?TA ?a)
                (top1_fundamental_group_invg ?A ?TA ?a)
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                   ?A ?TA ?a \<iota>
                   {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                         (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
          (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a))"
    by (by100 blast)
  \<comment> \<open>Step 10: The relator [k\<circ>p] in \<pi>_1(A,a) \<cong> Z corresponds to n.
     The standard S¹ loop p goes around once. Under \<iota> (which maps S¹ to A following q),
     the loop \<iota>\<circ>p wraps n times around A (since q identifies n-fold rotations).
     So [k\<circ>p] = n \<in> Z, and the quotient is Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.\<close>
  \<comment> \<open>Step 10a: \<pi>_1(A,a)/\<langle>\<langle>[k\<circ>p]\<rangle>\<rangle> \<cong> Z/nZ.\<close>
  have hquot_ZnZ_and_pres: "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on
         (top1_fundamental_group_carrier ?A ?TA ?a)
         (top1_fundamental_group_mul ?A ?TA ?a)
         (top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?A ?TA ?a)
            (top1_fundamental_group_mul ?A ?TA ?a)
            (top1_fundamental_group_id ?A ?TA ?a)
            (top1_fundamental_group_invg ?A ?TA ?a)
            {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
               ?A ?TA ?a \<iota>
               {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
      (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a))
      (top1_Zn_group n) (top1_Zn_mul n)
    \<and> (\<exists>e invg. top1_group_presented_by_on
          (top1_quotient_group_carrier_on
             (top1_fundamental_group_carrier ?A ?TA ?a)
             (top1_fundamental_group_mul ?A ?TA ?a)
             (top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier ?A ?TA ?a)
                (top1_fundamental_group_mul ?A ?TA ?a)
                (top1_fundamental_group_id ?A ?TA ?a)
                (top1_fundamental_group_invg ?A ?TA ?a)
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                   ?A ?TA ?a \<iota>
                   {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                         (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
          (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a))
          e invg ({..<1}::nat set) { replicate n (0::nat, True) })"
  proof -
    let ?GA = "top1_fundamental_group_carrier ?A ?TA ?a"
    let ?mulA = "top1_fundamental_group_mul ?A ?TA ?a"
    let ?eA = "top1_fundamental_group_id ?A ?TA ?a"
    let ?invA = "top1_fundamental_group_invg ?A ?TA ?a"
    let ?relator = "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
               ?A ?TA ?a \<iota>
               {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}"
    let ?N = "top1_normal_subgroup_generated_on ?GA ?mulA ?eA ?invA {?relator}"
    \<comment> \<open>Step 10.1: Get iso phi: pi1(A,a) -> Z.
       We have hA_Z_iso: pi1(A,a) iso Z. Extract an explicit iso.\<close>
    obtain \<phi> where h\<phi>_iso: "top1_group_iso_on ?GA ?mulA top1_Z_group top1_Z_mul \<phi>"
      using hA_Z unfolding top1_groups_isomorphic_on_def by (by100 blast)
    \<comment> \<open>Step 10.2: phi maps the relator to plus/minus n.
       The standard S1 loop goes around once. Under iota (= q on S1),
       this maps to the loop q(cos(2*pi*t), sin(2*pi*t)) in A,
       which equals the n-fold product of the A-generator alpha.
       So phi(relator) = plus/minus n.\<close>
    have h_relator_val: "\<phi> ?relator = int n \<or> \<phi> ?relator = - int n"
    proof -
      \<comment> \<open>Following Munkres p.443: gamma(t) = (cos(2*pi*t/n), sin(2*pi*t/n)) is the arc from p to r(p).
         alpha = h . gamma represents a generator of pi1(A,a).
         The standard S1 loop f goes around once, decomposing as gamma * (r.gamma) * ... * (r^{n-1}.gamma).
         Since h identifies rotations, h.f = alpha^n.
         Under any iso phi: pi1(A,a) -> Z, phi(alpha) = +/-1, so phi(alpha^n) = +/-n.\<close>
      \<comment> \<open>Step A: Define alpha = iota . gamma where gamma(t) = (cos(2*pi*t/n), sin(2*pi*t/n)).\<close>
      let ?\<gamma> = "\<lambda>t::real. (cos (2*pi*t/real n), sin (2*pi*t/real n))"
      let ?\<alpha> = "\<lambda>t::real. \<iota> (?\<gamma> t)"
      \<comment> \<open>Step B: alpha is a loop in A based at a (since gamma(0) = p and gamma(1) = r(p),
         and iota(p) = iota(r(p)) = a because q identifies rotations).\<close>
      have h\<alpha>_loop: "top1_is_loop_on ?A ?TA ?a ?\<alpha>"
      proof -
        \<comment> \<open>alpha(0) = iota(1,0) = a.\<close>
        have h\<alpha>0: "?\<alpha> 0 = ?a"
        proof -
          have "?\<gamma> 0 = (1, 0)" by (by100 simp)
          hence "?\<alpha> 0 = \<iota> (1, 0)" by (by100 simp)
          also have "\<dots> = ?a" using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
          finally show ?thesis .
        qed
        \<comment> \<open>alpha(1) = iota(cos(2pi/n), sin(2pi/n)) = iota(r(1,0)) = q(r(1,0)) = q(1,0) = a.\<close>
        have h\<alpha>1: "?\<alpha> 1 = ?a"
        proof -
          let ?pt = "(cos (2*pi*1/real n), sin (2*pi*1/real n))"
          have h1: "?\<alpha> 1 = \<iota> ?pt" by (by100 simp)
          have hpt_S1: "?pt \<in> top1_S1" unfolding top1_S1_def by (by100 auto)
          have h2: "\<iota> ?pt = q ?pt" using h\<iota>_eq hpt_S1 by (by100 blast)
          have h3: "q ?pt = q (1, 0)"
          proof (cases "n = 1")
            case True
            \<comment> \<open>n=1: pt = (cos(2pi), sin(2pi)) = (1,0).\<close>
            hence "?pt = (1, 0)" by (by100 simp)
            thus ?thesis by (by100 simp)
          next
            case False
            hence "n \<ge> 2" using assms(1) by (by100 linarith)
            hence "1 < n" by (by100 linarith)
            moreover have "?pt = (cos (2*pi*real 1/real n) * fst (1::real, 0::real)
                - sin (2*pi*real 1/real n) * snd (1::real, 0::real),
                sin (2*pi*real 1/real n) * fst (1::real, 0::real)
                + cos (2*pi*real 1/real n) * snd (1::real, 0::real))"
              by (by100 simp)
            ultimately have "q (1, 0) = q ?pt"
              using hq_S1[rule_format, OF h10_S1 hpt_S1] by (by100 blast)
            thus ?thesis by (by100 simp)
          qed
          show ?thesis using h1 h2 h3 hq_10 by (by100 simp)
        qed
        \<comment> \<open>alpha is continuous on [0,1] into A.\<close>
        have h\<alpha>_cont: "top1_is_path_on ?A ?TA ?a ?a ?\<alpha>"
        proof -
          \<comment> \<open>gamma maps [0,1] into S1.\<close>
          have h\<gamma>_image: "\<forall>t \<in> top1_unit_interval. ?\<gamma> t \<in> top1_S1"
            unfolding top1_S1_def top1_unit_interval_def by (by100 auto)
          \<comment> \<open>gamma is continuous on [0,1] (cos and sin are continuous).\<close>
          have h\<gamma>_cont_on: "continuous_on top1_unit_interval ?\<gamma>"
            using assms(1) by (intro continuous_intros; by100 simp)
          \<comment> \<open>Bridge to formal continuous_map_on.\<close>
          have h\<gamma>_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              top1_S1 top1_S1_topology ?\<gamma>"
          proof -
            \<comment> \<open>gamma = R_to_S1 . (lambda t. t/n).\<close>
            have h\<gamma>_eq: "?\<gamma> = top1_R_to_S1 \<circ> (\<lambda>t. t / real n)"
            proof (rule ext)
              fix t :: real show "?\<gamma> t = (top1_R_to_S1 \<circ> (\<lambda>t. t / real n)) t"
                unfolding top1_R_to_S1_def by (by100 simp)
            qed
            \<comment> \<open>R_to_S1 is continuous UNIV -> S1 (covering map).\<close>
            have hR_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
              using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
            \<comment> \<open>Restrict to [0,1].\<close>
            from top1_continuous_map_on_restrict_domain_simple[OF hR_cont subset_UNIV]
            have hR_I: "top1_continuous_map_on top1_unit_interval
                (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
                top1_S1 top1_S1_topology top1_R_to_S1" .
            \<comment> \<open>subspace_topology UNIV open_sets I = I_topology.\<close>
            have hI_eq: "subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval
                = top1_unit_interval_topology"
              unfolding top1_unit_interval_topology_def by (by100 blast)
            have hR_I2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_S1 top1_S1_topology top1_R_to_S1"
              using hR_I hI_eq by (by100 simp)
            \<comment> \<open>t/n is continuous [0,1] -> [0,1] (or at least [0,1] -> UNIV -> S1 via R_to_S1).\<close>
            \<comment> \<open>Actually, compose: (lambda t. t/n) maps [0,1] into UNIV, R_to_S1 maps UNIV to S1.\<close>
            \<comment> \<open>Use: continuous_map_on is closed under precomposition with continuous real functions.\<close>
            \<comment> \<open>The composition R_to_S1 . (t/n) is continuous UNIV -> S1.\<close>
            have hscale_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                (UNIV::real set) top1_open_sets (\<lambda>t. t / real n)"
            proof -
              have hn_ne: "real n \<noteq> (0::real)" using assms(1) by (by100 simp)
              have hco: "continuous_on (UNIV::real set) (\<lambda>t::real. t / real n)"
                using hn_ne by (intro continuous_intros; by100 blast)
              have hsub: "subspace_topology (UNIV::real set) top1_open_sets (UNIV::real set) = top1_open_sets"
                using subspace_topology_UNIV_self by (by100 blast)
              from top1_continuous_map_on_real_subspace_open_sets[of UNIV "\<lambda>t. t / real n" UNIV] hco
              show ?thesis using hsub by (by100 simp)
            qed
            have hcomp_UNIV: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                top1_S1 top1_S1_topology (top1_R_to_S1 \<circ> (\<lambda>t. t / real n))"
              by (rule top1_continuous_map_on_comp[OF hscale_cont hR_cont])
            from top1_continuous_map_on_restrict_domain_simple[OF hcomp_UNIV subset_UNIV]
            have "top1_continuous_map_on top1_unit_interval
                (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
                top1_S1 top1_S1_topology (top1_R_to_S1 \<circ> (\<lambda>t. t / real n))" .
            hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_S1 top1_S1_topology (top1_R_to_S1 \<circ> (\<lambda>t. t / real n))"
              using hI_eq by (by100 simp)
            thus ?thesis using h\<gamma>_eq by (by100 simp)
          qed
          \<comment> \<open>Compose gamma with iota.\<close>
          have h_comp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              ?A ?TA (\<iota> \<circ> ?\<gamma>)"
            by (rule top1_continuous_map_on_comp[OF h\<gamma>_cmap h\<iota>_cont])
          have h\<alpha>_eq: "(\<iota> \<circ> ?\<gamma>) = ?\<alpha>" by (by100 auto)
          have h\<alpha>_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              ?A ?TA ?\<alpha>"
            using h_comp h\<alpha>_eq by (by100 simp)
          show ?thesis using h\<alpha>_cmap h\<alpha>0 h\<alpha>1
            unfolding top1_is_path_on_def by (by100 blast)
        qed
        show ?thesis using h\<alpha>_cont h\<alpha>0 h\<alpha>1
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      qed
      \<comment> \<open>Step C: The class of alpha generates pi1(A,a), i.e. phi([alpha]) = +/-1.\<close>
      let ?class_\<alpha> = "{g. top1_loop_equiv_on ?A ?TA ?a ?\<alpha> g}"
      have h\<alpha>_gen: "\<phi> ?class_\<alpha> = 1 \<or> \<phi> ?class_\<alpha> = -1"
      proof -
        \<comment> \<open>Get the specific homeomorphism that sends std_loop to alpha.\<close>
        let ?TA_l = "subspace_topology X TX ?A"
        obtain h_circ where hhc: "top1_homeomorphism_on top1_S1 top1_S1_topology ?A ?TA_l h_circ"
            and hhc_10: "h_circ (1, 0) = ?a"
            and hhc_eq: "\<forall>t\<in>top1_unit_interval. h_circ (top1_R_to_S1 t) = q (cos (2*pi*t/real n), sin (2*pi*t/real n))"
          using hA_circle by (by100 blast)
        \<comment> \<open>h_circ . std_loop = alpha on [0,1].\<close>
        have hhc_alpha: "\<forall>t\<in>top1_unit_interval. h_circ (cos (2*pi*t), sin (2*pi*t)) = ?\<alpha> t"
        proof (intro ballI)
          fix t assume ht: "t \<in> top1_unit_interval"
          have "h_circ (cos (2*pi*t), sin (2*pi*t)) = h_circ (top1_R_to_S1 t)"
            unfolding top1_R_to_S1_def by (by100 simp)
          also have "\<dots> = q (cos (2*pi*t/real n), sin (2*pi*t/real n))"
            using hhc_eq ht by (by100 blast)
          also have "\<dots> = \<iota> (cos (2*pi*t/real n), sin (2*pi*t/real n))"
          proof -
            have "(cos (2*pi*t/real n), sin (2*pi*t/real n)) \<in> top1_S1"
              unfolding top1_S1_def by (by100 auto)
            thus ?thesis using h\<iota>_eq by (by100 metis)
          qed
          finally show "h_circ (cos (2*pi*t), sin (2*pi*t)) = ?\<alpha> t" by (by100 simp)
        qed
        \<comment> \<open>h_circ induces iso pi1(S1, (1,0)) -> pi1(A, a) since h_circ(1,0) = a.\<close>
        have hS1_top_l: "is_topology_on top1_S1 top1_S1_topology"
          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hTA_l: "is_topology_on ?A ?TA_l"
          by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
        \<comment> \<open>The induced iso sends [std_loop] to [h_circ . std_loop] = [alpha].\<close>
        \<comment> \<open>Compose phi . (h_circ)*: pi1(S1) -> Z. This is an iso sending [std_loop] to phi([alpha]).\<close>
        \<comment> \<open>By standard_S1_loop_generates_Z: any iso pi1(S1) -> Z maps [std_loop] to +/-1.\<close>
        \<comment> \<open>h_circ induces iso pi1(S1,(1,0)) -> pi1(A,a) with base point h_circ(1,0)=a.\<close>
        have hiso_hc: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_carrier ?A ?TA_l ?a)
            (top1_fundamental_group_mul ?A ?TA_l ?a)"
        proof -
          have "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_carrier ?A ?TA_l (h_circ (1, 0)))
              (top1_fundamental_group_mul ?A ?TA_l (h_circ (1, 0)))"
            by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top_l hTA_l hhc h10_S1]) (by100 simp)
          thus ?thesis using hhc_10 by (by100 simp)
        qed
        \<comment> \<open>Compose with hA_Z to get iso pi1(S1) -> Z.\<close>
        have hcomposed_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            top1_Z_group top1_Z_mul"
          by (rule groups_isomorphic_trans_fwd[OF hiso_hc hA_Z])
        \<comment> \<open>Extract explicit iso psi from the composed iso.\<close>
        obtain \<psi> where h\<psi>: "bij_betw \<psi>
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) top1_Z_group"
            and h\<psi>_hom: "top1_group_hom_on
                (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
                (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
                top1_Z_group top1_Z_mul \<psi>"
            and h\<psi>_std: "\<psi> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                  (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = 1 \<or>
                \<psi> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                  (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = -1"
        proof -
          from hcomposed_iso obtain f where
            hf: "top1_group_iso_on
                (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
                (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
                top1_Z_group top1_Z_mul f"
            unfolding top1_groups_isomorphic_on_def by (by100 blast)
          have hf_bij: "bij_betw f (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) top1_Z_group"
            using hf unfolding top1_group_iso_on_def by (by100 blast)
          have hf_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
              top1_Z_group top1_Z_mul f"
            using hf unfolding top1_group_iso_on_def by (by100 blast)
          from standard_S1_loop_generates_Z[OF hf_bij hf_hom]
          show ?thesis using that[OF hf_bij hf_hom] by (by100 blast)
        qed
        \<comment> \<open>Need: psi([std_loop]) = phi([alpha]).
           Both psi and phi are isos to Z. The composed iso pi1(S1)->pi1(A)->Z has
           psi = phi . h_circ*. Since h_circ* sends [std_loop] to [h_circ.std_loop] = [alpha],
           we get psi([std_loop]) = phi([alpha]).
           But psi is an arbitrary iso from the existential, not the specific composition.
           However, standard_S1_loop_generates_Z tells us ANY iso sends [std_loop] to +/-1.\<close>
        \<comment> \<open>Actually we don't need psi = phi . h_circ*. We just need phi([alpha]) = +/-1.
           Direct: phi is an iso pi1(A,a)->Z. [alpha] generates pi1(A,a) because h_circ sends
           the generator of pi1(S1) to [alpha]. Under any iso to Z, a generator maps to +/-1.\<close>
        \<comment> \<open>More precisely: hiso_hc gives pi1(S1) ~ pi1(A,a). Combined with hA_Z: pi1(A,a) ~ Z.
           The generator of pi1(A,a) is h_circ*([std_loop]) ~ [alpha].
           phi maps generators to +/-1.\<close>
        \<comment> \<open>Key: h_circ*([std_loop]) = [alpha]. Then phi([alpha]) = (phi.h_circ*)([std_loop]) = psi([std_loop]) = +/-1.
           But psi is arbitrary. Instead: CONSTRUCT phi . h_circ* and apply standard_S1_loop_generates_Z.\<close>
        \<comment> \<open>h_circ* is a group hom.\<close>
        have hhc_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA_l h_circ"
          using hhc unfolding top1_homeomorphism_on_def by (by100 blast)
        let ?hc_star = "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0) ?A ?TA_l ?a h_circ"
        \<comment> \<open>h_circ*([std_loop]) = [h_circ . std_loop] = [alpha].\<close>
        have hhc_star_std: "?hc_star {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = ?class_\<alpha>"
        proof -
          \<comment> \<open>By definition, induced_on sends [f] to {g. EX f' in [f]. loop_equiv (h_circ . f') g}.\<close>
          have "?hc_star {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}
            = {g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))) g}"
          proof -
            let ?sl = "\<lambda>s::real. (cos (2*pi*s), sin (2*pi*s))"
            let ?sl_class = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?sl g}"
            \<comment> \<open>By definition: induced_on = {g. EX f' in [sl]. loop_equiv (h_circ . f') g}.\<close>
            have hdef: "?hc_star ?sl_class = {g. \<exists>f' \<in> ?sl_class. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> f') g}"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            \<comment> \<open>std_loop is in its own class.\<close>
            have hsl_in: "?sl \<in> ?sl_class"
              using top1_loop_equiv_on_refl[OF standard_S1_loop_is_loop] by (by100 blast)
            \<comment> \<open>For any f' in [sl], h_circ.f' ~ h_circ.sl (continuous preserves homotopy).\<close>
            have "\<And>f'. f' \<in> ?sl_class \<Longrightarrow>
                {g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> f') g}
                = {g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> ?sl) g}"
            proof -
              fix f' assume hf': "f' \<in> ?sl_class"
              have hf'_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?sl f'"
                using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
              have hf'_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f'"
                using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
              from top1_continuous_preserves_path_homotopy[OF hS1_top_l hhc_cont
                  standard_S1_loop_is_loop hf'_loop hf'_htpy]
              have "top1_path_homotopic_on ?A ?TA_l (h_circ (1,0)) (h_circ (1,0)) (h_circ \<circ> ?sl) (h_circ \<circ> f')" .
              hence "top1_path_homotopic_on ?A ?TA_l ?a ?a (h_circ \<circ> ?sl) (h_circ \<circ> f')"
                using hhc_10 by (by100 simp)
              from path_homotopic_same_class[OF hTA_l this]
              show "{g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> f') g}
                  = {g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> ?sl) g}"
                by (by100 simp)
            qed
            hence "?hc_star ?sl_class = {g. top1_loop_equiv_on ?A ?TA_l ?a (h_circ \<circ> ?sl) g}"
              using hdef hsl_in by (by5000 blast)
            thus ?thesis by (by100 blast)
          qed
          \<comment> \<open>(h_circ . std_loop)(t) = h_circ(cos 2pi*t, sin 2pi*t) = alpha(t) for t in I.\<close>
          also have "\<dots> = ?class_\<alpha>"
          proof -
            \<comment> \<open>h_circ . std_loop and alpha agree on [0,1], hence loop_equiv classes are equal.\<close>
            have "\<And>t. t \<in> top1_unit_interval \<Longrightarrow>
                (h_circ \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))) t = ?\<alpha> t"
              using hhc_alpha by (by100 simp)
            let ?hsl = "h_circ \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
            \<comment> \<open>hsl and alpha agree on [0,1] \<supseteq> I_set.\<close>
            have heq_ext: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> ?hsl t = ?\<alpha> t"
              using hhc_alpha by (by100 simp)
            \<comment> \<open>Preimages agree: {t in I. hsl(t) in U} = {t in I. alpha(t) in U}.\<close>
            have hpre_eq: "\<And>U. {t \<in> top1_unit_interval. ?hsl t \<in> U} = {t \<in> top1_unit_interval. ?\<alpha> t \<in> U}"
              using heq_ext by (by100 auto)
            \<comment> \<open>continuous_map_on for hsl iff for alpha.\<close>
            have hcont_eq: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA_l ?hsl
                \<longleftrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA_l ?\<alpha>"
              unfolding top1_continuous_map_on_def using hpre_eq heq_ext by (by5000 auto)
            \<comment> \<open>path_homotopic for hsl iff for alpha.\<close>
            have hhtpy_eq: "\<And>h. top1_path_homotopic_on ?A ?TA_l ?a ?a ?hsl h
                \<longleftrightarrow> top1_path_homotopic_on ?A ?TA_l ?a ?a ?\<alpha> h"
            proof -
              fix h
              show "top1_path_homotopic_on ?A ?TA_l ?a ?a ?hsl h
                  \<longleftrightarrow> top1_path_homotopic_on ?A ?TA_l ?a ?a ?\<alpha> h"
              proof (rule iffI)
                assume "top1_path_homotopic_on ?A ?TA_l ?a ?a ?hsl h"
                then obtain F where hF: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology ?A ?TA_l F"
                    and "\<forall>s\<in>top1_unit_interval. F (s, 0) = ?hsl s"
                    and "\<forall>s\<in>top1_unit_interval. F (s, 1) = h s"
                    and "\<forall>t\<in>top1_unit_interval. F (0, t) = ?a"
                    and "\<forall>t\<in>top1_unit_interval. F (1, t) = ?a"
                  unfolding top1_path_homotopic_on_def by (by100 blast)
                have "\<forall>s\<in>top1_unit_interval. F (s, 0) = ?\<alpha> s"
                  using \<open>\<forall>s\<in>top1_unit_interval. F (s, 0) = ?hsl s\<close> heq_ext by (by100 simp)
                \<comment> \<open>Also need is_path for alpha and h from the assumption.\<close>
                have "top1_is_path_on ?A ?TA_l ?a ?a ?hsl" and "top1_is_path_on ?A ?TA_l ?a ?a h"
                  using \<open>top1_path_homotopic_on ?A ?TA_l ?a ?a ?hsl h\<close>
                  unfolding top1_path_homotopic_on_def by (by100 blast)+
                have "top1_is_path_on ?A ?TA_l ?a ?a ?\<alpha>"
                  using h\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
                thus "top1_path_homotopic_on ?A ?TA_l ?a ?a ?\<alpha> h"
                  unfolding top1_path_homotopic_on_def
                  using hF \<open>\<forall>s\<in>_. F (s, 0) = ?\<alpha> s\<close> \<open>\<forall>s\<in>_. F (s, 1) = h s\<close>
                    \<open>\<forall>t\<in>_. F (0, t) = ?a\<close> \<open>\<forall>t\<in>_. F (1, t) = ?a\<close> \<open>top1_is_path_on ?A ?TA_l ?a ?a h\<close>
                  by (by100 blast)
              next
                assume "top1_path_homotopic_on ?A ?TA_l ?a ?a ?\<alpha> h"
                then obtain F where hF: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology ?A ?TA_l F"
                    and "\<forall>s\<in>top1_unit_interval. F (s, 0) = ?\<alpha> s"
                    and "\<forall>s\<in>top1_unit_interval. F (s, 1) = h s"
                    and "\<forall>t\<in>top1_unit_interval. F (0, t) = ?a"
                    and "\<forall>t\<in>top1_unit_interval. F (1, t) = ?a"
                  unfolding top1_path_homotopic_on_def by (by100 blast)
                have "\<forall>s\<in>top1_unit_interval. F (s, 0) = ?hsl s"
                  using \<open>\<forall>s\<in>top1_unit_interval. F (s, 0) = ?\<alpha> s\<close> heq_ext by (by100 simp)
                have "top1_is_path_on ?A ?TA_l ?a ?a ?\<alpha>" and "top1_is_path_on ?A ?TA_l ?a ?a h"
                  using \<open>top1_path_homotopic_on ?A ?TA_l ?a ?a ?\<alpha> h\<close>
                  unfolding top1_path_homotopic_on_def by (by100 blast)+
                have "top1_is_path_on ?A ?TA_l ?a ?a ?hsl"
                proof -
                  have hcont_hsl: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA_l ?hsl"
                    using hcont_eq \<open>top1_is_path_on ?A ?TA_l ?a ?a ?\<alpha>\<close>
                    unfolding top1_is_path_on_def by (by100 blast)
                  have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                  have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                  have h0: "?hsl 0 = ?a"
                  proof -
                    have "?hsl 0 = ?\<alpha> 0" using heq_ext h0_I by (by100 blast)
                    also have "?\<alpha> 0 = ?a" using \<open>top1_is_path_on ?A ?TA_l ?a ?a ?\<alpha>\<close>
                      unfolding top1_is_path_on_def by (by100 simp)
                    finally show ?thesis .
                  qed
                  have h1: "?hsl 1 = ?a"
                  proof -
                    have "?hsl 1 = ?\<alpha> 1" using heq_ext h1_I by (by100 blast)
                    also have "?\<alpha> 1 = ?a" using \<open>top1_is_path_on ?A ?TA_l ?a ?a ?\<alpha>\<close>
                      unfolding top1_is_path_on_def by (by100 simp)
                    finally show ?thesis .
                  qed
                  show ?thesis using hcont_hsl h0 h1
                    unfolding top1_is_path_on_def by (by100 blast)
                qed
                thus "top1_path_homotopic_on ?A ?TA_l ?a ?a ?hsl h"
                  unfolding top1_path_homotopic_on_def
                  using hF \<open>\<forall>s\<in>_. F (s, 0) = ?hsl s\<close> \<open>\<forall>s\<in>_. F (s, 1) = h s\<close>
                    \<open>\<forall>t\<in>_. F (0, t) = ?a\<close> \<open>\<forall>t\<in>_. F (1, t) = ?a\<close> \<open>top1_is_path_on ?A ?TA_l ?a ?a h\<close>
                  by (by100 blast)
              qed
            qed
            \<comment> \<open>is_loop for hsl iff is_loop for alpha.\<close>
            have hloop_eq: "top1_is_loop_on ?A ?TA_l ?a ?hsl \<longleftrightarrow> top1_is_loop_on ?A ?TA_l ?a ?\<alpha>"
            proof -
              have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
              have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
              have "?hsl 0 = ?\<alpha> 0" using heq_ext h0_I by (by100 blast)
              moreover have "?hsl 1 = ?\<alpha> 1" using heq_ext h1_I by (by100 blast)
              ultimately show ?thesis
                unfolding top1_is_loop_on_def top1_is_path_on_def
                using hcont_eq by (by5000 auto)
            qed
            \<comment> \<open>Combine: loop_equiv for hsl iff for alpha.\<close>
            hence "\<And>g. top1_loop_equiv_on ?A ?TA_l ?a ?hsl g
                \<longleftrightarrow> top1_loop_equiv_on ?A ?TA_l ?a ?\<alpha> g"
              unfolding top1_loop_equiv_on_def
              using hloop_eq hhtpy_eq by (by5000 blast)
            thus ?thesis by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>phi . h_circ* : pi1(S1) -> Z is bij + hom.\<close>
        let ?\<psi>_explicit = "\<phi> \<circ> ?hc_star"
        \<comment> \<open>Get the induced iso from h_circ.\<close>
        \<comment> \<open>h_circ is homeomorphism, hence homotopy equivalence. By Theorem_58_7, induced map is iso.\<close>
        have hhc_htpy_eq: "top1_homotopy_equivalence_on top1_S1 top1_S1_topology ?A ?TA_l h_circ
            (inv_into top1_S1 h_circ)"
          unfolding top1_homotopy_equivalence_on_def
        proof (intro conjI)
          show "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA_l h_circ"
            using hhc_cont by (by100 blast)
        next
          show "top1_continuous_map_on ?A ?TA_l top1_S1 top1_S1_topology (inv_into top1_S1 h_circ)"
            using hhc unfolding top1_homeomorphism_on_def by (by100 blast)
        next
          \<comment> \<open>inv . h = id on S1.\<close>
          show "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
              (inv_into top1_S1 h_circ \<circ> h_circ) (\<lambda>x. x)"
          proof -
            have "\<forall>x \<in> top1_S1. (inv_into top1_S1 h_circ \<circ> h_circ) x = x"
            proof
              fix x assume "x \<in> top1_S1"
              thus "(inv_into top1_S1 h_circ \<circ> h_circ) x = x"
                using hhc inv_into_f_f
                unfolding top1_homeomorphism_on_def bij_betw_def by (by5000 simp)
            qed
            hence heq: "\<And>x. x \<in> top1_S1 \<Longrightarrow> (inv_into top1_S1 h_circ \<circ> h_circ) x = (\<lambda>x. x) x"
              by (by100 simp)
            \<comment> \<open>id is continuous S1 -> S1.\<close>
            have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>x. x)"
              using top1_continuous_map_on_id[OF hS1_top_l] unfolding id_def by (by100 blast)
            \<comment> \<open>By Lemma_51_1_homotopic_refl: id ~ id.\<close>
            from Lemma_51_1_homotopic_refl[OF hid_cont hS1_top_l]
            have "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>x. x) (\<lambda>x. x)" .
            \<comment> \<open>Since inv.h = id on S1, the homotopy also works for inv.h.\<close>
            \<comment> \<open>Direct: the constant homotopy H(x,t)=x satisfies H(x,0)=(inv.h)(x)=x and H(x,1)=x.\<close>
            show ?thesis unfolding top1_homotopic_on_def
            proof (intro conjI)
              have hinv_cont: "top1_continuous_map_on ?A ?TA_l top1_S1 top1_S1_topology (inv_into top1_S1 h_circ)"
                using hhc unfolding top1_homeomorphism_on_def by (by100 blast)
              show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (inv_into top1_S1 h_circ \<circ> h_circ)"
                by (rule top1_continuous_map_on_comp[OF hhc_cont hinv_cont])
            next
              show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>x. x)"
                by (rule hid_cont)
            next
              \<comment> \<open>Constant homotopy: F(x,t) = x.\<close>
              have "top1_continuous_map_on (top1_S1 \<times> top1_unit_interval)
                  (product_topology_on top1_S1_topology top1_unit_interval_topology) top1_S1 top1_S1_topology (\<lambda>p. fst p)"
                using homotopy_const_continuous[OF hid_cont hS1_top_l] by (by100 simp)
              moreover have "\<forall>x\<in>top1_S1. fst (x, (0::real)) = (inv_into top1_S1 h_circ \<circ> h_circ) x"
                using heq by (by100 simp)
              moreover have "\<forall>x\<in>top1_S1. fst (x, (1::real)) = x" by (by100 simp)
              ultimately show "\<exists>F. top1_continuous_map_on (top1_S1 \<times> top1_unit_interval)
                  (product_topology_on top1_S1_topology top1_unit_interval_topology) top1_S1 top1_S1_topology F
                \<and> (\<forall>x\<in>top1_S1. F (x, 0) = (inv_into top1_S1 h_circ \<circ> h_circ) x)
                \<and> (\<forall>x\<in>top1_S1. F (x, 1) = x)"
                by (by100 blast)
            qed
          qed
        next
          \<comment> \<open>h . inv = id on A.\<close>
          show "top1_homotopic_on ?A ?TA_l ?A ?TA_l
              (h_circ \<circ> inv_into top1_S1 h_circ) (\<lambda>y. y)"
          proof -
            have hbij: "bij_betw h_circ top1_S1 ?A"
              using hhc unfolding top1_homeomorphism_on_def by (by100 blast)
            have heqA: "\<forall>y \<in> ?A. (h_circ \<circ> inv_into top1_S1 h_circ) y = y"
            proof
              fix y assume "y \<in> ?A"
              thus "(h_circ \<circ> inv_into top1_S1 h_circ) y = y"
                using hbij f_inv_into_f[of y h_circ top1_S1]
                unfolding bij_betw_def by (by5000 simp)
            qed
            have hidA: "top1_continuous_map_on ?A ?TA_l ?A ?TA_l (\<lambda>y. y)"
              using top1_continuous_map_on_id[OF hTA_l] unfolding id_def by (by100 blast)
            have hcomp_cont: "top1_continuous_map_on ?A ?TA_l ?A ?TA_l (h_circ \<circ> inv_into top1_S1 h_circ)"
            proof -
              have "top1_continuous_map_on ?A ?TA_l top1_S1 top1_S1_topology (inv_into top1_S1 h_circ)"
                using hhc unfolding top1_homeomorphism_on_def by (by100 blast)
              thus ?thesis by (rule top1_continuous_map_on_comp[OF _ hhc_cont])
            qed
            \<comment> \<open>Constant homotopy: F(y,t) = y.\<close>
            have "top1_continuous_map_on (?A \<times> top1_unit_interval)
                (product_topology_on ?TA_l top1_unit_interval_topology) ?A ?TA_l (\<lambda>p. fst p)"
              using homotopy_const_continuous[OF hidA hTA_l] by (by100 simp)
            moreover have "\<forall>y\<in>?A. fst (y, (0::real)) = (h_circ \<circ> inv_into top1_S1 h_circ) y"
              using heqA by (by100 simp)
            moreover have "\<forall>y\<in>?A. fst (y, (1::real)) = y" by (by100 simp)
            ultimately show ?thesis unfolding top1_homotopic_on_def
              using hcomp_cont hidA by (by100 blast)
          qed
        qed
        have "h_circ (1, 0) = ?a" by (rule hhc_10)
        have hhc_iso: "top1_group_iso_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_carrier ?A ?TA_l ?a)
            (top1_fundamental_group_mul ?A ?TA_l ?a)
            (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0) ?A ?TA_l ?a h_circ)"
        proof -
          from Theorem_58_7[OF hS1_top_l hTA_l hhc_htpy_eq h10_S1]
          show ?thesis using hhc_10 by (by100 simp)
        qed
        have hhc_iso2: "top1_group_iso_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
            ?GA ?mulA ?hc_star"
          using hhc_iso by (by100 blast)
        have hgrpA_loc2: "top1_is_group_on ?GA ?mulA ?eA ?invA"
          by (rule top1_fundamental_group_is_group[OF hTA_l ha_A])
        have hgrpS1: "top1_is_group_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
            (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))"
          by (rule top1_fundamental_group_is_group[OF hS1_top_l h10_S1])
        have h\<psi>e_iso: "top1_group_iso_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            top1_Z_group top1_Z_mul ?\<psi>_explicit"
        proof -
          have hgrpZ2: "top1_is_group_on top1_Z_group top1_Z_mul (0::int) uminus"
          proof -
            have "top1_Z_id = (0::int)" unfolding top1_Z_id_def by (by100 blast)
            moreover have "top1_Z_invg = (uminus :: int \<Rightarrow> int)" unfolding top1_Z_invg_def by (by100 blast)
            ultimately show ?thesis
              using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 simp)
          qed
          show ?thesis
            by (rule group_iso_on_compose[OF hhc_iso2 h\<phi>_iso hgrpS1 hgrpA_loc2 hgrpZ2])
        qed
        have h\<psi>e_bij: "bij_betw ?\<psi>_explicit
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            top1_Z_group"
          using h\<psi>e_iso unfolding top1_group_iso_on_def by (by100 blast)
        have h\<psi>e_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            top1_Z_group top1_Z_mul ?\<psi>_explicit"
          using h\<psi>e_iso unfolding top1_group_iso_on_def by (by100 blast)
        from standard_S1_loop_generates_Z[OF h\<psi>e_bij h\<psi>e_hom]
        have "?\<psi>_explicit {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = 1 \<or>
            ?\<psi>_explicit {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = -1" .
        hence "\<phi> (?hc_star {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}) = 1 \<or>
            \<phi> (?hc_star {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}) = -1"
          by (by100 simp)
        thus ?thesis using hhc_star_std by (by100 simp)
      qed
      \<comment> \<open>Step D: The induced map of iota sends [std S1 loop] to [alpha]^n in pi1(A,a).
         The standard S1 loop t -> (cos(2*pi*t), sin(2*pi*t)) composed with iota
         gives t -> iota(cos(2*pi*t), sin(2*pi*t)) which equals alpha composed n times
         (up to path homotopy).\<close>
      have h_relator_is_alpha_n: "?relator = top1_group_pow ?mulA ?eA ?class_\<alpha> n"
      proof -
        \<comment> \<open>Following Munkres: iota . (std S1 loop) decomposes as alpha^n.
           For t in [k/n, (k+1)/n], the std loop at t is a rotation of gamma(nt-k).
           Since q identifies rotations, q . (std loop) restricted to each piece equals alpha reparametrized.
           So iota . (std loop) is path-homotopic to alpha * alpha * ... * alpha (n times).\<close>
        have hTA_loc: "is_topology_on ?A ?TA" by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
        let ?std_loop = "\<lambda>s::real. (cos (2*pi*s), sin (2*pi*s))"
        let ?\<iota>_loop = "\<lambda>s. \<iota> (?std_loop s)"
        \<comment> \<open>Step D.1: iota . std_loop is path-homotopic to the n-fold product of alpha in A.\<close>
        have h_htpy: "top1_path_homotopic_on ?A ?TA ?a ?a ?\<iota>_loop
            (top1_path_power ?\<alpha> ?a n)"
        proof (cases "n = 1")
          case True
          \<comment> \<open>For n=1: alpha(t) = iota(cos(2*pi*t), sin(2*pi*t)) = iota_loop(t).
             path_power alpha a 1 = path_product alpha (const a).
             By right identity (symmetric): alpha ~ path_product alpha (const a).\<close>
          have heq_n1: "?\<alpha> = ?\<iota>_loop"
          proof (rule ext)
            fix t :: real show "?\<alpha> t = ?\<iota>_loop t" using True by (by100 simp)
          qed
          have "top1_is_path_on ?A ?TA ?a ?a ?\<alpha>"
            using h\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
          from Theorem_51_2_right_identity[OF hTA_loc this]
          have "top1_path_homotopic_on ?A ?TA ?a ?a (top1_path_product ?\<alpha> (top1_constant_path ?a)) ?\<alpha>" .
          from Lemma_51_1_path_homotopic_sym[OF this]
          have "top1_path_homotopic_on ?A ?TA ?a ?a ?\<alpha> (top1_path_product ?\<alpha> (top1_constant_path ?a))" .
          hence "top1_path_homotopic_on ?A ?TA ?a ?a ?\<iota>_loop (top1_path_power ?\<alpha> ?a 1)"
            using heq_n1 by (by100 simp)
          thus ?thesis using True by (by100 simp)
        next
          case False
          hence hn_ge2: "n \<ge> 2" using assms(1) by (by100 linarith)
          \<comment> \<open>Key property: iota_loop has quasi-period 1/n under q-identification.
             iota_loop(t + 1/n) = q(cos(2*pi*(t+1/n)), sin(...)) = q(cos(2*pi*t + 2*pi/n), sin(...))
             = q(cos(2*pi*t), sin(2*pi*t)) = iota_loop(t) by rotation identification.\<close>
          have hf_period: "\<forall>t. ?\<iota>_loop (t + 1/real n) = ?\<iota>_loop t"
          proof (intro allI)
            fix t :: real
            \<comment> \<open>iota_loop(t + 1/n) = iota(cos(2*pi*(t+1/n)), sin(2*pi*(t+1/n)))
               = q(cos(2*pi*t + 2*pi/n), sin(2*pi*t + 2*pi/n)).
               The point (cos(2*pi*t + 2*pi/n), sin(...)) is rotation_1 of (cos(2*pi*t), sin(2*pi*t)).
               By hq_S1: q identifies rotations. So q(rot_1(z)) = q(z) for z in S1.\<close>
            have "(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) \<in> top1_S1"
              unfolding top1_S1_def by (by100 auto)
            have "(cos (2*pi*t), sin (2*pi*t)) \<in> top1_S1"
              unfolding top1_S1_def by (by100 auto)
            \<comment> \<open>The shifted point = rotation_1 of original.\<close>
            have h_rot: "(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) =
                (cos (2*pi*real 1/real n) * cos (2*pi*t) - sin (2*pi*real 1/real n) * sin (2*pi*t),
                 sin (2*pi*real 1/real n) * cos (2*pi*t) + cos (2*pi*real 1/real n) * sin (2*pi*t))"
              using cos_add[of "2*pi*t" "2*pi*real 1/real n"] sin_add[of "2*pi*t" "2*pi*real 1/real n"]
              by (by100 simp)
            \<comment> \<open>By hq_S1: q identifies this rotation (k=1 < n).\<close>
            have "1 < n" using hn_ge2 by (by100 linarith)
            have "q (cos (2*pi*t), sin (2*pi*t)) = q (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))"
            proof -
              have "(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) =
                  (cos (2*pi*real 1/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                  - sin (2*pi*real 1/real n) * snd (cos (2*pi*t), sin (2*pi*t)),
                   sin (2*pi*real 1/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                  + cos (2*pi*real 1/real n) * snd (cos (2*pi*t), sin (2*pi*t)))"
                using h_rot by (by100 simp)
              hence "\<exists>k::nat. k < n \<and> (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) =
                  (cos (2*pi*real k/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                  - sin (2*pi*real k/real n) * snd (cos (2*pi*t), sin (2*pi*t)),
                   sin (2*pi*real k/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                  + cos (2*pi*real k/real n) * snd (cos (2*pi*t), sin (2*pi*t)))"
              proof -
                have "(1::nat) < n" using \<open>1 < n\<close> by (by100 blast)
                moreover have "(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) =
                    (cos (2*pi*real (1::nat)/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                    - sin (2*pi*real (1::nat)/real n) * snd (cos (2*pi*t), sin (2*pi*t)),
                     sin (2*pi*real (1::nat)/real n) * fst (cos (2*pi*t), sin (2*pi*t))
                    + cos (2*pi*real (1::nat)/real n) * snd (cos (2*pi*t), sin (2*pi*t)))"
                  using h_rot by (by100 simp)
                ultimately show ?thesis by (by100 blast)
              qed
              thus ?thesis
                using hq_S1[rule_format, OF \<open>(cos (2*pi*t), sin (2*pi*t)) \<in> top1_S1\<close>
                      \<open>(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) \<in> top1_S1\<close>]
                by (by100 blast)
            qed
            \<comment> \<open>Since iota = q on S1:\<close>
            have hq_eq: "q (cos (2*pi*t), sin (2*pi*t)) = q (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))"
              using \<open>q (cos (2*pi*t), sin (2*pi*t)) = q (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))\<close> .
            have h\<iota>1: "\<iota> (cos (2*pi*t), sin (2*pi*t)) = q (cos (2*pi*t), sin (2*pi*t))"
              using h\<iota>_eq \<open>(cos (2*pi*t), sin (2*pi*t)) \<in> top1_S1\<close> by (by100 blast)
            have h\<iota>2: "\<iota> (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) = q (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))"
              using h\<iota>_eq \<open>(cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n)) \<in> top1_S1\<close> by (by100 metis)
            have h_angle_eq: "2*pi*t + 2*pi/real n = 2*pi*(t + 1/real n)"
              using assms(1) by (simp add: field_simps)
            have "?\<iota>_loop t = q (cos (2*pi*t), sin (2*pi*t))" using h\<iota>1 by (by100 simp)
            also have "\<dots> = q (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))" by (rule hq_eq)
            also have "\<dots> = \<iota> (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))" using h\<iota>2 by (by100 simp)
            finally have "?\<iota>_loop t = \<iota> (cos (2*pi*t + 2*pi/real n), sin (2*pi*t + 2*pi/real n))" .
            hence "?\<iota>_loop t = ?\<iota>_loop (t + 1/real n)" using h_angle_eq by (by100 simp)
            thus "?\<iota>_loop (t + 1/real n) = ?\<iota>_loop t" by (by100 simp)
          qed
          \<comment> \<open>alpha(t) = iota_loop(t/n) since alpha(t) = q(cos(2*pi*t/n),...) = iota_loop(t/n).\<close>
          have h\<alpha>_eq_f: "\<forall>t \<in> top1_unit_interval. ?\<alpha> t = ?\<iota>_loop (t / real n)"
          proof (intro ballI)
            fix t :: real assume "t \<in> top1_unit_interval"
            show "?\<alpha> t = ?\<iota>_loop (t / real n)" by (by100 simp)
          qed
          \<comment> \<open>path_power alpha n = iota_loop . psi_n where psi_n is the binary-tree reparametrization.
             By reparam_path_homotopy: iota_loop . id ~ iota_loop . psi_n.\<close>
          \<comment> \<open>Construct reparametrization psi_n by recursion:
             psi_0(t) = 0
             psi_{m+1}(t) = 2t/n for t in [0,1/2], psi_m(2t-1) + 1/n for t in [1/2,1].
             Then f(psi_n(t)) = path_power alpha a n (t) by induction using hf_period.
             Apply reparam_path_homotopy: f . id ~ f . psi_n.\<close>
          \<comment> \<open>Key: f(psi_m(2t-1) + 1/n) = f(psi_m(2t-1)) by hf_period.
             So f(psi_{m+1}(t)) = alpha(2t) for t<=1/2, path_power m (2t-1) for t>1/2
             = path_power (m+1) (t).\<close>
          \<comment> \<open>Prove by induction: for all m, there exists continuous psi_m: I -> [0, m/n]
             with psi_m(0)=0, psi_m(1)=m/n, and iota_loop . psi_m = path_power alpha a m on I.
             At m=n: psi_n maps to [0,1], and by reparam_path_homotopy: iota_loop ~ path_power alpha n.\<close>
          have hind: "\<forall>m \<le> n. \<exists>\<psi>. (\<forall>t\<in>top1_unit_interval. \<psi> t \<ge> 0 \<and> \<psi> t \<le> real m / real n)
              \<and> \<psi> 0 = 0 \<and> \<psi> 1 = real m / real n
              \<and> (\<forall>t\<in>top1_unit_interval. ?\<iota>_loop (\<psi> t) = top1_path_power ?\<alpha> ?a m t)
              \<and> continuous_on top1_unit_interval \<psi>"
          proof (intro allI impI)
            fix m assume "m \<le> n"
            show "\<exists>\<psi>. (\<forall>t\<in>top1_unit_interval. \<psi> t \<ge> 0 \<and> \<psi> t \<le> real m / real n)
                \<and> \<psi> 0 = 0 \<and> \<psi> 1 = real m / real n
                \<and> (\<forall>t\<in>top1_unit_interval. ?\<iota>_loop (\<psi> t) = top1_path_power ?\<alpha> ?a m t)
                \<and> continuous_on top1_unit_interval \<psi>"
            proof (induct m)
              case 0
              \<comment> \<open>psi_0 = const 0. iota_loop(0) = a = path_power 0 t.\<close>
              have hf0: "?\<iota>_loop 0 = ?a" using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
              have hpp0: "\<And>t. top1_path_power ?\<alpha> ?a 0 t = ?a"
                by (simp add: top1_constant_path_def)
              show ?case
                apply (rule exI[of _ "\<lambda>_. 0"])
                using hf0 hpp0 by (intro conjI; by100 auto)
            next
              case (Suc m)
              \<comment> \<open>Given psi_m, define psi_{m+1}(t) = 2t/n for t<=1/2, psi_m(2t-1)+1/n for t>1/2.\<close>
              from Suc obtain \<psi>m where
                  h\<psi>m_range: "\<forall>t\<in>top1_unit_interval. \<psi>m t \<ge> 0 \<and> \<psi>m t \<le> real m / real n"
                  and h\<psi>m_0: "\<psi>m 0 = 0" and h\<psi>m_1: "\<psi>m 1 = real m / real n"
                  and h\<psi>m_eq: "\<forall>t\<in>top1_unit_interval. ?\<iota>_loop (\<psi>m t) = top1_path_power ?\<alpha> ?a m t"
                  and h\<psi>m_cont: "continuous_on top1_unit_interval \<psi>m"
                by (by100 blast)
              let ?\<psi>s = "\<lambda>t::real. if t \<le> 1/2 then 2*t / real n else \<psi>m (2*t - 1) + 1 / real n"
              \<comment> \<open>Verification: f(psi_s(t)) = path_power alpha (Suc m) t.\<close>
              have h_eq_new: "\<forall>t\<in>top1_unit_interval. ?\<iota>_loop (?\<psi>s t) = top1_path_power ?\<alpha> ?a (Suc m) t"
              proof (intro ballI)
                fix t :: real assume ht: "t \<in> top1_unit_interval"
                show "?\<iota>_loop (?\<psi>s t) = top1_path_power ?\<alpha> ?a (Suc m) t"
                proof (cases "t \<le> 1/2")
                  case True
                  \<comment> \<open>psi_s(t) = 2t/n. iota_loop(2t/n) = alpha(2t) by h_alpha_eq_f.\<close>
                  have "?\<iota>_loop (?\<psi>s t) = ?\<iota>_loop (2*t / real n)" using True by (by100 simp)
                  also have "\<dots> = ?\<alpha> (2*t)"
                  proof -
                    have "2*t \<in> top1_unit_interval" using ht True
                      unfolding top1_unit_interval_def by (by100 auto)
                    from h\<alpha>_eq_f[rule_format, OF this]
                    show ?thesis by (by100 simp)
                  qed
                  finally have "?\<iota>_loop (?\<psi>s t) = ?\<alpha> (2*t)" .
                  \<comment> \<open>path_power (Suc m) at t<=1/2 = alpha(2t).\<close>
                  moreover have "top1_path_power ?\<alpha> ?a (Suc m) t = ?\<alpha> (2*t)"
                  proof -
                    have "top1_path_power ?\<alpha> ?a (Suc m) t = top1_path_product ?\<alpha> (top1_path_power ?\<alpha> ?a m) t"
                      by (by100 simp)
                    also have "\<dots> = ?\<alpha> (2*t)" using True unfolding top1_path_product_def by (by100 simp)
                    finally show ?thesis .
                  qed
                  ultimately show ?thesis by (by100 simp)
                next
                  case False
                  hence ht2: "t > 1/2" by (by100 linarith)
                  \<comment> \<open>psi_s(t) = psi_m(2t-1) + 1/n.\<close>
                  have "?\<iota>_loop (?\<psi>s t) = ?\<iota>_loop (\<psi>m (2*t - 1) + 1/real n)"
                    using ht2 by (by100 simp)
                  also have "\<dots> = ?\<iota>_loop (\<psi>m (2*t - 1))"
                    using hf_period by (by100 metis)
                  also have "\<dots> = top1_path_power ?\<alpha> ?a m (2*t - 1)"
                  proof -
                    have "2*t - 1 \<in> top1_unit_interval"
                      using ht ht2 unfolding top1_unit_interval_def by (by100 auto)
                    thus ?thesis using h\<psi>m_eq by (by100 blast)
                  qed
                  finally have "?\<iota>_loop (?\<psi>s t) = top1_path_power ?\<alpha> ?a m (2*t - 1)" .
                  \<comment> \<open>path_power (Suc m) at t>1/2 = path_power m (2t-1).\<close>
                  moreover have "top1_path_power ?\<alpha> ?a (Suc m) t = top1_path_power ?\<alpha> ?a m (2*t - 1)"
                  proof -
                    have "top1_path_power ?\<alpha> ?a (Suc m) t = top1_path_product ?\<alpha> (top1_path_power ?\<alpha> ?a m) t"
                      by (by100 simp)
                    also have "\<dots> = top1_path_power ?\<alpha> ?a m (2*t - 1)"
                      using ht2 unfolding top1_path_product_def by (by100 simp)
                    finally show ?thesis .
                  qed
                  ultimately show ?thesis by (by100 simp)
                qed
              qed
              have h_range_new: "\<forall>t\<in>top1_unit_interval. ?\<psi>s t \<ge> 0 \<and> ?\<psi>s t \<le> real (Suc m) / real n"
              proof (intro ballI conjI)
                fix t :: real assume ht: "t \<in> top1_unit_interval"
                have hn_pos: "real n > 0" using assms(1) by (by100 simp)
                show "?\<psi>s t \<ge> 0"
                proof (cases "t \<le> 1/2")
                  case True thus ?thesis using hn_pos ht unfolding top1_unit_interval_def by (by100 auto)
                next
                  case False
                  have "2*t-1 \<in> top1_unit_interval" using ht False unfolding top1_unit_interval_def by (by100 auto)
                  thus ?thesis using h\<psi>m_range False hn_pos by (by100 auto)
                qed
                show "?\<psi>s t \<le> real (Suc m) / real n"
                proof (cases "t \<le> 1/2")
                  case True
                  have "2*t \<le> 1" using True by (by100 linarith)
                  hence "2*t/real n \<le> 1/real n" using hn_pos
                    by (metis divide_right_mono less_imp_le)
                  also have "\<dots> \<le> real (Suc m) / real n"
                  proof -
                    have "(1::real) \<le> real (Suc m)" by (by100 simp)
                    thus ?thesis using hn_pos by (metis divide_right_mono less_imp_le)
                  qed
                  finally show ?thesis using True by (by100 simp)
                next
                  case False
                  have "2*t-1 \<in> top1_unit_interval" using ht False unfolding top1_unit_interval_def by (by100 auto)
                  hence "\<psi>m (2*t-1) \<le> real m / real n" using h\<psi>m_range by (by100 blast)
                  hence "\<psi>m (2*t-1) + 1/real n \<le> real m / real n + 1/real n" by (by100 linarith)
                  also have "\<dots> = real (Suc m) / real n" using hn_pos assms(1) by (simp add: field_simps)
                  finally show ?thesis using False by (by100 simp)
                qed
              qed
              have h_endpts: "?\<psi>s 0 = 0 \<and> ?\<psi>s 1 = real (Suc m) / real n"
                using h\<psi>m_1 assms(1) by (simp add: field_simps)
              have h_cont_new: "continuous_on top1_unit_interval ?\<psi>s"
              proof -
                have hn_ne: "real n \<noteq> (0::real)" using assms(1) by (by100 simp)
                \<comment> \<open>Left piece: continuous on {0..1/2}.\<close>
                let ?f = "\<lambda>t::real. 2*t / real n"
                let ?g = "\<lambda>t::real. \<psi>m (2*t - 1) + 1 / real n"
                have hc_f: "continuous_on {0..1/2} ?f"
                  using hn_ne by (intro continuous_intros; by100 blast)
                \<comment> \<open>Right piece: continuous on {1/2..1}.\<close>
                have hc_g: "continuous_on {1/2..1} ?g"
                proof -
                  have hc_lin: "continuous_on {1/2..1::real} (\<lambda>t. 2*t - 1)" by (intro continuous_intros)
                  have himg: "(\<lambda>t::real. 2*t - 1) ` {1/2..1} \<subseteq> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 auto)
                  have "continuous_on {1/2..1} (\<lambda>t. \<psi>m (2*t - 1))"
                    by (rule continuous_on_compose2[OF h\<psi>m_cont hc_lin himg])
                  thus ?thesis by (intro continuous_intros)
                qed
                \<comment> \<open>Matching at t=1/2: f(1/2) = 1/n = g(1/2).\<close>
                have hmatch: "\<forall>t. (t \<in> {0..1/2} \<and> \<not> t \<le> 1/2) \<or> (t \<in> {1/2..1} \<and> t \<le> 1/2)
                    \<longrightarrow> ?f t = ?g t"
                proof (intro allI impI)
                  fix t :: real assume "(t \<in> {0..1/2} \<and> \<not> t \<le> 1/2) \<or> (t \<in> {1/2..1} \<and> t \<le> 1/2)"
                  hence ht: "t = 1/2" by (by100 auto)
                  have "?f t = 1 / real n" using ht by (by100 simp)
                  also have "\<dots> = ?g t"
                  proof -
                    have "2*t - 1 = 0" using ht by (by100 simp)
                    thus ?thesis using h\<psi>m_0 by (by100 simp)
                  qed
                  finally show "?f t = ?g t" .
                qed
                \<comment> \<open>Combine via continuous_on_cases.\<close>
                have "top1_unit_interval = {0..1/2::real} \<union> {1/2..1}"
                  unfolding top1_unit_interval_def by (by100 auto)
                moreover have "closed {0..1/2::real}" by (by100 auto)
                moreover have "closed {1/2..1::real}" by (by100 auto)
                ultimately show ?thesis
                  using continuous_on_cases[OF \<open>closed {0..1/2}\<close> \<open>closed {1/2..1}\<close> hc_f hc_g hmatch]
                  by (by100 simp)
              qed
              show ?case
                apply (rule exI[of _ ?\<psi>s])
                using h_range_new h_endpts h_eq_new h_cont_new by (by100 blast)
            qed
          qed
          \<comment> \<open>At m=n: obtain psi_n with iota_loop . psi_n = path_power alpha n.\<close>
          have hn_div: "real n / real n = (1::real)" using assms(1) by (by100 simp)
          from hind[rule_format, of n]
          obtain \<psi> where h\<psi>_range_raw: "\<forall>t\<in>top1_unit_interval. \<psi> t \<ge> 0 \<and> \<psi> t \<le> real n / real n"
              and h\<psi>_0: "\<psi> 0 = 0" and h\<psi>_1_raw: "\<psi> 1 = real n / real n"
              and h\<psi>_eq: "\<forall>t\<in>top1_unit_interval. ?\<iota>_loop (\<psi> t) = top1_path_power ?\<alpha> ?a n t"
              and h\<psi>_cont: "continuous_on top1_unit_interval \<psi>"
            by (by100 blast)
          have h\<psi>_range: "\<forall>t\<in>top1_unit_interval. \<psi> t \<ge> 0 \<and> \<psi> t \<le> 1"
            using h\<psi>_range_raw hn_div by (by100 simp)
          have h\<psi>_1: "\<psi> 1 = 1" using h\<psi>_1_raw hn_div by (by100 simp)
          \<comment> \<open>Apply reparam_path_homotopy: iota_loop . id ~ iota_loop . psi.\<close>
          \<comment> \<open>Apply reparam_path_homotopy with f=iota_loop, phi=id, psi=our psi.\<close>
          \<comment> \<open>Need: continuous_map_on versions of f, id, and psi.\<close>
          have hf_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              X TX ?\<iota>_loop"
          proof -
            \<comment> \<open>std_loop: I -> S1 continuous.\<close>
            have hsl_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_S1 top1_S1_topology (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
              using standard_S1_loop_is_loop unfolding top1_is_loop_on_def top1_is_path_on_def
              by (by100 blast)
            \<comment> \<open>iota: S1 -> A continuous. Lift to X.\<close>
            have h\<iota>_img_X: "\<iota> ` top1_S1 \<subseteq> X"
              using h\<iota>_cont hA_sub unfolding top1_continuous_map_on_def by (by100 blast)
            have h\<iota>_X: "top1_continuous_map_on top1_S1 top1_S1_topology X TX \<iota>"
            proof -
              from top1_continuous_map_on_codomain_enlarge[OF h\<iota>_cont hA_sub]
              have "top1_continuous_map_on top1_S1 top1_S1_topology X (subspace_topology X TX X) \<iota>"
                by (by100 blast)
              moreover have "subspace_topology X TX X = TX"
              proof -
                have "\<forall>U \<in> TX. U \<subseteq> X"
                  using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
                thus ?thesis by (rule subspace_topology_self)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>Compose: iota . std_loop : I -> X.\<close>
            have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (\<iota> \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
              by (rule top1_continuous_map_on_comp[OF hsl_cont h\<iota>_X])
            moreover have "(\<iota> \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))) = ?\<iota>_loop" by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          have h\<psi>_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              top1_unit_interval top1_unit_interval_topology \<psi>"
          proof -
            have h\<psi>_img: "\<forall>t\<in>top1_unit_interval. \<psi> t \<in> top1_unit_interval"
              using h\<psi>_range unfolding top1_unit_interval_def by (by100 auto)
            have "top1_unit_interval_topology = subspace_topology UNIV top1_open_sets top1_unit_interval"
              unfolding top1_unit_interval_topology_def by (by100 blast)
            thus ?thesis
              using top1_continuous_map_on_subspace_open_sets_on[of top1_unit_interval \<psi> top1_unit_interval]
                    h\<psi>_img h\<psi>_cont by (by5000 simp)
          qed
          have hid_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              top1_unit_interval top1_unit_interval_topology (\<lambda>t. t)"
          proof -
            have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
              unfolding top1_unit_interval_topology_def
              by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
                (by100 blast)
            from top1_continuous_map_on_id[OF hI_top] show ?thesis unfolding id_def by (by100 blast)
          qed
          have hf_img: "\<forall>s\<in>top1_unit_interval. ?\<iota>_loop s \<in> ?A"
          proof (intro ballI)
            fix s assume "s \<in> top1_unit_interval"
            have "(cos (2*pi*s), sin (2*pi*s)) \<in> top1_S1" unfolding top1_S1_def by (by100 auto)
            thus "?\<iota>_loop s \<in> ?A" using h\<iota>_cont unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have hf_0: "?\<iota>_loop 0 = ?a"
            using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
          have hf_1: "?\<iota>_loop 1 = ?a"
          proof -
            have "(cos (2*pi*1), sin (2*pi*1)) = ((1::real), 0)" by (by100 simp)
            thus ?thesis using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
          qed
          \<comment> \<open>By reparam_path_homotopy: iota_loop . id ~ iota_loop . psi in A.\<close>
          have h0I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
          have h1I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
          from reparam_path_homotopy[OF hTX hf_cmap hf_img hA_sub hTA_loc hid_cmap h\<psi>_cmap
              _ _ h\<psi>_0 h\<psi>_1] h0I h1I
          have "top1_path_homotopic_on ?A ?TA (?\<iota>_loop 0) (?\<iota>_loop 1)
              (?\<iota>_loop \<circ> (\<lambda>t. t)) (?\<iota>_loop \<circ> \<psi>)"
            by (by100 blast)
          \<comment> \<open>iota_loop . id = iota_loop, iota_loop . psi = path_power alpha n (pointwise on I).\<close>
          have "(?\<iota>_loop \<circ> (\<lambda>t. t)) = ?\<iota>_loop" by (by100 auto)
          hence "top1_path_homotopic_on ?A ?TA ?a ?a ?\<iota>_loop (?\<iota>_loop \<circ> \<psi>)"
            using hf_0 hf_1 \<open>top1_path_homotopic_on ?A ?TA (?\<iota>_loop 0) (?\<iota>_loop 1)
              (?\<iota>_loop \<circ> (\<lambda>t. t)) (?\<iota>_loop \<circ> \<psi>)\<close> by (by100 simp)
          \<comment> \<open>Bridge: iota_loop . psi = path_power alpha n on I.\<close>
          moreover have "\<forall>t\<in>top1_unit_interval. (?\<iota>_loop \<circ> \<psi>) t = top1_path_power ?\<alpha> ?a n t"
            using h\<psi>_eq by (by100 simp)
          \<comment> \<open>The two loops agree pointwise on I, so they're path-homotopic by reflexivity + extensionality.\<close>
          ultimately show ?thesis
          proof -
            assume hhtpy: "top1_path_homotopic_on ?A ?TA ?a ?a ?\<iota>_loop (?\<iota>_loop \<circ> \<psi>)"
            assume hagree: "\<forall>t\<in>top1_unit_interval. (?\<iota>_loop \<circ> \<psi>) t = top1_path_power ?\<alpha> ?a n t"
            \<comment> \<open>path_homotopic_same_class: homotopic loops have same class.\<close>
            \<comment> \<open>And loops agreeing on I have same class (extensionality).\<close>
            have h_eq_htpy: "top1_path_homotopic_on ?A ?TA ?a ?a (?\<iota>_loop \<circ> \<psi>) (top1_path_power ?\<alpha> ?a n)"
            proof -
              \<comment> \<open>path_power alpha n is a loop in A, hence path-homotopic to itself.\<close>
              have "top1_is_loop_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a n)"
                by (rule top1_path_power_is_loop[OF hTA_loc h\<alpha>_loop])
              hence "top1_is_path_on ?A ?TA ?a ?a (top1_path_power ?\<alpha> ?a n)"
                unfolding top1_is_loop_on_def by (by100 blast)
              from Lemma_51_1_path_homotopic_refl[OF this]
              have "top1_path_homotopic_on ?A ?TA ?a ?a (top1_path_power ?\<alpha> ?a n) (top1_path_power ?\<alpha> ?a n)" .
              \<comment> \<open>Since iota_loop . psi = path_power alpha n on I, they have the same homotopy class.\<close>
              \<comment> \<open>Swap: since iota_loop.psi and path_power agree on I, use the reflexivity homotopy
                 for path_power, rewriting the F(s,0) condition.\<close>
              hence "\<exists>F. top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology ?A ?TA F
                  \<and> (\<forall>s\<in>top1_unit_interval. F (s, 0) = top1_path_power ?\<alpha> ?a n s)
                  \<and> (\<forall>s\<in>top1_unit_interval. F (s, 1) = top1_path_power ?\<alpha> ?a n s)
                  \<and> (\<forall>t\<in>top1_unit_interval. F (0, t) = ?a)
                  \<and> (\<forall>t\<in>top1_unit_interval. F (1, t) = ?a)"
                unfolding top1_path_homotopic_on_def by (by100 blast)
              hence "\<exists>F. top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology ?A ?TA F
                  \<and> (\<forall>s\<in>top1_unit_interval. F (s, 0) = (?\<iota>_loop \<circ> \<psi>) s)
                  \<and> (\<forall>s\<in>top1_unit_interval. F (s, 1) = top1_path_power ?\<alpha> ?a n s)
                  \<and> (\<forall>t\<in>top1_unit_interval. F (0, t) = ?a)
                  \<and> (\<forall>t\<in>top1_unit_interval. F (1, t) = ?a)"
                using hagree by (by5000 auto)
              moreover have "top1_is_path_on ?A ?TA ?a ?a (?\<iota>_loop \<circ> \<psi>)"
              proof -
                \<comment> \<open>Continuity: psi maps I -> I (continuous_map_on), iota_loop maps I -> A.\<close>
                have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA (?\<iota>_loop \<circ> \<psi>)"
                proof -
                  \<comment> \<open>iota_loop is a path in A (alpha loop, which we proved).\<close>
                  have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA ?\<alpha>"
                    using h\<alpha>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  \<comment> \<open>But we need iota_loop, not alpha. They differ. However, iota_loop . psi agrees
                     with path_power alpha n on I. And path_power alpha n is continuous.\<close>
                  have hcomp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?A ?TA
                      (top1_path_power ?\<alpha> ?a n)"
                    using top1_path_power_is_loop[OF hTA_loc h\<alpha>_loop]
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  \<comment> \<open>iota_loop . psi agrees with path_power on I, so use the same continuity.\<close>
                  have hpre_eq: "\<And>V. {x \<in> top1_unit_interval. (?\<iota>_loop \<circ> \<psi>) x \<in> V}
                      = {x \<in> top1_unit_interval. top1_path_power ?\<alpha> ?a n x \<in> V}"
                    using hagree by (by100 auto)
                  show ?thesis using hcomp hf_img
                    unfolding top1_continuous_map_on_def using hpre_eq hagree by (by5000 auto)
                qed
                moreover have "(?\<iota>_loop \<circ> \<psi>) 0 = ?a" using h\<psi>_0 hf_0 by (by100 simp)
                moreover have "(?\<iota>_loop \<circ> \<psi>) 1 = ?a" using h\<psi>_1 hf_1 by (by100 simp)
                ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
              qed
              moreover have "top1_is_path_on ?A ?TA ?a ?a (top1_path_power ?\<alpha> ?a n)"
                using \<open>top1_is_loop_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a n)\<close>
                unfolding top1_is_loop_on_def by (by100 blast)
              ultimately show ?thesis unfolding top1_path_homotopic_on_def by (by100 blast)
            qed
            show ?thesis using Lemma_51_1_path_homotopic_trans[OF hTA_loc hhtpy h_eq_htpy] by (by100 blast)
          qed
        qed
        \<comment> \<open>Step D.2: The relator is the class of iota . std_loop.\<close>
        have h_rel_class: "?relator = {g. top1_loop_equiv_on ?A ?TA ?a ?\<iota>_loop g}"
        proof -
          let ?std_class = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?std_loop g}"
          \<comment> \<open>By definition: relator = {g. EX f in std_class. loop_equiv(iota . f, g)}.\<close>
          have hdef: "?relator = {g. \<exists>f \<in> ?std_class. top1_loop_equiv_on ?A ?TA ?a (\<iota> \<circ> f) g}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          \<comment> \<open>std_loop is in its own class (reflexivity).\<close>
          have hstd_in: "?std_loop \<in> ?std_class"
            using top1_loop_equiv_on_refl[OF standard_S1_loop_is_loop] by (by100 blast)
          \<comment> \<open>For any f in std_class, iota.f ~ iota.std_loop (continuous map preserves homotopy).\<close>
          have hTA_loc: "is_topology_on ?A ?TA" by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
          have hclass_all: "\<And>f. f \<in> ?std_class \<Longrightarrow>
              {g. top1_loop_equiv_on ?A ?TA ?a (\<iota> \<circ> f) g} = {g. top1_loop_equiv_on ?A ?TA ?a ?\<iota>_loop g}"
          proof -
            fix f assume hf: "f \<in> ?std_class"
            hence hf_equiv: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?std_loop f"
              unfolding top1_loop_equiv_on_def by (by100 blast)
            hence hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
              unfolding top1_loop_equiv_on_def by (by100 blast)
            have hf_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?std_loop f"
              using hf_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
            \<comment> \<open>iota is continuous S1 -> A, so iota.std_loop ~ iota.f.\<close>
            have hS1_top_loc: "is_topology_on top1_S1 top1_S1_topology"
              using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
            have h\<iota>_cmapS1: "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA \<iota>"
              using h\<iota>_cont by (by100 blast)
            from top1_continuous_preserves_path_homotopy[OF hS1_top_loc h\<iota>_cmapS1
                standard_S1_loop_is_loop hf_loop hf_htpy]
            have "top1_path_homotopic_on ?A ?TA (\<iota> (1,0)) (\<iota> (1,0)) (\<iota> \<circ> ?std_loop) (\<iota> \<circ> f)" .
            have h\<iota>_10_loc: "\<iota> (1, 0) = ?a"
              using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
            have h\<iota>_loop_eq: "(\<iota> \<circ> ?std_loop) = ?\<iota>_loop"
              by (by100 auto)
            hence h\<iota>_htpy: "top1_path_homotopic_on ?A ?TA ?a ?a ?\<iota>_loop (\<iota> \<circ> f)"
              using \<open>top1_path_homotopic_on ?A ?TA (\<iota> (1,0)) (\<iota> (1,0)) (\<iota> \<circ> ?std_loop) (\<iota> \<circ> f)\<close>
                    h\<iota>_10_loc by (by100 simp)
            show "{g. top1_loop_equiv_on ?A ?TA ?a (\<iota> \<circ> f) g} = {g. top1_loop_equiv_on ?A ?TA ?a ?\<iota>_loop g}"
              using path_homotopic_same_class[OF hTA_loc h\<iota>_htpy] by (by100 simp)
          qed
          \<comment> \<open>Therefore the existential collapses.\<close>
          hence "?relator = {g. top1_loop_equiv_on ?A ?TA ?a ?\<iota>_loop g}"
            using hdef hstd_in by (by5000 blast)
          thus ?thesis .
        qed
        \<comment> \<open>Step D.3: path_power n gives the n-fold path product, whose class is group_pow n.\<close>
        have h_pow_class: "{g. top1_loop_equiv_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a m) g}
            = top1_group_pow ?mulA ?eA ?class_\<alpha> m" for m
        proof (induct m)
          case 0
          \<comment> \<open>path_power 0 = constant_path, class = eA = group_pow 0.\<close>
          show ?case unfolding top1_fundamental_group_id_def by (by5000 auto)
        next
          case (Suc k)
          \<comment> \<open>path_power (Suc k) = path_product alpha (path_power k).\<close>
          have h_pp: "top1_path_power ?\<alpha> ?a (Suc k) = top1_path_product ?\<alpha> (top1_path_power ?\<alpha> ?a k)"
            by (by100 simp)
          \<comment> \<open>Both alpha and path_power k are loops.\<close>
          have h_pp_loop: "top1_is_loop_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a k)"
            by (rule top1_path_power_is_loop[OF hTA_loc h\<alpha>_loop])
          \<comment> \<open>Class of product = product of classes.\<close>
          have h_mul_class: "{g. top1_loop_equiv_on ?A ?TA ?a
                (top1_path_product ?\<alpha> (top1_path_power ?\<alpha> ?a k)) g}
              = ?mulA ?class_\<alpha> {g. top1_loop_equiv_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a k) g}"
            using top1_fundamental_group_mul_class[OF hTA_loc h\<alpha>_loop h_pp_loop] by (by100 simp)
          show ?case using h_pp h_mul_class Suc by (by100 simp)
        qed
        \<comment> \<open>Step D.4: homotopic loops have the same equivalence class.\<close>
        have h_class_eq: "{g. top1_loop_equiv_on ?A ?TA ?a ?\<iota>_loop g}
            = {g. top1_loop_equiv_on ?A ?TA ?a (top1_path_power ?\<alpha> ?a n) g}"
          by (rule path_homotopic_same_class[OF hTA_loc h_htpy])
        show ?thesis using h_rel_class h_class_eq h_pow_class by (by100 simp)
      qed
      \<comment> \<open>Step E: phi is a hom, so phi([alpha]^n) = phi([alpha])^n in Z.\<close>
      have h\<alpha>_in_GA: "?class_\<alpha> \<in> ?GA"
        using h\<alpha>_loop unfolding top1_fundamental_group_carrier_def by (by100 blast)
      have h\<phi>_hom: "top1_group_hom_on ?GA ?mulA top1_Z_group top1_Z_mul \<phi>"
        using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
      have hgrpA_loc: "top1_is_group_on ?GA ?mulA ?eA ?invA"
        by (rule top1_fundamental_group_is_group[OF hTA_top ha_A])
      have hgrpZ_loc: "top1_is_group_on top1_Z_group top1_Z_mul (0::int) uminus"
      proof -
        have "top1_Z_id = (0::int)" unfolding top1_Z_id_def by (by100 blast)
        moreover have "top1_Z_invg = (uminus :: int \<Rightarrow> int)" unfolding top1_Z_invg_def by (by100 blast)
        ultimately show ?thesis
          using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 simp)
      qed
      have h_phi_pow: "\<phi> (top1_group_pow ?mulA ?eA ?class_\<alpha> n) = top1_group_pow top1_Z_mul (0::int) (\<phi> ?class_\<alpha>) n"
        using hom_group_pow[OF hgrpA_loc hgrpZ_loc h\<phi>_hom h\<alpha>_in_GA] by (by100 blast)
      \<comment> \<open>In Z: x^n = n*x.\<close>
      have hZ_pow_eq: "top1_group_pow top1_Z_mul (0::int) x n = int n * x" for x :: int
      proof (induct n)
        case 0 thus ?case by (by100 simp)
      next
        case (Suc n)
        have "top1_group_pow top1_Z_mul (0::int) x (Suc n) = top1_Z_mul x (top1_group_pow top1_Z_mul 0 x n)"
          by (by100 simp)
        also have "\<dots> = x + int n * x" using Suc unfolding top1_Z_mul_def by (by100 simp)
        also have "\<dots> = (1 + int n) * x" by (by5000 algebra)
        also have "\<dots> = int (Suc n) * x" by (by100 simp)
        finally show ?case .
      qed
      \<comment> \<open>Step F: Combine.\<close>
      from h\<alpha>_gen show ?thesis
      proof
        assume "\<phi> ?class_\<alpha> = 1"
        hence "\<phi> ?relator = int n * 1" using h_relator_is_alpha_n h_phi_pow hZ_pow_eq by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        assume "\<phi> ?class_\<alpha> = -1"
        hence "\<phi> ?relator = int n * (-1)" using h_relator_is_alpha_n h_phi_pow hZ_pow_eq by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 10.3: Use quotient_group_iso_transfer: pi1(A)/N iso Z/phi(N).\<close>
    have hgrpA: "top1_is_group_on ?GA ?mulA ?eA ?invA"
      by (rule top1_fundamental_group_is_group[OF hTA_top ha_A])
    have h\<iota>_10: "\<iota> (1, 0) = ?a"
      using h\<iota>_eq h10_S1 hq_10 by (by100 simp)
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA_top2: "is_topology_on ?A ?TA" by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    have h\<iota>_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        ?GA ?mulA
        (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?A ?TA ?a \<iota>)"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA_top2 h10_S1 ha_A h\<iota>_cont h\<iota>_10])
    have hstd_loop_in_S1: "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g} \<in>
        top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      by (rule standard_S1_loop_class_in_carrier)
    have hrel_in_GA: "{?relator} \<subseteq> ?GA"
    proof -
      have "?relator \<in> ?GA"
        using h\<iota>_hom hstd_loop_in_S1 unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hN_normal: "top1_normal_subgroup_on ?GA ?mulA ?eA ?invA ?N"
      by (rule normal_subgroup_generated_is_normal[OF hgrpA hrel_in_GA])
    have hgrpZ: "top1_is_group_on top1_Z_group top1_Z_mul (0::int) uminus"
    proof -
      have "top1_Z_id = (0::int)" unfolding top1_Z_id_def by (by100 blast)
      moreover have "top1_Z_invg = (uminus :: int \<Rightarrow> int)" unfolding top1_Z_invg_def by (by100 blast)
      ultimately show ?thesis
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 simp)
    qed
    have hquot_transfer: "top1_groups_isomorphic_on
        (top1_quotient_group_carrier_on ?GA ?mulA ?N)
        (top1_quotient_group_mul_on ?mulA)
        (top1_quotient_group_carrier_on top1_Z_group top1_Z_mul (\<phi> ` ?N))
        (top1_quotient_group_mul_on top1_Z_mul)"
      using quotient_group_iso_transfer[OF hgrpA hgrpZ h\<phi>_iso hN_normal] by (by100 blast)
    \<comment> \<open>Step 10.4: phi(N) = nZ. Whether relator maps to n or -n,
       the generated normal subgroup is the same: nZ.\<close>
    \<comment> \<open>For an iso phi, phi(normal_closure(S)) = normal_closure(phi(S)).
       Since phi(relator) = +/-n, normal_closure({+/-n}) = normal_closure({n}) in Z.\<close>
    have hphiN_eq: "\<phi> ` ?N = top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}"
    proof -
      \<comment> \<open>Step 1: phi(normal_closure({r})) = normal_closure({phi(r)}) for iso phi.\<close>
      have hiso_nc: "\<phi> ` ?N = top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {\<phi> ?relator}"
      proof (rule set_eqI, rule iffI)
        let ?NC_Z = "top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {\<phi> ?relator}"
        \<comment> \<open>Forward: NC_Z({phi(r)}) \<subseteq> phi(N).\<close>
        \<comment> \<open>phi(N) is normal in Z (iso image of normal subgroup).\<close>
        have hphiN_normal: "top1_normal_subgroup_on top1_Z_group top1_Z_mul (0::int) uminus (\<phi> ` ?N)"
          by (rule group_iso_on_image_normal_subgroup[OF h\<phi>_iso hgrpA hgrpZ hN_normal])
        \<comment> \<open>{phi(r)} \<subseteq> phi(N): since r \<in> N, phi(r) \<in> phi(N).\<close>
        have hr_in_N: "?relator \<in> ?N"
          unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
        hence hphir_in_phiN: "\<phi> ?relator \<in> \<phi> ` ?N" by (by100 blast)
        hence hset_sub: "{\<phi> ?relator} \<subseteq> \<phi> ` ?N" by (by100 blast)
        \<comment> \<open>By normal_closure_least: NC_Z({phi(r)}) \<subseteq> phi(N).\<close>
        have hfwd: "?NC_Z \<subseteq> \<phi> ` ?N"
          using normal_closure_least[OF hgrpZ hphiN_normal hset_sub] by (by100 blast)
        \<comment> \<open>Backward: phi(N) \<subseteq> NC_Z({phi(r)}).
           For c \<in> N: phi(c) \<in> phi(N). Need phi(c) \<in> NC_Z({phi(r)}).
           By inj_hom_preimage_normal_closure (reverse direction):
           actually we use that phi is surj + inj, so apply to phi^{-1}.\<close>
        have hbwd: "\<phi> ` ?N \<subseteq> ?NC_Z"
        proof -
          \<comment> \<open>NC_Z({phi(r)}) is normal in Z.\<close>
          have hphi_rel_in_Z: "\<phi> ?relator \<in> top1_Z_group"
            using h\<phi>_iso hrel_in_GA unfolding top1_group_iso_on_def top1_group_hom_on_def top1_Z_group_def
            by (by100 blast)
          have hNC_Z_normal: "top1_normal_subgroup_on top1_Z_group top1_Z_mul (0::int) uminus ?NC_Z"
          proof -
            have "{\<phi> ?relator} \<subseteq> top1_Z_group" using hphi_rel_in_Z by (by100 blast)
            thus ?thesis by (rule normal_subgroup_generated_is_normal[OF hgrpZ])
          qed
          \<comment> \<open>Preimage f^{-1}(NC_Z) is normal in pi1(A).\<close>
          have h\<phi>_hom: "top1_group_hom_on ?GA ?mulA top1_Z_group top1_Z_mul \<phi>"
            using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
          have hpreimg_normal: "top1_normal_subgroup_on ?GA ?mulA ?eA ?invA {g \<in> ?GA. \<phi> g \<in> ?NC_Z}"
            using preimage_normal_subgroup[OF hgrpA hgrpZ h\<phi>_hom hNC_Z_normal] by (by100 blast)
          \<comment> \<open>s \<in> preimage: phi(s) \<in> NC_Z({phi(s)}).\<close>
          have hrel_in_preimg: "?relator \<in> {g \<in> ?GA. \<phi> g \<in> ?NC_Z}"
          proof -
            have "?relator \<in> ?GA" using hrel_in_GA by (by100 blast)
            moreover have "\<phi> ?relator \<in> ?NC_Z"
              unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          hence "{?relator} \<subseteq> {g \<in> ?GA. \<phi> g \<in> ?NC_Z}" by (by100 blast)
          \<comment> \<open>By normal_closure_least: N = NC({r}) \<subseteq> preimage.\<close>
          hence "?N \<subseteq> {g \<in> ?GA. \<phi> g \<in> ?NC_Z}"
            using normal_closure_least[OF hgrpA hpreimg_normal] by (by100 blast)
          \<comment> \<open>Therefore phi(N) \<subseteq> NC_Z.\<close>
          thus ?thesis by (by100 blast)
        qed
        fix x
        show "x \<in> \<phi> ` ?N \<Longrightarrow> x \<in> ?NC_Z" using hbwd by (by100 blast)
        show "x \<in> ?NC_Z \<Longrightarrow> x \<in> \<phi> ` ?N" using hfwd by (by100 blast)
      qed
      \<comment> \<open>Step 2: normal_closure({n}) = normal_closure({-n}) in Z.\<close>
      have hneg_nc: "top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {- int n}
          = top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}"
      proof (rule set_eqI, rule iffI)
        let ?NC_n = "top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}"
        let ?NC_neg = "top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {- int n}"
        \<comment> \<open>-n \<in> NC({n}): -n = uminus n, and n \<in> NC({n}) \<supseteq> {n}, so uminus n \<in> NC({n}) since it's a group.\<close>
        have hn_in: "int n \<in> ?NC_n"
          unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
        have hn_Z: "int n \<in> top1_Z_group" unfolding top1_Z_group_def by (by100 blast)
        have hneg_Z: "- int n \<in> top1_Z_group" unfolding top1_Z_group_def by (by100 blast)
        have hNC_n_normal: "top1_normal_subgroup_on top1_Z_group top1_Z_mul (0::int) uminus ?NC_n"
          using normal_subgroup_generated_is_normal[OF hgrpZ] hn_Z
          unfolding top1_Z_group_def by (by5000 auto)
        have hneg_in_NCn: "- int n \<in> ?NC_n"
        proof -
          from hNC_n_normal have hgrp_NCn: "top1_is_group_on ?NC_n top1_Z_mul 0 uminus"
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          hence "uminus (int n) \<in> ?NC_n" using hn_in
            unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        have hNC_neg_normal: "top1_normal_subgroup_on top1_Z_group top1_Z_mul (0::int) uminus ?NC_neg"
          using normal_subgroup_generated_is_normal[OF hgrpZ] hneg_Z
          unfolding top1_Z_group_def by (by5000 auto)
        have hn_in_NCneg: "int n \<in> ?NC_neg"
        proof -
          have hneg_in: "- int n \<in> ?NC_neg"
            unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
          from hNC_neg_normal have "top1_is_group_on ?NC_neg top1_Z_mul 0 uminus"
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          hence "uminus (- int n) \<in> ?NC_neg" using hneg_in
            unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        fix x
        show "x \<in> ?NC_neg \<Longrightarrow> x \<in> ?NC_n"
          using normal_closure_least[OF hgrpZ hNC_n_normal] hneg_in_NCn by (by100 blast)
        show "x \<in> ?NC_n \<Longrightarrow> x \<in> ?NC_neg"
          using normal_closure_least[OF hgrpZ hNC_neg_normal] hn_in_NCneg by (by100 blast)
      qed
      \<comment> \<open>Step 3: Combine via h_relator_val.\<close>
      from h_relator_val show ?thesis
      proof
        assume "\<phi> ?relator = int n" thus ?thesis using hiso_nc by (by100 simp)
      next
        assume "\<phi> ?relator = - int n" thus ?thesis using hiso_nc hneg_nc by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 10.5: Z/nZ iso by Z_quotient_nZ_iso.\<close>
    have hn_ge: "n \<ge> 1" using assms(1) by (by100 linarith)
    have hZ_nZ: "top1_groups_isomorphic_on
        (top1_quotient_group_carrier_on top1_Z_group top1_Z_mul
           (top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}))
        (top1_quotient_group_mul_on top1_Z_mul)
        (top1_Zn_group n) (top1_Zn_mul n)"
    proof -
      have "top1_Z_group = (UNIV::int set)" unfolding top1_Z_group_def by (by100 blast)
      moreover have "top1_Z_mul = ((+)::int \<Rightarrow> int \<Rightarrow> int)" unfolding top1_Z_mul_def by (by100 blast)
      ultimately show ?thesis using Z_quotient_nZ_iso[OF hn_ge] by (by100 simp)
    qed
    \<comment> \<open>Presentation: the quotient Q = pi1(A)/N is presented by \<langle>a | a^n\<rangle>.\<close>
    have hQ_presented: "\<exists>e invg.
        top1_group_presented_by_on
          (top1_quotient_group_carrier_on ?GA ?mulA ?N) (top1_quotient_group_mul_on ?mulA)
          e invg ({..<1}::nat set) { replicate n (0::nat, True) }"
    proof -
      let ?Q = "top1_quotient_group_carrier_on ?GA ?mulA ?N"
      let ?mulQ = "top1_quotient_group_mul_on ?mulA"
      let ?coset = "\<lambda>g. top1_group_coset_on ?GA ?mulA ?N g"
      let ?eQ = "?coset ?eA"
      let ?invQ = "\<lambda>C. ?coset (?invA (SOME g. g \<in> ?GA \<and> C = ?coset g))"
      let ?\<pi> = "\<lambda>z. ?coset (inv_into ?GA \<phi> z)"
      \<comment> \<open>Step 1: Q is a group.\<close>
      have hQ_grp: "top1_is_group_on ?Q ?mulQ ?eQ ?invQ"
        by (rule quotient_group_is_group[OF hgrpA hN_normal])
      \<comment> \<open>Step 2: Quotient projection properties.\<close>
      have hcoset_hom: "top1_group_hom_on ?GA ?mulA ?Q ?mulQ ?coset"
        and hcoset_surj: "?coset ` ?GA = ?Q"
        and hcoset_ker: "top1_group_kernel_on ?GA ?eQ ?coset = ?N"
        using quotient_projection_properties[OF hgrpA hN_normal] by (by100 blast)+
      \<comment> \<open>Step 3: \<phi>^{-1} is a group hom Z \<rightarrow> ?GA.\<close>
      have h\<phi>_hom: "top1_group_hom_on ?GA ?mulA top1_Z_group top1_Z_mul \<phi>"
        using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
      have h\<phi>_bij: "bij_betw \<phi> ?GA top1_Z_group"
        using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
      have h\<phi>inv_hom: "top1_group_hom_on top1_Z_group top1_Z_mul ?GA ?mulA (inv_into ?GA \<phi>)"
        by (rule bij_hom_inv_is_hom[OF hgrpA hgrpZ h\<phi>_bij h\<phi>_hom])
      \<comment> \<open>Step 4: \<pi> = coset \<circ> \<phi>^{-1} is a hom Z \<rightarrow> Q.\<close>
      have h\<pi>_hom: "top1_group_hom_on top1_Z_group top1_Z_mul ?Q ?mulQ ?\<pi>"
      proof -
        from group_hom_comp[OF h\<phi>inv_hom hcoset_hom]
        have "top1_group_hom_on top1_Z_group top1_Z_mul ?Q ?mulQ (?coset \<circ> inv_into ?GA \<phi>)" .
        moreover have "(\<lambda>z. ?coset (inv_into ?GA \<phi> z)) = ?coset \<circ> inv_into ?GA \<phi>" by (by100 auto)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Step 5: \<pi> surjective.\<close>
      have h\<pi>_surj: "?\<pi> ` top1_Z_group = ?Q"
      proof -
        have h_inv_surj: "inv_into ?GA \<phi> ` top1_Z_group = ?GA"
        proof -
          have "\<phi> ` ?GA = top1_Z_group" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
          have "inj_on \<phi> ?GA" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
          show ?thesis
          proof (rule set_eqI, rule iffI)
            fix g assume "g \<in> inv_into ?GA \<phi> ` top1_Z_group"
            then obtain z where "z \<in> top1_Z_group" "g = inv_into ?GA \<phi> z" by (by100 blast)
            have "z \<in> \<phi> ` ?GA" using \<open>z \<in> top1_Z_group\<close> \<open>\<phi> ` ?GA = top1_Z_group\<close> by (by100 simp)
            hence "inv_into ?GA \<phi> z \<in> ?GA"
              by (rule inv_into_into)
            thus "g \<in> ?GA" using \<open>g = inv_into ?GA \<phi> z\<close> by (by100 simp)
          next
            fix g assume "g \<in> ?GA"
            hence "\<phi> g \<in> top1_Z_group" using \<open>\<phi> ` ?GA = top1_Z_group\<close> by (by100 blast)
            moreover have "inv_into ?GA \<phi> (\<phi> g) = g"
              using inv_into_f_f[OF \<open>inj_on \<phi> ?GA\<close> \<open>g \<in> ?GA\<close>] .
            ultimately show "g \<in> inv_into ?GA \<phi> ` top1_Z_group" by (by100 blast)
          qed
        qed
        have "?\<pi> ` top1_Z_group = ?coset ` (inv_into ?GA \<phi> ` top1_Z_group)"
          by (by100 auto)
        also have "\<dots> = ?coset ` ?GA" using h_inv_surj by (by100 simp)
        also have "\<dots> = ?Q" by (rule hcoset_surj)
        finally show ?thesis .
      qed
      \<comment> \<open>Step 6: ker(\<pi>) = NC\_Z(\{word\_product replicate n (0,True)\}).\<close>
      have h\<pi>_ker: "top1_group_kernel_on top1_Z_group ?eQ ?\<pi> =
          top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
            {top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                (map (\<lambda>(s, b). ((\<lambda>(_::nat). (1::int)) s, b)) (replicate n (0::nat, True)))}"
      proof -
        \<comment> \<open>Step 6a: word\_product of replicate n (0,True) with \<iota>(0) = 1 equals n.\<close>
        have hmap_simp: "map (\<lambda>(s, b). ((\<lambda>(_::nat). (1::int)) s, b)) (replicate n (0::nat, True))
            = replicate n (1::int, True)" by (induction n, by100 simp, by100 simp)
        have hword_rep: "\<And>m. top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (replicate m (1::int, True)) = int m"
        proof -
          fix m show "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
              (replicate m (1::int, True)) = int m"
          proof (induction m)
            case 0 show ?case unfolding top1_Z_id_def by (by100 simp)
          next
            case (Suc m)
            have "replicate (Suc m) (1::int, True) = (1::int, True) # replicate m (1, True)"
              by (by100 simp)
            hence "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                (replicate (Suc m) (1::int, True))
              = top1_Z_mul 1 (top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                  (replicate m (1, True)))"
              by (by100 simp)
            also have "\<dots> = top1_Z_mul 1 (int m)" using Suc.IH by (by100 simp)
            also have "\<dots> = int (Suc m)" unfolding top1_Z_mul_def by (by100 simp)
            finally show ?case .
          qed
        qed
        have hword_eq: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). (1::int)) s, b)) (replicate n (0::nat, True))) = int n"
          using hmap_simp hword_rep by (by100 simp)
        \<comment> \<open>Step 6b: ker(\<pi>) = {z \<in> Z | \<phi>^{-1}(z) \<in> N} = \<phi>(N).\<close>
        have hker_eq_phiN: "top1_group_kernel_on top1_Z_group ?eQ ?\<pi> = \<phi> ` ?N"
        proof (rule set_eqI, rule iffI)
          fix z assume "z \<in> top1_group_kernel_on top1_Z_group ?eQ ?\<pi>"
          \<comment> \<open>z \<in> Z, \<pi>(z) = eQ. So coset(\<phi>^{-1}(z)) = coset(eA). So \<phi>^{-1}(z) \<in> N.\<close>
          hence hz: "z \<in> top1_Z_group" "?\<pi> z = ?eQ"
            unfolding top1_group_kernel_on_def by (by100 blast)+
          have "?coset (inv_into ?GA \<phi> z) = ?coset ?eA" using hz(2) by (by100 simp)
          have "inv_into ?GA \<phi> z \<in> ?GA"
          proof -
            have "z \<in> \<phi> ` ?GA" using hz(1) h\<phi>_bij unfolding bij_betw_def by (by100 blast)
            thus ?thesis by (rule inv_into_into)
          qed
          hence "inv_into ?GA \<phi> z \<in> ?N"
            using \<open>?coset (inv_into ?GA \<phi> z) = ?coset ?eA\<close> hcoset_ker
            unfolding top1_group_kernel_on_def by (by100 blast)
          \<comment> \<open>\<phi>^{-1}(z) \<in> N, so z = \<phi>(\<phi>^{-1}(z)) \<in> \<phi>(N).\<close>
          moreover have "z = \<phi> (inv_into ?GA \<phi> z)"
          proof -
            have "z \<in> \<phi> ` ?GA" using hz(1) h\<phi>_bij unfolding bij_betw_def by (by100 blast)
            from f_inv_into_f[OF this] show ?thesis by (by100 simp)
          qed
          ultimately show "z \<in> \<phi> ` ?N" by (by100 blast)
        next
          fix z assume "z \<in> \<phi> ` ?N"
          then obtain g where hg: "g \<in> ?N" "z = \<phi> g" by (by100 blast)
          have "g \<in> ?GA" using hg(1) hN_normal
            unfolding top1_normal_subgroup_on_def by (by100 blast)
          hence "inv_into ?GA \<phi> z = g"
          proof -
            have "inj_on \<phi> ?GA" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
            from inv_into_f_f[OF this \<open>g \<in> ?GA\<close>] show ?thesis using hg(2) by (by100 simp)
          qed
          hence "?\<pi> z = ?coset g" by (by100 simp)
          also have "\<dots> = ?eQ"
          proof -
            from hg(1) have "g \<in> ?N" .
            hence "g \<in> top1_group_kernel_on ?GA ?eQ ?coset"
              using hcoset_ker by (by100 simp)
            thus ?thesis unfolding top1_group_kernel_on_def using \<open>g \<in> ?GA\<close> by (by100 blast)
          qed
          finally have "?\<pi> z = ?eQ" .
          moreover have "z \<in> top1_Z_group"
            using hg(2) \<open>g \<in> ?GA\<close> h\<phi>_bij unfolding bij_betw_def by (by100 blast)
          ultimately show "z \<in> top1_group_kernel_on top1_Z_group ?eQ ?\<pi>"
            unfolding top1_group_kernel_on_def by (by100 blast)
        qed
        \<comment> \<open>Step 6c: \<phi>(N) = \<phi>(NC\_G(\{relator\})) = NC\_Z(\{\<phi>(relator)\}).\<close>
        \<comment> \<open>Step 6d: NC\_Z(\{\<phi>(relator)\}) = NC\_Z(\{n\}) (from h\_relator\_val: \<phi>(relator) = \<pm>n).\<close>
        \<comment> \<open>Step 6e: NC\_Z(\{n\}) = NC\_Z(\{word\_product\}) (from hword\_eq).\<close>
        \<comment> \<open>ker(\<pi>) = \<phi>(N) = NC\_Z(\{n\}) = NC\_Z(\{word\_product\}).\<close>
        have "top1_group_kernel_on top1_Z_group ?eQ ?\<pi> = \<phi> ` ?N" by (rule hker_eq_phiN)
        also have "\<dots> = top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}"
          by (rule hphiN_eq)
        also have "{int n} = {top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). (1::int)) s, b)) (replicate n (0::nat, True)))}"
          using hword_eq by (by100 simp)
        also have "top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus \<dots>
            = top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg \<dots>"
          unfolding top1_Z_id_def top1_Z_invg_def by (by100 simp)
        finally show ?thesis .
      qed
      \<comment> \<open>Step 7: Assemble the presentation.\<close>
      \<comment> \<open>Z free on {..<1}.\<close>
      have hZ_free_01: "top1_is_free_group_full_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
          (\<lambda>(_::nat). (1::int)) {..<1::nat}"
      proof -
        have "{0::nat} = {..<1::nat}" by (by100 auto)
        thus ?thesis using Z_is_free_on_one_generator by (by100 simp)
      qed
      show ?thesis
        unfolding top1_group_presented_by_on_def
        apply (rule exI[of _ ?eQ], rule exI[of _ ?invQ])
        apply (intro conjI)
        apply (rule hQ_grp)
        apply (rule exI[of _ top1_Z_group], rule exI[of _ top1_Z_mul],
               rule exI[of _ top1_Z_id], rule exI[of _ top1_Z_invg],
               rule exI[of _ "\<lambda>(_::nat). (1::int)"], rule exI[of _ ?\<pi>])
        apply (intro conjI)
        apply (rule hZ_free_01)
        apply (rule h\<pi>_hom)
        apply (rule h\<pi>_surj)
        using h\<pi>_ker by (by100 simp)
    qed
    \<comment> \<open>Compose: pi1(A)/N iso Z/phi(N) = Z/nZ iso Z/nZ.\<close>
    have "top1_groups_isomorphic_on
        (top1_quotient_group_carrier_on ?GA ?mulA ?N)
        (top1_quotient_group_mul_on ?mulA)
        (top1_quotient_group_carrier_on top1_Z_group top1_Z_mul
           (top1_normal_subgroup_generated_on top1_Z_group top1_Z_mul (0::int) uminus {int n}))
        (top1_quotient_group_mul_on top1_Z_mul)"
      using hquot_transfer hphiN_eq by (by100 simp)
    hence hiso_part: "top1_groups_isomorphic_on
        (top1_quotient_group_carrier_on ?GA ?mulA ?N) (top1_quotient_group_mul_on ?mulA)
        (top1_Zn_group n) (top1_Zn_mul n)"
      by (rule groups_isomorphic_trans_fwd[OF _ hZ_nZ])
    show ?thesis using hiso_part hQ_presented by (by100 blast)
  qed
  \<comment> \<open>Step 11: Compose: \<pi>_1(X,a) \<cong> \<pi>_1(A,a)/\<langle>\<langle>relator\<rangle>\<rangle> \<cong> Z/nZ.\<close>
  have hmain: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX ?a)
      (top1_fundamental_group_mul X TX ?a)
      (top1_Zn_group n) (top1_Zn_mul n)"
  proof -
    have hquot_ZnZ: "top1_groups_isomorphic_on
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier ?A ?TA ?a)
           (top1_fundamental_group_mul ?A ?TA ?a)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier ?A ?TA ?a)
              (top1_fundamental_group_mul ?A ?TA ?a)
              (top1_fundamental_group_id ?A ?TA ?a)
              (top1_fundamental_group_invg ?A ?TA ?a)
              {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                 ?A ?TA ?a \<iota>
                 {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                       (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
        (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a))
        (top1_Zn_group n) (top1_Zn_mul n)"
      using hquot_ZnZ_and_pres by (by100 blast)
    show ?thesis by (rule groups_isomorphic_trans_fwd[OF h72_iso hquot_ZnZ])
  qed
  \<comment> \<open>Step 12: Base-point change: X is path-connected (continuous surjective image of B²).
     \<pi>_1(X, x0) \<cong> \<pi>_1(X, a) \<cong> Z/nZ.\<close>
  have hX_pc: "top1_path_connected_on X TX"
  proof -
    \<comment> \<open>B² is path-connected, q is continuous surjective. Image is path-connected.\<close>
    have hB2_pc: "top1_path_connected_on top1_B2 top1_B2_topology"
      by (rule top1_B2_path_connected)
    have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
      using hB2_pc unfolding top1_path_connected_on_def by (by100 blast)
    have hII_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      have "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
      show ?thesis unfolding top1_unit_interval_topology_def
        by (rule subspace_topology_is_topology_on[OF \<open>is_topology_on UNIV top1_open_sets\<close>
              \<open>top1_unit_interval \<subseteq> UNIV\<close>])
    qed
    show ?thesis unfolding top1_path_connected_on_def
    proof (intro conjI ballI)
      show "is_topology_on X TX" by (rule hTX)
    next
      fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
      from hx obtain a where ha: "a \<in> top1_B2" "q a = x" using hq_surj by (by100 blast)
      from hy obtain b where hb: "b \<in> top1_B2" "q b = y" using hq_surj by (by100 blast)
      from hB2_pc have "\<exists>f. top1_is_path_on top1_B2 top1_B2_topology a b f"
        using ha(1) hb(1) unfolding top1_path_connected_on_def by (by100 blast)
      then obtain \<gamma> where h\<gamma>: "top1_is_path_on top1_B2 top1_B2_topology a b \<gamma>"
        by (by100 blast)
      have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_B2 top1_B2_topology \<gamma>"
        using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have hq\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          X TX (q \<circ> \<gamma>)"
        by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hq_cont])
      have "(q \<circ> \<gamma>) 0 = x" using h\<gamma> ha(2) unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(q \<circ> \<gamma>) 1 = y" using h\<gamma> hb(2) unfolding top1_is_path_on_def by (by100 simp)
      ultimately have "top1_is_path_on X TX x y (q \<circ> \<gamma>)"
        using hq\<gamma>_cont unfolding top1_is_path_on_def by (by100 blast)
      thus "\<exists>f. top1_is_path_on X TX x y f" by (by100 blast)
    qed
  qed
  have hbc: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier X TX ?a)
      (top1_fundamental_group_mul X TX ?a)"
    by (rule Corollary_52_2_basepoint_independent[OF hX_pc assms(3) ha_X])
  have hiso_final: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_Zn_group n) (top1_Zn_mul n)"
    by (rule groups_isomorphic_trans_fwd[OF hbc hmain])
  \<comment> \<open>Helper: iso(pi1(x0), Q) from hbc + h72_iso.\<close>
  have hiso_x0_Q: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_quotient_group_carrier_on
         (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
         (top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
            (top1_fundamental_group_id ?A ?TA ?a) (top1_fundamental_group_invg ?A ?TA ?a)
            {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
               ?A ?TA ?a \<iota>
               {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
      (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a))"
    by (rule groups_isomorphic_trans_fwd[OF hbc h72_iso])
  \<comment> \<open>Group structures for iso reversal.\<close>
  have hgrp_x0: "top1_is_group_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
    by (rule top1_fundamental_group_is_group[OF hTX assms(3)])
  \<comment> \<open>The quotient group Q is also a group (from hquot\_ZnZ which gives iso to Z/nZ which is a group).\<close>
  have hgrp_Q: "\<exists>eQ invQ. top1_is_group_on
      (top1_quotient_group_carrier_on
         (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
         (top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
            (top1_fundamental_group_id ?A ?TA ?a) (top1_fundamental_group_invg ?A ?TA ?a)
            {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
               ?A ?TA ?a \<iota>
               {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
      (top1_quotient_group_mul_on (top1_fundamental_group_mul ?A ?TA ?a)) eQ invQ"
  proof -
    have hTA_top: "is_topology_on ?A ?TA"
    proof -
      have "?A \<subseteq> X" using hA_cl unfolding closedin_on_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTX \<open>?A \<subseteq> X\<close>])
    qed
    have ha_in_A: "?a \<in> ?A"
    proof -
      have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    have hgrpA': "top1_is_group_on
        (top1_fundamental_group_carrier ?A ?TA ?a)
        (top1_fundamental_group_mul ?A ?TA ?a)
        (top1_fundamental_group_id ?A ?TA ?a)
        (top1_fundamental_group_invg ?A ?TA ?a)"
      by (rule top1_fundamental_group_is_group[OF hTA_top ha_in_A])
    have hN_normal': "top1_normal_subgroup_on
        (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
        (top1_fundamental_group_id ?A ?TA ?a) (top1_fundamental_group_invg ?A ?TA ?a)
        (top1_normal_subgroup_generated_on
           (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
           (top1_fundamental_group_id ?A ?TA ?a) (top1_fundamental_group_invg ?A ?TA ?a)
           {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?A ?TA ?a \<iota>
              {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                    (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}})"
    proof -
      have "{top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?A ?TA ?a \<iota>
              {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                    (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}
          \<subseteq> top1_fundamental_group_carrier ?A ?TA ?a"
      proof -
        \<comment> \<open>The induced map \<iota>_*: \<pi>_1(S1, (1,0)) \<rightarrow> \<pi>_1(A, a') is a homomorphism.
           The standard loop class is in \<pi>_1(S1, (1,0)).
           Its image under \<iota>_* is in \<pi>_1(A, a').\<close>
        have "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?A ?TA ?a \<iota>
            {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                  (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}
          \<in> top1_fundamental_group_carrier ?A ?TA ?a"
        proof -
          \<comment> \<open>h\<iota>_cont and h\<iota>_eq are from Theorem 72.1 (outer proof block).\<close>
          have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
            using S1_compact unfolding top1_compact_on_def by (by100 blast)
          have h10_S1: "(1::real, 0::real) \<in> top1_S1"
            unfolding top1_S1_def by (by100 simp)
          have h\<iota>_10: "\<iota> (1, 0) = ?a"
            using h\<iota>_eq h10_S1 by (by100 simp)
          from top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA_top h10_S1 ha_in_A h\<iota>_cont h\<iota>_10]
          have hhom: "top1_group_hom_on
              (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_carrier ?A ?TA ?a) (top1_fundamental_group_mul ?A ?TA ?a)
              (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?A ?TA ?a \<iota>)" .
          \<comment> \<open>The standard loop class is in \<pi>_1(S1, (1,0)).\<close>
          have hstd_in: "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}
              \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
            by (rule standard_S1_loop_class_in_carrier)
          \<comment> \<open>Image of carrier element under hom is in carrier.\<close>
          from hhom hstd_in show ?thesis
            unfolding top1_group_hom_on_def by (by5000 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
      from normal_subgroup_generated_is_normal[OF hgrpA' this]
      show ?thesis .
    qed
    from quotient_group_is_group[OF hgrpA' hN_normal'] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Presentation: presented(Q) + iso(Q, pi1(x0)) packaged.\<close>
  have hpres: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg ({..<1}::nat set)
        { replicate n (0::nat, True) }
    \<and> top1_groups_isomorphic_on G mul
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    using conjunct2[OF hquot_ZnZ_and_pres] hiso_x0_Q
      top1_groups_isomorphic_on_sym hgrp_x0 hgrp_Q by (by5000 fast)
  show ?thesis using hiso_final hpres by (by100 blast)
qed

text \<open>Corollary: the dunce cap with n has presentation \<langle>a | a^n\<rangle>.
  This follows from Theorem 73.4 + the structure of the Theorem 72.1 quotient.\<close>
corollary dunce_cap_presentation:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "n > 0"
      and "top1_is_dunce_cap_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<1}::nat set)
             { replicate n (0::nat, True) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
  using Theorem_73_4_dunce_cap[OF assms] by (by100 blast)

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1² \<cdots> a_m²\<rangle>.
    The single relator is (a_1 a_1)(a_2 a_2)\<cdots>(a_m a_m). **)
theorem Theorem_74_4_fund_group_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<m}::nat set)
             { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
proof (cases "m = 1")
  case True
  \<comment> \<open>Case m = 1: Use Theorem 73.4 directly. \<pi>_1(dunce\_cap(2)) \<cong> Z/2Z.
     Z/2Z is presented by \<langle>a | a^2\<rangle>.\<close>
  have hdc: "top1_is_dunce_cap_on X TX (2::nat)"
    using assms(1) True unfolding top1_is_m_fold_projective_on_def by (by5000 auto)
  from Theorem_73_4_dunce_cap[OF _ hdc assms(2)]
  have hiso: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_Zn_group 2) (top1_Zn_mul 2)"
    and hpres_raw: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg ({..<1}::nat set) { replicate 2 (0::nat, True) }
    \<and> top1_groups_isomorphic_on G mul
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
    by (by100 simp)+
  \<comment> \<open>Match: {..<1} = {..<m} and replicate 2 = [(0,T),(0,T)] = concat for m=1.\<close>
  have hrep_eq: "replicate 2 (0::nat, True) = [(0, True), (0, True)]" by (by5000 eval)
  have hconcat_eq: "concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<1]) = [(0::nat, True), (0, True)]"
    by (by5000 eval)
  have hm_eq: "{..<m} = ({..<1}::nat set)" using True by (by100 simp)
  have hrel_eq: "{ replicate 2 (0::nat, True) }
      = { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }"
    using True hrep_eq hconcat_eq by (by100 simp)
  from hpres_raw show ?thesis unfolding hm_eq[symmetric] hrel_eq[symmetric] .
next
  case False
  \<comment> \<open>Case m \<ge> 2: Standard approach via polygonal quotient + Theorem 72.1.\<close>
  have hm2: "2 \<le> m" using assms(1) False unfolding top1_is_m_fold_projective_on_def by (by100 blast)
  have hscheme: "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
    using assms(1) False unfolding top1_is_m_fold_projective_on_def by (by100 blast)
  let ?scheme = "top1_m_projective_scheme m"
  have hlen: "length ?scheme \<ge> 3"
    using projective_scheme_length hm2 by (by100 simp)
  have hvc: "\<forall>(q'::real\<times>real\<Rightarrow>'a) (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
      (\<forall>i<length ?scheme. \<forall>j<length ?scheme.
        fst (?scheme!i) = fst (?scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q' ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
           (1-t) * vy i + t * vy (Suc i mod length ?scheme))
         = (if snd (?scheme!i) = snd (?scheme!j)
            then q' ((1-t) * vx j + t * vx (Suc j mod length ?scheme),
                    (1-t) * vy j + t * vy (Suc j mod length ?scheme))
            else q' (t * vx j + (1-t) * vx (Suc j mod length ?scheme),
                    t * vy j + (1-t) * vy (Suc j mod length ?scheme)))))
      \<longrightarrow> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. q' (vx i, vy i) = q' (vx j, vy j))"
    using projective_scheme_vertex_connectivity[OF hm2] by (by100 simp)
  \<comment> \<open>All entries in the projective scheme have direction True.\<close>
  have htd: "\<forall>\<alpha>\<in>fst ` set ?scheme.
      \<exists>i<length ?scheme. fst (?scheme!i) = \<alpha> \<and> snd (?scheme!i) = True"
  proof (intro ballI)
    fix \<alpha> assume "\<alpha> \<in> fst ` set ?scheme"
    then obtain x where "x \<in> set ?scheme" "fst x = \<alpha>" by (by100 blast)
    \<comment> \<open>All entries have True direction.\<close>
    hence "snd x = True" unfolding top1_m_projective_scheme_def by (by5000 auto)
    have "x = (\<alpha>, True)"
    proof -
      have "x = (fst x, snd x)" by (by100 simp)
      thus ?thesis using \<open>fst x = \<alpha>\<close> \<open>snd x = True\<close> by (by100 simp)
    qed
    hence "(\<alpha>, True) \<in> set ?scheme" using \<open>x \<in> set ?scheme\<close> by (by100 simp)
    hence "\<exists>i<length ?scheme. ?scheme!i = (\<alpha>, True)"
      by (simp add: in_set_conv_nth)
    then obtain i where "i < length ?scheme" "?scheme!i = (\<alpha>, True)"
      by (by100 blast)
    thus "\<exists>i<length ?scheme. fst (?scheme!i) = \<alpha> \<and> snd (?scheme!i) = True"
      by (by100 force)
  qed
  \<comment> \<open>Vertex identification from quotient\_of\_scheme\_extract\_full.\<close>
  have hvert: "\<exists>P q' vx vy.
      top1_is_polygonal_region_on P (length ?scheme)
    \<and> top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q'
    \<and> (\<forall>i<length ?scheme. (vx i, vy i) \<in> P)
    \<and> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. q' (vx i, vy i) = q' (vx j, vy j))
    \<and> (\<forall>i<length ?scheme. \<forall>j<length ?scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
        q' ((1-t) * vx i + t * vx (Suc i mod length ?scheme),
           (1-t) * vy i + t * vy (Suc i mod length ?scheme))
      = q' ((1-s) * vx j + s * vx (Suc j mod length ?scheme),
           (1-s) * vy j + s * vy (Suc j mod length ?scheme))
      \<longrightarrow> (i = j \<and> t = s)
        \<or> (fst (?scheme!i) = fst (?scheme!j) \<and>
           (if snd (?scheme!i) = snd (?scheme!j) then s = t else s = 1 - t)))"
  proof -
    \<comment> \<open>Extract ALL properties from quotient\_of\_scheme\_extract\_full (like torus case).\<close>
    obtain P0 q0 vx0 vy0 where
      hP0: "top1_is_polygonal_region_on P0 (length ?scheme)"
      and hq0: "top1_quotient_map_on P0 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P0) X TX q0"
      and hlen0: "length ?scheme \<ge> 3"
      and hverts0: "\<forall>i<length ?scheme. (vx0 i, vy0 i) \<in> P0"
      and hP0_hull: "P0 = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length ?scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length ?scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length ?scheme. coeffs i * vx0 i)
                       \<and> y = (\<Sum>i<length ?scheme. coeffs i * vy0 i)}"
      and hedge0: "\<forall>i<length ?scheme. \<forall>j<length ?scheme.
          fst (?scheme!i) = fst (?scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q0 ((1-t) * vx0 i + t * vx0 (Suc i mod length ?scheme),
             (1-t) * vy0 i + t * vy0 (Suc i mod length ?scheme))
           = (if snd (?scheme!i) = snd (?scheme!j)
              then q0 ((1-t) * vx0 j + t * vx0 (Suc j mod length ?scheme),
                      (1-t) * vy0 j + t * vy0 (Suc j mod length ?scheme))
              else q0 (t * vx0 j + (1-t) * vx0 (Suc j mod length ?scheme),
                      t * vy0 j + (1-t) * vy0 (Suc j mod length ?scheme))))"
      and hinterior0: "\<forall>p\<in>P0. (\<forall>i<length ?scheme. \<forall>t\<in>I_set.
            p \<noteq> ((1-t) * vx0 i + t * vx0 (Suc i mod length ?scheme),
                  (1-t) * vy0 i + t * vy0 (Suc i mod length ?scheme)))
       \<longrightarrow> (\<forall>p'\<in>P0. q0 p = q0 p' \<longrightarrow> p = p')"
      and hno_extra0: "\<forall>i<length ?scheme. \<forall>j<length ?scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q0 ((1-t) * vx0 i + t * vx0 (Suc i mod length ?scheme),
             (1-t) * vy0 i + t * vy0 (Suc i mod length ?scheme))
        = q0 ((1-s) * vx0 j + s * vx0 (Suc j mod length ?scheme),
             (1-s) * vy0 j + s * vy0 (Suc j mod length ?scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (?scheme!i) = fst (?scheme!j) \<and>
             (if snd (?scheme!i) = snd (?scheme!j) then s = t else s = 1 - t))"
      by (rule quotient_of_scheme_extract_full[OF hscheme])
    \<comment> \<open>Derive vertex identification from hvc and hedge0.\<close>
    have hvert_id0: "\<forall>i<length ?scheme. \<forall>j<length ?scheme.
        q0 (vx0 i, vy0 i) = q0 (vx0 j, vy0 j)"
      using hvc[rule_format, of q0 vx0 vy0] hedge0 by (by100 blast)
    show ?thesis
      apply (rule exI[of _ P0], rule exI[of _ q0], rule exI[of _ vx0], rule exI[of _ vy0])
      apply (intro conjI)
      apply (rule hP0)
      apply (rule hq0)
      apply (rule hverts0)
      apply (rule hvert_id0)
      apply (rule hno_extra0)
      done
  qed
  have hlabels: "fst ` set ?scheme = {..<m}"
  proof -
    have "fst ` set ?scheme = fst ` set (concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]))"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    also have "\<dots> = {..<m}"
    proof (induction m)
      case 0 thus ?case by (by100 simp)
    next
      case (Suc m)
      have "concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<Suc m])
          = concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) @ [(m, True), (m, True)]"
        by (by100 simp)
      hence "fst ` set (concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<Suc m]))
          = fst ` set (concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m])) \<union> {m}"
        by (by5000 auto)
      also have "\<dots> = {..<m} \<union> {m}" using Suc.IH by (by100 simp)
      also have "\<dots> = {..<Suc m}" by (by100 auto)
      finally show ?case .
    qed
    finally show ?thesis .
  qed
  have hrelator: "{ map (\<lambda>(s,b). (s, b)) ?scheme }
      = { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }"
  proof -
    have "map (\<lambda>(s,b). (s, b)) ?scheme = ?scheme" by (by100 simp)
    thus ?thesis unfolding top1_m_projective_scheme_def by (by100 simp)
  qed
  \<comment> \<open>Apply Theorem 74.2.\<close>
  have h742: "\<exists>(G :: (real \<Rightarrow> 'a) set set set) mul e invg.
      top1_group_presented_by_on G mul e invg (fst ` set ?scheme)
        { map (\<lambda>(s,b). (s, b)) ?scheme }
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)"
    using Theorem_74_2_scheme_presentation[OF hscheme assms(2) hlen hvert htd hvc] .
  show ?thesis using h742 hlabels hrelator by (by5000 simp)
qed
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

text \<open>Any free group on a finite set S is realized as \<pi>_1 of a wedge of |S| circles
  (which is a connected graph). This is the geometric realization step.\<close>
lemma free_group_realized_by_wedge:
  fixes F :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_group_full_on F mul e invg \<iota> S"
      and "finite S"
  shows "\<exists>(X :: 'a set) TX (x0 :: 'a).
      top1_is_graph_on X TX \<and> top1_connected_on X TX \<and> x0 \<in> X
    \<and> top1_groups_isomorphic_on F mul
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)"
  sorry \<comment> \<open>Construct a wedge of |S| circles. Apply Theorem 71.1: \<pi>_1(wedge) is free.
     Free groups on equinumerous sets are isomorphic (free\_group\_full\_reindex).
     Wedge is a graph (arcs = circles, coherent topology). Wedge is connected.\<close>

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
  proof -
    have "finite S" using assms(2) by (cases "finite S", by100 simp, by100 simp)
    note hrealiz = free_group_realized_by_wedge[OF assms(1) this]
    \<comment> \<open>Extract from the 3-var existential with 4 conjuncts.\<close>
    from hrealiz obtain X' :: "'a set" and TX' :: "'a set set" and x0' :: 'a where
      hconj: "top1_is_graph_on X' TX' \<and> top1_connected_on X' TX' \<and> x0' \<in> X'
      \<and> top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X' TX' x0') (top1_fundamental_group_mul X' TX' x0')"
      by (by5000 fast)
    show ?thesis
      apply (rule that[of X' TX' x0'])
      using hconj by (by100 blast)+
  qed
  \<comment> \<open>Choose covering E \<rightarrow> X with p_*(\<pi>_1(E)) = H. E is k-fold cover.\<close>
  obtain E :: "'b set" and TE :: "'b set set" and p :: "'b \<Rightarrow> 'a" and e0 :: 'b
    where hcov: "top1_covering_map_on E TE X TX p"
      and hE_conn: "top1_connected_on E TE"
      and he0: "e0 \<in> E"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).\<close>
  \<comment> \<open>E is a graph (Theorem 83.4). \<pi>_1(E) is free (Theorem 84.7).
     Note: Theorem 84.7 is defined later in this file, so cannot be directly called here.
     E has k \<times> (edges of X) edges and k \<times> (vertices of X) vertices.
     \<chi>(E) = k \<cdot> \<chi>(X) = k \<cdot> (-n). So rank = 1 - \<chi>(E) = 1 + kn = k(n-1) + 1.\<close>
  show ?thesis
    sorry \<comment> \<open>\<pi>_1(E) is free (Theorem 84.7). Euler char gives rank kn+1.\<close>
qed




text \<open>Lemma 84.6 (Munkres): Two-component SvK generation.
  If X = U \<union> V open, U \<inter> V = A \<union> B disjoint open PC,
  U and V simply connected, \<alpha> path in U from a\<in>A to b\<in>B,
  \<beta> path in V from b to a, then [\<alpha>*\<beta>] generates \<pi>_1(X, a).
  Combined with Theorem 63.1 ([\<alpha>*\<beta>] non-trivial), gives \<pi>_1(X, a) \<cong> \<Z>.\<close>
lemma Lemma_84_6_two_component_generation:
  assumes hTX: "is_topology_on_strict X TX"
      and hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
      and hcover: "U \<union> V = X"
      and hUV_split: "U \<inter> V = A \<union> B"
      and hAB_disj: "A \<inter> B = {}"
      and hA_open: "openin_on X TX A" and hB_open: "openin_on X TX B"
      and hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
      and hB_pc: "top1_path_connected_on B (subspace_topology X TX B)"
      and ha: "a \<in> A" and hb: "b \<in> B"
      and halpha: "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
      and hbeta: "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
      and hU_sc: "top1_simply_connected_on U (subspace_topology X TX U)"
      and hV_sc: "top1_simply_connected_on V (subspace_topology X TX V)"
  shows "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX a)
      (top1_fundamental_group_mul X TX a)
      top1_Z_group top1_Z_mul"
  sorry

text \<open>Helper: free group structure transfers across isomorphism.\<close>
lemma free_group_iso_transfer:
  assumes "top1_is_free_group_full_on G mulG eG invgG \<iota> S"
      and "top1_groups_isomorphic_on G mulG H mulH"
      and "top1_is_group_on H mulH eH invgH"
  shows "\<exists>\<iota>'. top1_is_free_group_full_on H mulH eH invgH \<iota>' S"
proof -
  from assms(2) obtain f where hf: "top1_group_iso_on G mulG H mulH f"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  from free_group_invariant_under_iso[OF assms(1) hf assms(3)]
  show ?thesis by (by100 blast)
qed

text \<open>Helper: tree union arcs (with endpoints in tree) is path-connected.
  Used in Theorem 84.7 for targets of deformation retractions.\<close>
lemma tree_union_arcs_path_connected:
  assumes hTX: "is_topology_on X TX"
      and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hS_fin: "finite S"
      and hS_arcs: "\<forall>A\<in>S. top1_is_arc_on A (subspace_topology X TX A) \<and> A \<subseteq> X"
      and hS_endpts: "\<forall>A\<in>S. \<exists>e. e \<in> T \<and> e \<in> A"
      and hx0: "x0 \<in> T"
  shows "top1_path_connected_on (T \<union> \<Union>S) (subspace_topology X TX (T \<union> \<Union>S))"
proof -
  let ?Y = "T \<union> \<Union>S"
  have hY_sub: "?Y \<subseteq> X" using hT_sub hS_arcs by (by100 blast)
  have hY_top: "is_topology_on ?Y (subspace_topology X TX ?Y)"
    by (rule subspace_topology_is_topology_on[OF hTX]) (use hY_sub in blast)
  have hT_pc: "top1_path_connected_on T (subspace_topology X TX T)"
    using tree_simply_connected[OF hT_tree] top1_simply_connected_on_path_connected by (by100 blast)
  \<comment> \<open>Each arc in S is PC.\<close>
  have hS_pc: "\<forall>A\<in>S. top1_path_connected_on A (subspace_topology X TX A)"
  proof (intro ballI)
    fix A assume "A \<in> S"
    have "top1_is_arc_on A (subspace_topology X TX A)" using hS_arcs \<open>A \<in> S\<close> by (by100 blast)
    obtain h where hh: "top1_homeomorphism_on top1_unit_interval
        top1_unit_interval_topology A (subspace_topology X TX A) h"
      using \<open>top1_is_arc_on A _\<close> unfolding top1_is_arc_on_def by (by100 blast)
    have hI_pc: "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "top1_unit_interval \<noteq> {}" unfolding top1_unit_interval_def by (by100 auto)
      have "\<And>x y t. x \<in> top1_unit_interval \<Longrightarrow> y \<in> top1_unit_interval \<Longrightarrow>
          0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> (1 - t) * x + t * y \<in> top1_unit_interval"
      proof -
        fix x y t :: real
        assume "x \<in> top1_unit_interval" "y \<in> top1_unit_interval" "0 \<le> t" "t \<le> 1"
        have "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
          using \<open>x \<in> _\<close> \<open>y \<in> _\<close> unfolding top1_unit_interval_def by (by100 simp)+
        have "1 - t \<ge> 0" using \<open>t \<le> 1\<close> by (by100 linarith)
        have "(1 - t) * x \<ge> 0" using \<open>1 - t \<ge> 0\<close> \<open>0 \<le> x\<close> by (by100 simp)
        have "t * y \<ge> 0" using \<open>0 \<le> t\<close> \<open>0 \<le> y\<close> by (by100 simp)
        have "(1 - t) * x \<le> 1 - t" using mult_left_mono[OF \<open>x \<le> 1\<close> \<open>1 - t \<ge> 0\<close>] by (by100 simp)
        have "t * y \<le> t" using mult_left_mono[OF \<open>y \<le> 1\<close> \<open>0 \<le> t\<close>] by (by100 simp)
        show "(1 - t) * x + t * y \<in> top1_unit_interval"
          unfolding top1_unit_interval_def using \<open>(1-t)*x \<ge> 0\<close> \<open>t*y \<ge> 0\<close>
            \<open>(1-t)*x \<le> 1-t\<close> \<open>t*y \<le> t\<close> by (by100 simp)
      qed
      from convex_real_subspace_path_connected[OF \<open>top1_unit_interval \<noteq> {}\<close> this]
      show ?thesis unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
    qed
    show "top1_path_connected_on A (subspace_topology X TX A)"
      using homeomorphism_preserves_path_connected[OF hh hI_pc] .
  qed
  \<comment> \<open>Use F = {T \\<union> A | A \\<in> S} \\<union> {T}. Each contains x0. Each is PC.\<close>
  let ?F = "insert T ((\<lambda>A. T \<union> A) ` S)"
  have hF_fin: "finite ?F" using hS_fin by (by100 auto)
  have hF_cover: "?Y = \<Union>?F" by (by100 blast)
  have hF_sub: "\<forall>B\<in>?F. B \<subseteq> ?Y" by (by100 blast)
  have hF_x0: "\<forall>B\<in>?F. x0 \<in> B" using hx0 by (by100 blast)
  \<comment> \<open>Each B \\<in> F is PC in subspace of Y.\<close>
  have hF_pc: "\<forall>B\<in>?F. top1_path_connected_on B (subspace_topology ?Y (subspace_topology X TX ?Y) B)"
  proof -
    \<comment> \<open>Helper: T \\<union> A is PC for any arc A with endpoint in T.\<close>
    have hTA_pc: "\<And>A. A \<in> S \<Longrightarrow> top1_path_connected_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
    proof -
      fix A assume "A \<in> S"
      have "A \<subseteq> X" using hS_arcs \<open>A \<in> S\<close> by (by100 blast)
      have hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
        using hS_pc \<open>A \<in> S\<close> by (by100 blast)
      obtain e0 where "e0 \<in> T" "e0 \<in> A" using hS_endpts \<open>A \<in> S\<close> by (by100 blast)
      have hTA_top: "is_topology_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
        by (rule subspace_topology_is_topology_on[OF hTX])
           (use hT_sub \<open>A \<subseteq> X\<close> in blast)
      \<comment> \<open>Use path\\_connected\\_finite\\_union\\_common\\_point with {T, A} and e0.\<close>
      let ?Fj = "{T, A}"
      have "\<forall>C\<in>?Fj. C \<subseteq> T \<union> A" by (by100 blast)
      have "\<forall>C\<in>?Fj. e0 \<in> C" using \<open>e0 \<in> T\<close> \<open>e0 \<in> A\<close> by (by100 blast)
      have hT_pc_TA: "top1_path_connected_on T
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) T)"
        using hT_pc subspace_topology_trans[of T "T \<union> A" X TX] by (by100 simp)
      have hA_pc_TA: "top1_path_connected_on A
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) A)"
        using hA_pc subspace_topology_trans[of A "T \<union> A" X TX] by (by100 simp)
      have "\<forall>C\<in>?Fj. top1_path_connected_on C
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) C)"
        using hT_pc_TA hA_pc_TA by (by100 blast)
      from path_connected_finite_union_common_point[OF hTA_top _
          \<open>\<forall>C\<in>?Fj. C \<subseteq> T \<union> A\<close>
          \<open>\<forall>C\<in>?Fj. top1_path_connected_on C _\<close>
          \<open>\<forall>C\<in>?Fj. e0 \<in> C\<close>]
      show "top1_path_connected_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
        by (by100 simp)
    qed
    show ?thesis
    proof (intro ballI)
      fix B assume "B \<in> ?F"
      have hB_sub_Y: "B \<subseteq> ?Y" using hF_sub \<open>B \<in> ?F\<close> by (by100 blast)
      have "subspace_topology ?Y (subspace_topology X TX ?Y) B = subspace_topology X TX B"
        by (rule subspace_topology_trans[OF hB_sub_Y])
      have "top1_path_connected_on B (subspace_topology X TX B)"
      proof -
        from \<open>B \<in> ?F\<close> consider "B = T" | "\<exists>A\<in>S. B = T \<union> A" by (by100 blast)
        thus ?thesis
        proof cases
          case 1 thus ?thesis using hT_pc by (by100 simp)
        next
          case 2
          then obtain A where "A \<in> S" "B = T \<union> A" by (by100 blast)
          thus ?thesis using hTA_pc[OF \<open>A \<in> S\<close>] by (by100 simp)
        qed
      qed
      thus "top1_path_connected_on B (subspace_topology ?Y (subspace_topology X TX ?Y) B)"
        using \<open>subspace_topology ?Y _ B = _\<close> by (by100 simp)
    qed
  qed
  from path_connected_finite_union_common_point[OF hY_top hF_fin hF_sub hF_pc hF_x0 hF_cover]
  show ?thesis .
qed

text \<open>Helper: deformation retract onto path-connected subspace implies path-connected.
  If X deformation retracts onto A and A is path-connected, then X is path-connected.
  Proof: the homotopy H gives a path from x to H(x,1) \<in> A for each x \<in> X.\<close>
text \<open>Helper: trivial \<pi>_1 carrier + path-connected \<Rightarrow> simply connected.\<close>
lemma trivial_pi1_imp_simply_connected:
  assumes "is_topology_on X TX"
      and "top1_path_connected_on X TX"
      and "x0 \<in> X"
      and "top1_fundamental_group_carrier X TX x0 =
          {top1_fundamental_group_id X TX x0}"
  shows "top1_simply_connected_on X TX"
proof -
  have "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
      top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX x0 f"
    \<comment> \<open>f's class \\<in> carrier = {id}, so class = id.\<close>
    have hcl: "{g. top1_loop_equiv_on X TX x0 f g} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hf by (by100 blast)
    hence hcl_id: "{g. top1_loop_equiv_on X TX x0 f g} =
        top1_fundamental_group_id X TX x0"
      using assms(4) by (by5000 force)
    \<comment> \<open>f \\<in> class(f) by reflexivity.\<close>
    have hpath: "top1_is_path_on X TX x0 x0 f"
      using hf unfolding top1_is_loop_on_def by (by100 blast)
    have "top1_loop_equiv_on X TX x0 f f"
      unfolding top1_loop_equiv_on_def
      using hf Lemma_51_1_path_homotopic_refl[OF hpath] by (by100 blast)
    hence "f \<in> {g. top1_loop_equiv_on X TX x0 f g}" by (by100 blast)
    \<comment> \<open>So f \\<in> id\\_class = {g. loop\\_equiv(const, g)}.\<close>
    hence "f \<in> top1_fundamental_group_id X TX x0" using hcl_id by (by100 simp)
    hence "top1_loop_equiv_on X TX x0 (top1_constant_path x0) f"
      unfolding top1_fundamental_group_id_def by (by100 blast)
    hence "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) f"
      unfolding top1_loop_equiv_on_def by (by100 blast)
    show "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_sym) (rule \<open>top1_path_homotopic_on _ _ _ _ _ f\<close>)
  qed
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF assms(1) assms(2) assms(3)])
       (use \<open>\<forall>f. _\<close> in blast)
qed

lemma deformation_retract_path_connected:
  assumes hdr: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
  shows "top1_path_connected_on X TX"
proof -
  have hA_sub: "A \<subseteq> X"
    using conjunct1[OF hdr[unfolded top1_deformation_retract_of_on_def]] by (by100 blast)
  from hdr obtain H where
    hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H" and
    hH_0: "\<forall>x\<in>X. H (x, 0) = x" and
    hH_1: "\<forall>x\<in>X. H (x, 1) \<in> A" and
    hH_A: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    unfolding top1_deformation_retract_of_on_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>For each x \\<in> X, t \\<mapsto> H(x, t) is a path from x to H(x,1) \\<in> A.\<close>
  have hpath_to_A: "\<And>x. x \<in> X \<Longrightarrow> top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
  proof -
    fix x assume hx: "x \<in> X"
    \<comment> \<open>t \\<mapsto> H(x, t) = H \\<circ> (\\<lambda>t. (x, t)). The section \\<lambda>t. (x, t) is continuous I \\<rightarrow> X \\<times> I.\<close>
    have hsection: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>t. (x, t))"
      by (rule top1_continuous_map_on_section2[OF hTX hI_top hx])
    from top1_continuous_map_on_comp[OF hsection hH_cont]
    have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H (x, t))"
      unfolding comp_def by (by100 simp)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    show "top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
      unfolding top1_is_path_on_def
      using hcomp hH_0[rule_format, OF hx] hH_1[rule_format, OF hx] h0_I h1_I
      by (by100 blast)
  qed
  show ?thesis unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
    \<comment> \<open>Path x \\<rightarrow> H(x,1) in X.\<close>
    have hpx: "top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
      by (rule hpath_to_A[OF hx])
    \<comment> \<open>Path H(y,1) \\<rightarrow> y in X (reverse of H(y, \\<cdot>)).\<close>
    have hpy: "top1_is_path_on X TX y (H (y, 1)) (\<lambda>t. H (y, t))"
      by (rule hpath_to_A[OF hy])
    have hpy_rev: "top1_is_path_on X TX (H (y, 1)) y (top1_path_reverse (\<lambda>t. H (y, t)))"
      by (rule top1_path_reverse_is_path[OF hpy])
    \<comment> \<open>Path H(x,1) \\<rightarrow> H(y,1) in A (path-connected).\<close>
    have hHx_A: "H (x, 1) \<in> A" using hH_1 hx by (by100 blast)
    have hHy_A: "H (y, 1) \<in> A" using hH_1 hy by (by100 blast)
    obtain g where hg: "top1_is_path_on A (subspace_topology X TX A) (H (x, 1)) (H (y, 1)) g"
      using hA_pc hHx_A hHy_A unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Lift g to X (A \\<subseteq> X).\<close>
    have hg_X: "top1_is_path_on X TX (H (x, 1)) (H (y, 1)) g"
      by (rule path_in_subspace_is_path_in_ambient[OF hTX hA_sub hg])
    \<comment> \<open>Concatenate: x \\<rightarrow> H(x,1) \\<rightarrow> H(y,1) \\<rightarrow> y.\<close>
    have hpxg: "top1_is_path_on X TX x (H (y, 1)) (top1_path_product (\<lambda>t. H (x, t)) g)"
      by (rule top1_path_product_is_path[OF hTX hpx hg_X])
    have hfinal: "top1_is_path_on X TX x y
        (top1_path_product (top1_path_product (\<lambda>t. H (x, t)) g) (top1_path_reverse (\<lambda>t. H (y, t))))"
      by (rule top1_path_product_is_path[OF hTX hpxg hpy_rev])
    show "\<exists>f. top1_is_path_on X TX x y f" by (rule exI[of _ _]) (rule hfinal)
  qed
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
  \<comment> \<open>Step 1: X is a graph, so extract arcs with full structure.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
    using assms(1) unfolding top1_is_graph_on_def by (by5000 auto)
  \<comment> \<open>Step 2: Choose a maximal tree T \<subseteq> X. A maximal tree exists by Zorn's lemma
     (or, for countable graphs, by explicit construction).\<close>
  obtain T :: "'a set" where hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_reaches: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
      and hx0_T: "x0 \<in> T"
      and hT_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hT_coverage: "T = \<Union>{A \<in> \<A>. A \<subseteq> T}"
      and hT_max_raw: "\<forall>T'. T' \<subseteq> X \<longrightarrow> T \<subseteq> T' \<longrightarrow> top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow>
          (\<forall>A\<in>\<A>. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)) \<longrightarrow>
          T' = \<Union>{A \<in> \<A>. A \<subseteq> T'} \<longrightarrow> T' = T"
  proof -
    from connected_graph_has_maximal_tree[OF assms(1) assms(2) assms(3) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh]
    obtain T0 where hT0: "top1_is_tree_on T0 (subspace_topology X TX T0)"
        and hT0_sub: "T0 \<subseteq> X" and hT0_x0: "x0 \<in> T0"
        and hT0_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T0 \<or> A \<inter> T0 \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        and hT0_coverage: "T0 = \<Union>{A \<in> \<A>. A \<subseteq> T0}"
        and hT0_max: "\<forall>T'. T' \<subseteq> X \<longrightarrow> T0 \<subseteq> T' \<longrightarrow> top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow>
            (\<forall>A\<in>\<A>. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)) \<longrightarrow>
            T' = \<Union>{A \<in> \<A>. A \<subseteq> T'} \<longrightarrow> T' = T0"
      by (by5000 auto)
    have hT0_reaches: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T0. w \<in> A)"
      by (rule maximal_tree_reaches_all_arcs[OF assms(1) assms(2) assms(3) h\<A> h\<A>_cover
          h\<A>_inter h\<A>_coh hT0 hT0_sub hT0_x0 hT0_max hT0_subgraph hT0_coverage])
    show ?thesis using that[OF hT0 hT0_sub hT0_reaches hT0_x0 hT0_subgraph hT0_coverage hT0_max]
      by (by100 blast)
  qed
  \<comment> \<open>Step 3 (Munkres 84.7, book-faithful SvK approach):
     Non-tree arcs A\<alpha> with both endpoints in T generate \<pi>\_1(X, x0).
     Finite case: induction using svk\_free\_product\_free.
     Infinite case: compactness reduction to finite.\<close>
  \<comment> \<open>Non-tree arcs.\<close>
  let ?NT = "{A \<in> \<A>. \<not> A \<subseteq> T}"
  \<comment> \<open>Each non-tree arc has both endpoints in T (from maximal tree hT\_max).\<close>
  have hNT_endpoints: "\<forall>A\<in>?NT. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> T"
  proof (intro ballI)
    fix A e assume hA: "A \<in> ?NT" and he: "e \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
    have "A \<in> \<A>" using hA by (by100 blast)
    have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
    have he_X: "e \<in> X" using he \<open>A \<subseteq> X\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>From hT\_reaches: e is in some arc B that meets T.\<close>
    from hT_reaches[rule_format, OF he_X]
    obtain B where hB: "B \<in> \<A>" "e \<in> B" "\<exists>w\<in>T. w \<in> B" by (by100 blast)
    then obtain w where hw: "w \<in> T" "w \<in> B" by (by100 blast)
    show "e \<in> T"
    proof (cases "B \<subseteq> T")
      case True thus ?thesis using hB(2) by (by100 blast)
    next
      case False
      \<comment> \<open>B is a non-tree arc. e is endpoint of A, and e \\<in> B.\<close>
      from hT_subgraph[rule_format, OF hB(1)] False
      have hBT_ep: "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)" by (by100 blast)
      \<comment> \<open>w \\<in> B \\<inter> T, so w is an endpoint of B.\<close>
      have "w \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
        using hw hBT_ep by (by100 blast)
      \<comment> \<open>e is endpoint of A, e \\<in> B. If A \\<noteq> B: e \\<in> A \\<inter> B \\<subseteq> endpoints(B).\<close>
      have "e \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
      proof (cases "A = B")
        case True thus ?thesis using he True by (by100 simp)
      next
        case False
        have "e \<in> A \<inter> B" using he hB(2) unfolding top1_arc_endpoints_on_def by (by100 blast)
        from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> hB(1) False]
        show ?thesis using \<open>e \<in> A \<inter> B\<close> by (by100 blast)
      qed
      \<comment> \<open>Now e and w are both endpoints of B. B has \\<le> 2 endpoints.\<close>
      \<comment> \<open>If e = w: e \\<in> T.\<close>
      \<comment> \<open>If e \\<noteq> w: B connects e to w with B \\<inter> T \\<subseteq> {e,w} and w \\<in> T but e \\<notin> T (by assumption).
         Then T \\<union> B is connected + SC + graph \\<Rightarrow> tree, contradicting T's maximality.\<close>
      show "e \<in> T"
      proof (rule ccontr)
        assume "e \<notin> T"
        hence "e \<noteq> w" using hw(1) by (by100 blast)
        \<comment> \<open>B \\<inter> T = {w} (w is the only T-endpoint of B, since e \\<notin> T).\<close>
        have "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)" using hBT_ep .
        \<comment> \<open>Contradiction via maximality: T \\<union> B would be a strictly larger tree.\<close>
        \<comment> \<open>This requires T \\<union> B is a tree + satisfies subgraph/coverage conditions.\<close>
        \<comment> \<open>card(B \\<inter> T) = 1 (w is the only T-point of B).\<close>
        have hBT_card: "card (B \<inter> T) = 1"
        proof -
          have "B \<inter> T \<subseteq> {w}"
          proof -
            \<comment> \<open>endpoints(B) = {h'(0), h'(1)} for homeomorphism h'. |endpoints| \\<le> 2.\<close>
            have "top1_is_arc_on B (subspace_topology X TX B)" using h\<A> hB(1) by (by100 blast)
            then obtain h' where hh': "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                B (subspace_topology X TX B) h'" unfolding top1_is_arc_on_def by (by100 blast)
            have hX_strict: "is_topology_on_strict X TX"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            have hX_haus_loc: "is_hausdorff_on X TX"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            have "B \<subseteq> X" using h\<A> hB(1) by (by100 blast)
            from arc_endpoints_are_boundary[OF hX_strict hX_haus_loc \<open>B \<subseteq> X\<close>
                \<open>top1_is_arc_on B _\<close> hh']
            have hep_eq: "top1_arc_endpoints_on B (subspace_topology X TX B) = {h' 0, h' 1}" .
            \<comment> \<open>e \\<in> endpoints(B) and e \\<notin> T. So B \\<inter> T \\<subseteq> endpoints(B) - {e} \\<subseteq> {w}.\<close>
            have "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)" using hBT_ep .
            hence "B \<inter> T \<subseteq> {h' 0, h' 1}" using hep_eq by (by100 simp)
            have "e \<in> {h' 0, h' 1}" using \<open>e \<in> top1_arc_endpoints_on B _\<close> hep_eq by (by100 simp)
            have "B \<inter> T \<subseteq> {h' 0, h' 1} - {e}" using \<open>B \<inter> T \<subseteq> {h' 0, h' 1}\<close> \<open>e \<notin> T\<close> by (by100 blast)
            have "w \<in> {h' 0, h' 1}" using \<open>w \<in> top1_arc_endpoints_on B _\<close> hep_eq by (by100 simp)
            have "{h' 0, h' 1} - {e} \<subseteq> {w}"
            proof (cases "e = h' 0")
              case True hence "{h' 0, h' 1} - {e} = {h' 1} - {e}" by (by100 blast)
              also have "... \<subseteq> {h' 1}" by (by100 blast)
              finally show ?thesis using \<open>w \<in> {h' 0, h' 1}\<close> True \<open>e \<noteq> w\<close> by (by100 blast)
            next
              case False hence "e = h' 1" using \<open>e \<in> {h' 0, h' 1}\<close> by (by100 blast)
              hence "{h' 0, h' 1} - {e} = {h' 0} - {e}" by (by100 blast)
              also have "... \<subseteq> {h' 0}" by (by100 blast)
              finally show ?thesis using \<open>w \<in> {h' 0, h' 1}\<close> \<open>e = h' 1\<close> \<open>e \<noteq> w\<close> by (by100 blast)
            qed
            thus "B \<inter> T \<subseteq> {w}" using \<open>B \<inter> T \<subseteq> {h' 0, h' 1} - {e}\<close> by (by100 blast)
          qed
          moreover have "w \<in> B \<inter> T" using hw by (by100 blast)
          ultimately have "B \<inter> T = {w}" by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>B \\<inter> T \\<noteq> {}.\<close>
        have hBT_ne: "B \<inter> T \<noteq> {}" using hw by (by100 blast)
        \<comment> \<open>T \\<union> B is a tree (graph + connected + SC). Tree because B meets T at 1 endpoint.\<close>
        have hB_sub: "B \<subseteq> X" using h\<A> hB(1) by (by100 blast)
        have hTB_graph: "top1_is_graph_on (T \<union> B) (subspace_topology X TX (T \<union> B))"
        proof -
          let ?\<A>TB = "{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
          have h_arcs: "\<forall>A'\<in>?\<A>TB. A' \<subseteq> X \<and> top1_is_arc_on A' (subspace_topology X TX A')"
            using h\<A> by (by100 blast)
          have h_cover_loc: "\<Union>?\<A>TB \<subseteq> X" using h\<A> by (by100 blast)
          have h_inter_loc: "\<forall>A'\<in>?\<A>TB. \<forall>B'\<in>?\<A>TB. A' \<noteq> B' \<longrightarrow>
               A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')
             \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology X TX B')
             \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2"
            using h\<A>_inter by (by100 blast)
          have "\<Union>?\<A>TB = T \<union> B"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Union>?\<A>TB" thus "x \<in> T \<union> B" by (by100 blast)
          next
            fix x assume "x \<in> T \<union> B"
            thus "x \<in> \<Union>?\<A>TB"
            proof
              assume "x \<in> T"
              hence "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T}" using hT_coverage by (by100 simp)
              thus ?thesis by (by100 blast)
            next
              assume "x \<in> B"
              have "B \<in> ?\<A>TB" using hB(1) by (by100 blast)
              thus ?thesis using \<open>x \<in> B\<close> by (by100 blast)
            qed
          qed
          have hTB_sub_X: "T \<union> B \<subseteq> X" using hT_sub hB_sub by (by100 blast)
          have h_coh_loc: "\<forall>D. D \<subseteq> \<Union>?\<A>TB \<longrightarrow>
              (closedin_on (\<Union>?\<A>TB) (subspace_topology X TX (\<Union>?\<A>TB)) D \<longleftrightarrow>
               (\<forall>A'\<in>?\<A>TB. closedin_on A' (subspace_topology X TX A') (A' \<inter> D)))"
          proof (intro allI impI iffI ballI)
            fix D A' assume hD: "D \<subseteq> \<Union>?\<A>TB"
                and hcl: "closedin_on (\<Union>?\<A>TB) (subspace_topology X TX (\<Union>?\<A>TB)) D" and "A' \<in> ?\<A>TB"
            have hX_top_loc: "is_topology_on X TX"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
            have "A' \<subseteq> \<Union>?\<A>TB" using \<open>A' \<in> ?\<A>TB\<close> by (by100 blast)
            have "\<Union>?\<A>TB \<subseteq> X" using h_cover_loc .
            from Theorem_17_2[OF subspace_topology_is_topology_on[OF hX_top_loc \<open>\<Union>?\<A>TB \<subseteq> X\<close>] \<open>A' \<subseteq> \<Union>?\<A>TB\<close>]
            have "closedin_on A' (subspace_topology (\<Union>?\<A>TB) (subspace_topology X TX (\<Union>?\<A>TB)) A') (A' \<inter> D)"
              using hcl by (by100 blast)
            have "subspace_topology (\<Union>?\<A>TB) (subspace_topology X TX (\<Union>?\<A>TB)) A' = subspace_topology X TX A'"
              by (rule subspace_topology_trans[OF \<open>A' \<subseteq> \<Union>?\<A>TB\<close>])
            thus "closedin_on A' (subspace_topology X TX A') (A' \<inter> D)"
              using \<open>closedin_on A' _ (A' \<inter> D)\<close> by (by100 simp)
          next
            fix D assume hD: "D \<subseteq> \<Union>?\<A>TB"
                and hall: "\<forall>A'\<in>?\<A>TB. closedin_on A' (subspace_topology X TX A') (A' \<inter> D)"
            have hD_sub_X: "D \<subseteq> X" using hD h_cover_loc by (by100 blast)
            have hX_top_loc: "is_topology_on X TX"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
            have "\<forall>A'\<in>\<A>. closedin_on A' (subspace_topology X TX A') (A' \<inter> D)"
            proof (intro ballI)
              fix A' assume "A' \<in> \<A>"
              show "closedin_on A' (subspace_topology X TX A') (A' \<inter> D)"
              proof (cases "A' \<in> ?\<A>TB")
                case True from hall[rule_format, OF True] show ?thesis .
              next
                case False hence "\<not> A' \<subseteq> T \<union> B" using \<open>A' \<in> \<A>\<close> by (by100 blast)
                \<comment> \<open>A' \\<inter> (T \\<union> B) \\<subseteq> endpoints(A'): from hT\\_subgraph + h\\<A>\\_inter.\<close>
                have hA'T_ep: "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                proof -
                  from hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>]
                  show ?thesis using \<open>\<not> A' \<subseteq> T \<union> B\<close> by (by100 blast)
                qed
                have hA'B_ep: "A' \<inter> B \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                proof (cases "A' = B")
                  case True thus ?thesis using \<open>\<not> A' \<subseteq> T \<union> B\<close> by (by100 blast)
                next
                  case False
                  from h\<A>_inter[rule_format, OF \<open>A' \<in> \<A>\<close> hB(1) False]
                  show ?thesis by (by100 blast)
                qed
                have "A' \<inter> (T \<union> B) \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                  using hA'T_ep hA'B_ep by (by100 blast)
                have "A' \<inter> D \<subseteq> A' \<inter> (T \<union> B)" using hD \<open>\<Union>?\<A>TB = T \<union> B\<close> by (by100 blast)
                hence "A' \<inter> D \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                  using \<open>A' \<inter> (T \<union> B) \<subseteq> _\<close> by (by100 blast)
                have hAD_sub_ep: "A' \<inter> D \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                  using \<open>A' \<inter> D \<subseteq> A' \<inter> (T \<union> B)\<close> \<open>A' \<inter> (T \<union> B) \<subseteq> _\<close> by (by100 blast)
                hence "finite (A' \<inter> D)"
                proof -
                  have "finite (top1_arc_endpoints_on A' (subspace_topology X TX A'))"
                  proof -
                    have "top1_is_arc_on A' (subspace_topology X TX A')" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                    then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                        A' (subspace_topology X TX A') h'" unfolding top1_is_arc_on_def by (by100 blast)
                    have hX_strict_loc: "is_topology_on_strict X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_haus_loc: "is_hausdorff_on X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have "A' \<subseteq> X" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict_loc hX_haus_loc \<open>A' \<subseteq> X\<close>
                        \<open>top1_is_arc_on A' _\<close> \<open>top1_homeomorphism_on _ _ A' _ h'\<close>]
                    show ?thesis by (by100 simp)
                  qed
                  thus ?thesis using finite_subset[OF hAD_sub_ep] by (by100 blast)
                qed
                have "A' \<subseteq> X" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                have hA'_haus: "is_hausdorff_on A' (subspace_topology X TX A')"
                proof -
                  have "is_hausdorff_on X TX" using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  from conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A' \<subseteq> X\<close> this show ?thesis by (by100 blast)
                qed
                have hA'_T1: "top1_T1_on A' (subspace_topology X TX A')" by (rule hausdorff_imp_T1_on[OF hA'_haus])
                have hA'_top: "is_topology_on A' (subspace_topology X TX A')"
                  using hA'_haus unfolding is_hausdorff_on_def by (by100 blast)
                have hAD_eq: "A' \<inter> D = \<Union>((\<lambda>x. {x}) ` (A' \<inter> D))" by (by100 blast)
                have hAD_fin: "finite ((\<lambda>x. {x}) ` (A' \<inter> D))" using \<open>finite (A' \<inter> D)\<close> by (by100 simp)
                have hAD_cl: "\<forall>U\<in>((\<lambda>x. {x}) ` (A' \<inter> D)). closedin_on A' (subspace_topology X TX A') U"
                proof (intro ballI)
                  fix U assume "U \<in> (\<lambda>x. {x}) ` (A' \<inter> D)"
                  then obtain y where "y \<in> A'" "U = {y}" by (by100 blast)
                  thus "closedin_on A' (subspace_topology X TX A') U"
                    using hA'_T1 unfolding top1_T1_on_def by (by100 blast)
                qed
                from closedin_Union_finite[OF hA'_top hAD_fin hAD_cl]
                show ?thesis using hAD_eq by (by100 simp)
              qed
            qed
            from h\<A>_coh[rule_format, OF hD_sub_X] this
            have "closedin_on X TX D" by (by100 blast)
            from Theorem_17_2[OF hX_top_loc hTB_sub_X]
            have "\<And>S. closedin_on (T \<union> B) (subspace_topology X TX (T \<union> B)) S \<longleftrightarrow>
                (\<exists>F. closedin_on X TX F \<and> S = F \<inter> (T \<union> B))" .
            hence "closedin_on (T \<union> B) (subspace_topology X TX (T \<union> B)) D"
              using \<open>closedin_on X TX D\<close> hD \<open>\<Union>?\<A>TB = T \<union> B\<close> by (by100 blast)
            thus "closedin_on (\<Union>?\<A>TB) (subspace_topology X TX (\<Union>?\<A>TB)) D"
              using \<open>\<Union>?\<A>TB = T \<union> B\<close> by (by100 simp)
          qed
          from subgraph_union_of_arcs_is_graph[OF assms(1) h_arcs h_cover_loc h_inter_loc h_coh_loc]
          show ?thesis using \<open>\<Union>?\<A>TB = T \<union> B\<close> by (by100 simp)
        qed
        have hT_closed: "closedin_on X TX T"
        proof -
          have "\<forall>A'\<in>\<A>. closedin_on A' (subspace_topology X TX A') (A' \<inter> T)"
          proof (intro ballI)
            fix A' assume "A' \<in> \<A>"
            from hT_subgraph[rule_format, OF this]
            show "closedin_on A' (subspace_topology X TX A') (A' \<inter> T)"
            proof
              assume "A' \<subseteq> T"
              have "A' \<inter> T = A'" using \<open>A' \<subseteq> T\<close> by (by100 blast)
              have "is_topology_on X TX"
                using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
              from closedin_carrier[OF subspace_topology_is_topology_on[OF this, of A']]
              show ?thesis using \<open>A' \<inter> T = A'\<close> h\<A> \<open>A' \<in> \<A>\<close> by (by100 simp)
            next
              assume "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
              \<comment> \<open>Finite \\<inter> in Hausdorff arc \\<Rightarrow> closed.\<close>
              have "finite (A' \<inter> T)"
              proof -
                have "finite (top1_arc_endpoints_on A' (subspace_topology X TX A'))"
                proof -
                  have "top1_is_arc_on A' (subspace_topology X TX A')" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                  then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      A' (subspace_topology X TX A') h'" unfolding top1_is_arc_on_def by (by100 blast)
                  have "A' \<subseteq> X" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                  have hX_strict: "is_topology_on_strict X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have hX_haus: "is_hausdorff_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  from arc_endpoints_are_boundary[OF hX_strict hX_haus
                      \<open>A' \<subseteq> X\<close> \<open>top1_is_arc_on A' _\<close> \<open>top1_homeomorphism_on _ _ A' _ h'\<close>]
                  show ?thesis by (by100 simp)
                qed
                thus ?thesis using finite_subset[OF \<open>A' \<inter> T \<subseteq> _\<close>] by (by100 blast)
              qed
              have "A' \<subseteq> X" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
              have hA'_haus: "is_hausdorff_on A' (subspace_topology X TX A')"
              proof -
                have "is_hausdorff_on X TX" using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                from conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A' \<subseteq> X\<close> this show ?thesis by (by100 blast)
              qed
              have hA'_T1: "top1_T1_on A' (subspace_topology X TX A')" by (rule hausdorff_imp_T1_on[OF hA'_haus])
              have hA'_top: "is_topology_on A' (subspace_topology X TX A')"
                using hA'_haus unfolding is_hausdorff_on_def by (by100 blast)
              have hAT_eq: "A' \<inter> T = \<Union>((\<lambda>x. {x}) ` (A' \<inter> T))" by (by100 blast)
              have hAT_fin: "finite ((\<lambda>x. {x}) ` (A' \<inter> T))" using \<open>finite (A' \<inter> T)\<close> by (by100 simp)
              have hAT_cl: "\<forall>U\<in>((\<lambda>x. {x}) ` (A' \<inter> T)). closedin_on A' (subspace_topology X TX A') U"
              proof (intro ballI)
                fix U assume "U \<in> (\<lambda>x. {x}) ` (A' \<inter> T)"
                then obtain y where "y \<in> A'" "U = {y}" by (by100 blast)
                thus "closedin_on A' (subspace_topology X TX A') U"
                  using hA'_T1 unfolding top1_T1_on_def by (by100 blast)
              qed
              from closedin_Union_finite[OF hA'_top hAT_fin hAT_cl]
              show ?thesis using hAT_eq by (by100 simp)
            qed
          qed
          from h\<A>_coh[rule_format, OF hT_sub] this show ?thesis by (by100 blast)
        qed
        have hTB_tree: "top1_is_tree_on (T \<union> B) (subspace_topology X TX (T \<union> B))"
          by (rule Lemma_84_2_tree_union_arc[OF assms(1) hT_tree hT_sub hB(1) h\<A>
              h\<A>_cover h\<A>_inter hBT_ne hBT_ep hBT_card hB_sub hT_closed hTB_graph])
        \<comment> \<open>T \\<union> B satisfies subgraph + coverage conditions.\<close>
        have hTB_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<union> B \<or>
            A \<inter> (T \<union> B) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof (intro ballI)
          fix A' assume "A' \<in> \<A>"
          show "A' \<subseteq> T \<union> B \<or> A' \<inter> (T \<union> B) \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
          proof (cases "A' \<subseteq> T")
            case True thus ?thesis by (by100 blast)
          next
            case False
            have hA'T: "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
              using hT_subgraph \<open>A' \<in> \<A>\<close> False by (by100 blast)
            show ?thesis
            proof (cases "A' = B")
              case True thus ?thesis by (by100 blast)
            next
              case False
              have "A' \<inter> B \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                using h\<A>_inter[rule_format, OF \<open>A' \<in> \<A>\<close> hB(1) False] by (by100 blast)
              thus ?thesis using hA'T by (by100 blast)
            qed
          qed
        qed
        have hTB_coverage: "T \<union> B = \<Union>{A \<in> \<A>. A \<subseteq> T \<union> B}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> T \<union> B"
          thus "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T \<union> B}"
          proof
            assume "x \<in> T"
            hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
            then obtain A' where "A' \<in> \<A>" "A' \<subseteq> T" "x \<in> A'" by (by100 blast)
            have "A' \<subseteq> T \<union> B" using \<open>A' \<subseteq> T\<close> by (by100 blast)
            thus ?thesis using \<open>A' \<in> \<A>\<close> \<open>x \<in> A'\<close> by (by100 blast)
          next
            assume "x \<in> B"
            have "B \<subseteq> T \<union> B" by (by100 blast)
            thus ?thesis using hB(1) \<open>x \<in> B\<close> by (by100 blast)
          qed
        next
          fix x assume "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T \<union> B}" thus "x \<in> T \<union> B" by (by100 blast)
        qed
        \<comment> \<open>Maximality: T = T \\<union> B.\<close>
        have "T \<union> B \<subseteq> X" using hT_sub hB_sub by (by100 blast)
        have "T \<subseteq> T \<union> B" by (by100 blast)
        have "T \<union> B = T"
          using hT_max_raw \<open>T \<union> B \<subseteq> X\<close> \<open>T \<subseteq> T \<union> B\<close> hTB_tree hTB_subgraph hTB_coverage
          by (by100 blast)
        hence "B \<subseteq> T" by (by100 blast)
        \<comment> \<open>But B \\<notin> T (from case False: B \\<nsubseteq> T).\<close>
        thus False using False hB(1) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3a: \<pi>\_1(X) is free. Apply Theorem 84.7 proof from Munkres.\<close>
  \<comment> \<open>Munkres 84.7, Steps 1-3 (SvK approach).
     Case 1: X = T (no non-tree arcs): \<pi>\_1 trivial, free on \<emptyset>.
     Case 2: non-tree arcs exist. \<pi>\_1(X) is free.
       Finite: induction using svk\_free\_product\_free.
       Infinite: compactness reduction to finite.\<close>
  show ?thesis
  proof (cases "?NT = {}")
    case True
    \<comment> \<open>No non-tree arcs: X = T (every arc is in T). X is simply connected.\<close>
    have "X = T"
    proof -
      have "\<forall>A\<in>\<A>. A \<subseteq> T" using True by (by100 blast)
      hence "\<Union>\<A> \<subseteq> T" by (by100 blast)
      hence "X \<subseteq> T" using h\<A>_cover by (by100 simp)
      thus ?thesis using hT_sub by (by100 blast)
    qed
    \<comment> \<open>T is simply connected (tree). \<pi>\_1(T, x0) is trivial. Trivial group is free on \<emptyset>.\<close>
    have "top1_simply_connected_on X TX"
    proof -
      have "top1_simply_connected_on T (subspace_topology X TX T)"
        using hT_tree unfolding top1_is_tree_on_def by (by100 blast)
      have "subspace_topology X TX T = TX"
      proof -
        have "is_topology_on_strict X TX"
          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
        have "\<forall>U\<in>TX. U \<subseteq> X"
          using \<open>is_topology_on_strict X TX\<close> unfolding is_topology_on_strict_def by (by100 blast)
        have "subspace_topology X TX X = TX" by (rule subspace_topology_self[OF \<open>\<forall>U\<in>TX. U \<subseteq> X\<close>])
        thus ?thesis using \<open>X = T\<close> by (by100 simp)
      qed
      have "top1_simply_connected_on T TX"
        using \<open>top1_simply_connected_on T (subspace_topology X TX T)\<close>
            \<open>subspace_topology X TX T = TX\<close> by (by100 simp)
      thus ?thesis using \<open>X = T\<close> by (by100 simp)
    qed
    \<comment> \<open>\<pi>\_1 of simply connected space is trivial. Trivial group is free on \<emptyset>.\<close>
    \<comment> \<open>Construct: G = {0::int}, free on S = {}. Then iso G \\<pi>\\_1(X).\<close>
    have hX_conn: "top1_connected_on X TX" using assms(2) .
    have hTX_top: "is_topology_on X TX"
      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
    \<comment> \<open>Step 1: The trivial group {0} is free on \\<emptyset>.\<close>
    have hfree: "top1_is_free_group_full_on {0::int} (\<lambda>x y. 0) 0 id (\<lambda>n::nat. 0::int) ({} :: nat set)"
      unfolding top1_is_free_group_full_on_def
    proof (intro conjI)
      show "top1_is_group_on {0::int} (\<lambda>x y. 0) 0 id"
        unfolding top1_is_group_on_def by (by100 auto)
      show "\<forall>s\<in>({}::nat set). (\<lambda>n::nat. 0::int) s \<in> {0::int}" by (by100 blast)
      show "inj_on (\<lambda>n::nat. 0::int) ({} :: nat set)" by (by100 simp)
      show "{0::int} = top1_subgroup_generated_on {0} (\<lambda>x y. 0) 0 id ((\<lambda>n::nat. 0::int) ` {})"
      proof -
        have "(\<lambda>n::nat. 0::int) ` {} = {}" by (by100 simp)
        hence "top1_subgroup_generated_on {0::int} (\<lambda>x y. 0) 0 id ((\<lambda>n::nat. 0::int) ` {}) =
            top1_subgroup_generated_on {0} (\<lambda>x y. 0) 0 id {}" by (by100 simp)
        also have "... = \<Inter>{ H. {} \<subseteq> H \<and> H \<subseteq> {0::int} \<and> top1_is_group_on H (\<lambda>x y. 0) 0 id}"
          unfolding top1_subgroup_generated_on_def by (by100 blast)
        also have "... = {0::int}"
        proof -
          have "{0::int} \<in> { H. {} \<subseteq> H \<and> H \<subseteq> {0::int} \<and> top1_is_group_on H (\<lambda>x y. 0) 0 id}"
          proof (intro CollectI conjI)
            show "{} \<subseteq> {0::int}" by (by100 blast)
            show "{0::int} \<subseteq> {0::int}" by (by100 blast)
            show "top1_is_group_on {0::int} (\<lambda>x y. 0) 0 id"
              unfolding top1_is_group_on_def by (by100 auto)
          qed
          moreover have "\<forall>H\<in>{ H. {} \<subseteq> H \<and> H \<subseteq> {0::int} \<and> top1_is_group_on H (\<lambda>x y. 0) 0 id}.
              {0::int} \<subseteq> H"
          proof (intro ballI)
            fix H assume "H \<in> { H. {} \<subseteq> H \<and> H \<subseteq> {0::int} \<and> top1_is_group_on H (\<lambda>x y. 0) 0 id}"
            hence "top1_is_group_on H (\<lambda>x y. 0) 0 id" "H \<subseteq> {0::int}" by (by100 blast)+
            have "0 \<in> H" using \<open>top1_is_group_on H _ 0 _\<close> unfolding top1_is_group_on_def by (by100 blast)
            thus "{0::int} \<subseteq> H" by (by100 blast)
          qed
          note h1 = \<open>{0::int} \<in> _\<close>
          note h2 = \<open>\<forall>H\<in>_. {0::int} \<subseteq> H\<close>
          let ?S = "{ H. {} \<subseteq> H \<and> H \<subseteq> {0::int} \<and> top1_is_group_on H (\<lambda>x y. 0) 0 id}"
          show ?thesis
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Inter>?S"
            thus "x \<in> {0::int}" using h1 by (by100 blast)
          next
            fix x assume "x \<in> {0::int}"
            thus "x \<in> \<Inter>?S" using h2 by (by100 blast)
          qed
        qed
        finally show ?thesis by (by100 simp)
      qed
      show "\<forall>ws::((nat \<times> bool) list).
          ws \<noteq> [] \<longrightarrow>
          top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>n::nat. 0::int) s, b)) ws) \<longrightarrow>
          (\<forall>i<length ws. fst (ws ! i) \<in> ({}::nat set)) \<longrightarrow>
          top1_group_word_product (\<lambda>x y. 0) 0 id (map (\<lambda>(s, b). ((\<lambda>n. 0::int) s, b)) ws) \<noteq> 0"
      proof (intro allI impI)
        fix ws :: "(nat \<times> bool) list"
        assume "ws \<noteq> []" and "\<forall>i<length ws. fst (ws ! i) \<in> ({}::nat set)"
        hence "length ws = 0" by (by100 auto)
        hence "ws = []" by (by100 simp)
        thus "top1_group_word_product (\<lambda>x y. 0) 0 id (map (\<lambda>(s, b). (0::int, b)) ws) \<noteq> 0"
          using \<open>ws \<noteq> []\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 2: \\<pi>\\_1(X, x0) is trivial (simply connected).\<close>
    \<comment> \<open>Step 3: iso {0} \\<pi>\\_1(X).\<close>
    have hiso: "top1_groups_isomorphic_on {0::int} (\<lambda>x y. 0)
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)"
    proof -
      let ?pi = "top1_fundamental_group_carrier X TX x0"
      let ?mul = "top1_fundamental_group_mul X TX x0"
      let ?eid = "top1_fundamental_group_id X TX x0"
      from simply_connected_trivial_carrier[OF \<open>top1_simply_connected_on X TX\<close> assms(3)]
      have hpi_sing: "?pi = {?eid}" .
      \<comment> \<open>Define f: {0} \\<rightarrow> \\<pi>\\_1(X) by f(0) = id.\<close>
      let ?f = "\<lambda>_::int. ?eid"
      have "top1_group_iso_on {0::int} (\<lambda>x y. 0) ?pi ?mul ?f"
        unfolding top1_group_iso_on_def
      proof (intro conjI)
        show "top1_group_hom_on {0::int} (\<lambda>x y. 0) ?pi ?mul ?f"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix a assume "a \<in> {0::int}" thus "?f a \<in> ?pi" using hpi_sing by (by100 blast)
        next
          fix a b assume "a \<in> {0::int}" "b \<in> {0::int}"
          have hpi_grp: "top1_is_group_on ?pi ?mul ?eid (top1_fundamental_group_invg X TX x0)"
            by (rule top1_fundamental_group_is_group[OF hTX_top assms(3)])
          have "?eid \<in> ?pi" using hpi_grp unfolding top1_is_group_on_def by (by100 blast)
          have "?mul ?eid ?eid = ?eid"
            using hpi_grp \<open>?eid \<in> ?pi\<close> unfolding top1_is_group_on_def by (by100 blast)
          thus "?f ((\<lambda>x y. 0::int) a b) = ?mul (?f a) (?f b)" by (by100 simp)
        qed
        show "bij_betw ?f {0::int} ?pi"
          unfolding bij_betw_def using hpi_sing by (by100 auto)
      qed
      thus ?thesis unfolding top1_groups_isomorphic_on_def by (by100 blast)
    qed
    show ?thesis using hfree hiso by (by100 blast)
  next
    case False
    \<comment> \<open>Non-tree arcs exist. Apply SvK induction (book Steps 1-3).\<close>
    \<comment> \<open>Munkres 84.7, Steps 1-3: SvK induction on number of non-tree arcs.
       Step 1 (induction step, n > 1): U = X - p2...pn, V = X - p1. SvK gives free product.
       Step 2 (base case, n = 1): direct SvK computation (\\<pi>\\_1 \\<cong> \\<Z>).
       Step 3 (infinite): any loop in finitely many arcs, reduce to finite.\\<close>
    \<comment> \<open>For each non-tree arc A, pick an interior point pA.\\<close>
    \<comment> \<open>Key: for any finite set S of non-tree arcs, T \\<union> (\\<Union>S) is a subgraph of X
       whose complement has X - \\<Union>{pA | A \\<in> ?NT - S} as deformation retract to T \\<union> (\\<Union>S).\\<close>
    \<comment> \<open>Munkres 84.7 SvK proof. Key helper: deformation retract.\\<close>
    have hdr_helper: "\<And>S ps. finite S \<Longrightarrow> S \<subseteq> ?NT \<Longrightarrow>
        (\<forall>A\<in>S. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)) \<Longrightarrow>
        top1_deformation_retract_of_on (X - ps ` S)
            (subspace_topology X TX (X - ps ` S))
            (T \<union> \<Union>(?NT - S))"
    proof -
      fix S ps
      assume hS_fin: "finite S" and hS_sub: "S \<subseteq> ?NT"
        and hps_loc: "\<forall>A\<in>S. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
      let ?Y = "X - ps ` S"
      let ?TY = "subspace_topology X TX ?Y"
      let ?target = "T \<union> \<Union>(?NT - S)"
      \<comment> \<open>The proof follows the same pattern as graph\\_remove\\_interior\\_points\\_sc.
         Define H\\_DR on Y \\<times> I: identity on target, slide half-arcs to T-endpoints.
         Continuity by pasting on closed pieces.\<close>
      have htarget_sub: "?target \<subseteq> ?Y"
      proof -
        have "T \<subseteq> ?Y"
        proof -
          have "\<forall>A\<in>S. ps A \<notin> T"
          proof (intro ballI)
            fix A assume "A \<in> S"
            hence "A \<in> ?NT" using hS_sub by (by100 blast)
            hence "A \<in> \<A>" "\<not> A \<subseteq> T" unfolding assms by (by100 blast)+
            from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
            have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using hps_loc \<open>A \<in> S\<close> by (by100 blast)
            thus "ps A \<notin> T"
              using \<open>A \<inter> T \<subseteq> _\<close> \<open>ps A \<notin> _\<close> hps_loc \<open>A \<in> S\<close> by (by100 blast)
          qed
          thus ?thesis using hT_sub by (by100 blast)
        qed
        moreover have "\<Union>(?NT - S) \<subseteq> ?Y"
        proof -
          have "\<forall>A\<in>?NT - S. A \<subseteq> ?Y"
          proof (intro ballI)
            fix A assume "A \<in> ?NT - S"
            have "A \<in> \<A>" using \<open>A \<in> ?NT - S\<close> by (by100 blast)
            have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            have "A \<inter> ps ` S = {}"
            proof (rule ccontr)
              assume "A \<inter> ps ` S \<noteq> {}"
              then obtain B where "B \<in> S" "ps B \<in> A" by (by100 blast)
              have "B \<in> \<A>" using hS_sub \<open>B \<in> S\<close> by (by100 blast)
              have "B \<noteq> A" using \<open>A \<in> ?NT - S\<close> \<open>B \<in> S\<close> by (by100 blast)
              have "ps B \<in> B" using hps_loc \<open>B \<in> S\<close> by (by100 blast)
              hence "ps B \<in> A \<inter> B" using \<open>ps B \<in> A\<close> by (by100 blast)
              hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
                using h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>B \<noteq> A\<close>[symmetric]]
                by (by100 blast)
              thus False using hps_loc \<open>B \<in> S\<close> by (by100 blast)
            qed
            thus "A \<subseteq> ?Y" using \<open>A \<subseteq> X\<close> by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      \<comment> \<open>Infrastructure: homeomorphisms for arcs in S.\<close>
      define hAc where "hAc \<equiv> \<lambda>A.
        SOME h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h"
      define tAc where "tAc \<equiv> \<lambda>A. inv_into top1_unit_interval (hAc A) (ps A)"
      have hhAc: "\<And>A. A \<in> S \<Longrightarrow> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) (hAc A)"
      proof -
        fix A assume "A \<in> S"
        hence "A \<in> ?NT" using hS_sub by (by100 blast)
        hence "A \<in> \<A>" by (by100 blast)
        hence "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> by (by100 blast)
        then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology X TX A) h" unfolding top1_is_arc_on_def by (by100 blast)
        thus "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology X TX A) (hAc A)"
          unfolding hAc_def
          by (rule someI[of "\<lambda>h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h"])
      qed
      \<comment> \<open>Define H\\_DR: for x \\<in> target: H(x,t) = x. For x in half-arc: slide.\<close>
      define H_DR where "H_DR \<equiv> \<lambda>(x, t::real).
        if x \<in> ?target then x
        else (let A = THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A) in
              let h = hAc A in
              let \<sigma> = inv_into top1_unit_interval h x in
              let ep = (if \<sigma> < tAc A then 0 else 1) in
              h (\<sigma> + t * (ep - \<sigma>)))"
      show "top1_deformation_retract_of_on ?Y ?TY ?target"
        unfolding top1_deformation_retract_of_on_def
      proof (intro conjI)
        show "?target \<subseteq> ?Y" using htarget_sub .
        show "\<exists>H. top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H
            \<and> (\<forall>x\<in>?Y. H (x, 0) = x) \<and> (\<forall>x\<in>?Y. H (x, 1) \<in> ?target)
            \<and> (\<forall>a\<in>?target. \<forall>t\<in>I_set. H (a, t) = a)"
        proof (rule exI[of _ H_DR])
          have "(\<forall>x\<in>?Y. H_DR (x, 0) = x)"
          proof (intro ballI)
            fix x assume "x \<in> ?Y"
            show "H_DR (x, 0) = x"
            proof (cases "x \<in> ?target")
              case True thus ?thesis unfolding H_DR_def by (by100 simp)
            next
              case False
              \<comment> \<open>x \\<notin> target. x is in some arc A \\<in> S. t=0 gives h(\\<sigma>) = x.\<close>
              have "x \<in> X" using \<open>x \<in> ?Y\<close> by (by100 blast)
              hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
              then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
              have "A \<in> S"
              proof (rule ccontr)
                assume "A \<notin> S"
                show False
                proof (cases "A \<subseteq> T")
                  case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
                next
                  case aFalse: False
                  hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
                  hence "A \<in> ?NT - S" using \<open>A \<notin> S\<close> by (by100 blast)
                  hence "x \<in> \<Union>(?NT - S)" using \<open>x \<in> A\<close> by (by100 blast)
                  hence "x \<in> ?target" by (by100 blast)
                  thus False using False by (by100 blast)
                qed
              qed
              have hbij_A: "bij_betw (hAc A) top1_unit_interval A"
                using hhAc[OF \<open>A \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
              have "x \<in> hAc A ` top1_unit_interval"
                using \<open>x \<in> A\<close> hbij_A unfolding bij_betw_def by (by100 blast)
              have "hAc A (inv_into top1_unit_interval (hAc A) x) = x"
                by (rule f_inv_into_f[OF \<open>x \<in> hAc A ` top1_unit_interval\<close>])
              \<comment> \<open>With t=0: \\<sigma> + 0*(ep - \\<sigma>) = \\<sigma>. hAc(\\<sigma>) = x.\<close>
              \<comment> \<open>x \\<notin> endpoints of A (endpoints \\<in> T \\<subseteq> target, but x \\<notin> target).\<close>
              have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
              have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] False by (by100 blast)
              hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A\<close> by (by100 blast)
              \<comment> \<open>THE uniqueness: A is the unique arc in S containing x as interior point.\<close>
              have hTHE: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
              proof (rule the_equality)
                show "A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                  using \<open>A \<in> S\<close> hx_int by (by100 blast)
              next
                fix A' assume h: "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
                show "A' = A"
                proof (rule ccontr)
                  assume "A' \<noteq> A"
                  from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
                  show False using \<open>x \<in> A\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                qed
              qed
              show ?thesis unfolding H_DR_def Let_def using False hTHE
                \<open>hAc A (inv_into top1_unit_interval (hAc A) x) = x\<close> by (by100 simp)
            qed
          qed
          moreover have "(\<forall>x\<in>?Y. H_DR (x, 1) \<in> ?target)"
          proof (intro ballI)
            fix x assume "x \<in> ?Y"
            show "H_DR (x, 1) \<in> ?target"
            proof (cases "x \<in> ?target")
              case True thus ?thesis unfolding H_DR_def by (by100 simp)
            next
              case False
              \<comment> \<open>x \\<notin> target. H\\_DR(x,1) = hAc A (ep) where ep=0 or 1.\<close>
              have "x \<in> X" using \<open>x \<in> ?Y\<close> by (by100 blast)
              hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
              then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
              have "A \<in> S"
              proof (rule ccontr)
                assume "A \<notin> S"
                show False
                proof (cases "A \<subseteq> T")
                  case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
                next
                  case aFalse: False
                  hence "A \<in> ?NT - S" using \<open>A \<in> \<A>\<close> \<open>A \<notin> S\<close> by (by100 blast)
                  thus False using \<open>x \<in> A\<close> False by (by100 blast)
                qed
              qed
              have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
              have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] False by (by100 blast)
              hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A\<close> by (by100 blast)
              have hTHE: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
              proof (rule the_equality)
                show "A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                  using \<open>A \<in> S\<close> hx_int by (by100 blast)
              next
                fix A' assume "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
                show "A' = A"
                proof (rule ccontr)
                  assume "A' \<noteq> A"
                  from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
                  show False using \<open>x \<in> A\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                qed
              qed
              \<comment> \<open>With t=1: \\<sigma> + 1*(ep-\\<sigma>) = ep. hAc A ep \\<in> T \\<subseteq> target.\<close>
              have "H_DR (x, 1) = hAc A (if inv_into top1_unit_interval (hAc A) x < tAc A then 0 else 1)"
                unfolding H_DR_def Let_def using False hTHE by (by100 simp)
              moreover have "hAc A 0 \<in> T" and "hAc A 1 \<in> T"
              proof -
                have hX_strict: "is_topology_on_strict X TX"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have hX_haus: "is_hausdorff_on X TX"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                have harc: "top1_is_arc_on A (subspace_topology X TX A)"
                  using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close> harc hhAc[OF \<open>A \<in> S\<close>]]
                have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hAc A 0, hAc A 1}" .
                show "hAc A 0 \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] hep by (by100 simp)
                show "hAc A 1 \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] hep by (by100 simp)
              qed
              ultimately show ?thesis by (by100 auto)
            qed
          qed
          moreover have "(\<forall>a\<in>?target. \<forall>t\<in>I_set. H_DR (a, t) = a)"
            unfolding H_DR_def by (by100 simp)
          moreover have "top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H_DR"
          proof -
            let ?YI = "?Y \<times> I_set"
            let ?YItop = "product_topology_on ?TY I_top"
            have hX_top: "is_topology_on X TX"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
            have hY_sub: "?Y \<subseteq> X" by (by100 blast)
            have hTY_top: "is_topology_on ?Y ?TY"
              by (rule subspace_topology_is_topology_on[OF hX_top hY_sub])
            have hYI_top: "is_topology_on ?YI ?YItop"
              by (rule product_topology_on_is_topology_on[OF hTY_top
                  top1_unit_interval_topology_is_topology_on])
            \<comment> \<open>Decompose Y\\<times>I into target\\<times>I and (Y\\\\target)\\<times>I.\<close>
            define D_T where "D_T = ?target \<times> I_set"
            define D_B where "D_B = (\<Union>A\<in>S. A \<inter> ?Y) \<times> I_set"
            \<comment> \<open>D\\_T \\<cup> D\\_B = Y\\<times>I (target \\<cup> \\<Union>{A\\<cap>Y | A \\<in> S} = Y).\<close>
            have hcover: "D_T \<union> D_B = ?YI"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> D_T \<union> D_B"
              thus "p \<in> ?YI" unfolding D_T_def D_B_def using htarget_sub by (by100 blast)
            next
              fix p assume "p \<in> ?YI"
              then obtain x t where hxt: "p = (x, t)" "x \<in> ?Y" "t \<in> I_set" by (by100 blast)
              show "p \<in> D_T \<union> D_B"
              proof (cases "x \<in> ?target")
                case True thus ?thesis unfolding D_T_def hxt(1) using hxt(3) by (by100 blast)
              next
                case False
                have "x \<in> X" using hxt(2) by (by100 blast)
                hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
                then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
                have "A \<in> S"
                proof (rule ccontr)
                  assume "A \<notin> S"
                  show False
                  proof (cases "A \<subseteq> T")
                    case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
                  next
                    case aFalse: False
                    hence "A \<in> ?NT - S" using \<open>A \<in> \<A>\<close> \<open>A \<notin> S\<close> by (by100 blast)
                    thus False using \<open>x \<in> A\<close> False by (by100 blast)
                  qed
                qed
                thus ?thesis unfolding D_B_def hxt(1) using \<open>x \<in> A\<close> hxt by (by100 blast)
              qed
            qed
            \<comment> \<open>target closed in Y (needs coherent topology — same as SC lemma T closed in Y).
               For now: sorry this standard fact.\<close>
            have htarget_closed: "closedin_on ?Y ?TY ?target"
            proof -
              \<comment> \<open>T closed in X (coherent topology + per-arc closedin).\<close>
              have hT_closed_X_dr: "closedin_on X TX T"
              proof -
                have "\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
                proof (intro ballI)
                  fix Ag assume "Ag \<in> \<A>"
                  have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                  show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
                  proof (cases "Ag \<subseteq> T")
                    case True
                    hence "Ag \<inter> T = Ag" by (by100 blast)
                    thus ?thesis using closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]]
                      by (by100 simp)
                  next
                    case False
                    from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] False
                    have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
                    have hX_haus: "is_hausdorff_on X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_strict: "is_topology_on_strict X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have harc: "top1_is_arc_on Ag (subspace_topology X TX Ag)"
                      using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                    then obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                        Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Ag \<subseteq> X\<close> harc hh]
                    have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
                    hence "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))" by (by100 simp)
                    from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close> this]
                    have "finite (Ag \<inter> T)" .
                    have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
                      using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus by (by100 blast)
                    show ?thesis
                      by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close>]) (by100 blast)
                  qed
                qed
                thus ?thesis using h\<A>_coh[rule_format, OF hT_sub] by (by100 blast)
              qed
              \<comment> \<open>T closed in Y.\<close>
              have hT_closed_Y_dr: "closedin_on ?Y ?TY T"
              proof -
                from Theorem_17_2[OF hX_top hY_sub, of T]
                show ?thesis using hT_closed_X_dr htarget_sub by (by100 blast)
              qed
              \<comment> \<open>\\<Union>(NT\\\\S) closed in Y: complement is Y \\<setminus> (T \\<union> \\<Union>(NT\\\\S)) = interiors of arcs in S.
                 This is a finite union of open sets (since S is finite). Hence complement open,
                 hence target closed.
                 Alternative: target closed in X (by coherent topology) then restrict to Y.\<close>
              \<comment> \<open>target closed in X: by coherent topology, target \\<cap> A closed in A for each arc.\<close>
              have htarget_closed_X: "closedin_on X TX ?target"
              proof -
                have "\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)"
                proof (intro ballI)
                  fix Ag assume "Ag \<in> \<A>"
                  have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                  show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)"
                  proof (cases "Ag \<in> S")
                    case True
                    \<comment> \<open>Ag \\<in> S: Ag \\<cap> target = Ag \\<cap> T (endpoints only, since Ag non-tree and not in NT\\\\S).\<close>
                    have "Ag \<in> ?NT" using hS_sub True by (by100 blast)
                    hence "\<not> Ag \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] this
                    have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
                    have "Ag \<inter> ?target = Ag \<inter> T"
                    proof -
                      have "Ag \<inter> \<Union>(?NT - S) \<subseteq> Ag \<inter> T"
                      proof (intro subsetI)
                        fix x assume "x \<in> Ag \<inter> \<Union>(?NT - S)"
                        then obtain B where "B \<in> ?NT - S" "x \<in> B" "x \<in> Ag" by (by100 blast)
                        have "B \<in> \<A>" using \<open>B \<in> ?NT - S\<close> by (by100 blast)
                        have "B \<noteq> Ag" using \<open>B \<in> ?NT - S\<close> True by (by100 blast)
                        hence "x \<in> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)"
                          using h\<A>_inter[rule_format, OF \<open>Ag \<in> \<A>\<close> \<open>B \<in> \<A>\<close>] \<open>x \<in> Ag\<close> \<open>x \<in> B\<close> \<open>B \<noteq> Ag\<close>
                          by (by100 blast)
                        thus "x \<in> Ag \<inter> T"
                          using hNT_endpoints[rule_format, OF \<open>Ag \<in> ?NT\<close>] \<open>x \<in> Ag\<close> by (by100 blast)
                      qed
                      thus ?thesis by (by100 blast)
                    qed
                    \<comment> \<open>Ag \\<cap> T is finite (endpoints) hence closed in Hausdorff Ag.\<close>
                    have hX_haus: "is_hausdorff_on X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_strict: "is_topology_on_strict X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have harc: "top1_is_arc_on Ag (subspace_topology X TX Ag)"
                      using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                    then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                        Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Ag \<subseteq> X\<close> harc this]
                    have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
                    hence "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))" by (by100 simp)
                    from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close> this]
                    have "finite (Ag \<inter> T)" .
                    have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
                      using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus by (by100 blast)
                    have "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
                      by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close>]) (by100 blast)
                    thus ?thesis using \<open>Ag \<inter> ?target = Ag \<inter> T\<close> by (by100 simp)
                  next
                    case False
                    \<comment> \<open>Ag \\<notin> S: either Ag \\<subseteq> T or Ag \\<in> NT\\\\S. In both cases Ag \\<subseteq> target.\<close>
                    have "Ag \<subseteq> ?target"
                    proof (cases "Ag \<subseteq> T")
                      case True thus ?thesis by (by100 blast)
                    next
                      case aFalse: False
                      hence "Ag \<in> ?NT" using \<open>Ag \<in> \<A>\<close> by (by100 blast)
                      hence "Ag \<in> ?NT - S" using False by (by100 blast)
                      thus ?thesis by (by100 blast)
                    qed
                    hence "Ag \<inter> ?target = Ag" by (by100 blast)
                    thus ?thesis
                      using closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]]
                      by (by100 simp)
                  qed
                qed
                have "?target \<subseteq> X" using hT_sub h\<A> by (by100 blast)
                note hper_arc = \<open>\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)\<close>
                thus ?thesis using h\<A>_coh[rule_format, OF \<open>?target \<subseteq> X\<close>] hper_arc by (by100 blast)
              qed
              \<comment> \<open>target closed in Y (from target closed in X + Theorem\\_17\\_2).\<close>
              from Theorem_17_2[OF hX_top hY_sub, of ?target]
              show ?thesis using htarget_closed_X htarget_sub by (by100 blast)
            qed
            \<comment> \<open>Each A\\<cap>Y closed in Y for A \\<in> S.\<close>
            have hS_AY_closed: "\<forall>A\<in>S. closedin_on ?Y ?TY (A \<inter> ?Y)"
            proof (intro ballI)
              fix A assume "A \<in> S"
              have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
              hence "A \<in> \<A>" by (by100 blast)
              hence "A \<subseteq> X" using h\<A> by (by100 blast)
              have harc_A: "top1_is_arc_on A (subspace_topology X TX A)"
                using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
              then obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  A (subspace_topology X TX A) h0" unfolding top1_is_arc_on_def by (by100 blast)
              have hI_cpt: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
              proof -
                have hCI: "top1_compact_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
                  by (rule top1_closed_interval_compact) (by100 linarith)
                have hCI_eq: "top1_closed_interval 0 1 = top1_unit_interval"
                  unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
                show ?thesis unfolding top1_compact_on_def
                proof (intro conjI allI impI)
                  show "is_topology_on top1_unit_interval top1_unit_interval_topology"
                    by (rule top1_unit_interval_topology_is_topology_on)
                next
                  fix Uc assume hUc: "Uc \<subseteq> top1_unit_interval_topology \<and> top1_unit_interval \<subseteq> \<Union>Uc"
                  have "Uc \<subseteq> top1_closed_interval_topology 0 1"
                    using hUc I_top_sub_closed_interval_top by (by100 blast)
                  moreover have "top1_closed_interval 0 1 \<subseteq> \<Union>Uc" using hUc hCI_eq by (by100 simp)
                  ultimately have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_closed_interval 0 1 \<subseteq> \<Union>F"
                    using hCI unfolding top1_compact_on_def by (by100 blast)
                  thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F" using hCI_eq by (by100 simp)
                qed
              qed
              have hh0c: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  A (subspace_topology X TX A) h0"
                using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
              have hTA: "is_topology_on A (subspace_topology X TX A)"
                by (rule subspace_topology_is_topology_on[OF hX_top \<open>A \<subseteq> X\<close>])
              from top1_compact_on_continuous_image[OF hI_cpt hTA hh0c]
              have "top1_compact_on (h0 ` top1_unit_interval)
                  (subspace_topology A (subspace_topology X TX A) (h0 ` top1_unit_interval))" .
              have "h0 ` top1_unit_interval = A"
                using hh0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              have "subspace_topology A (subspace_topology X TX A) A = subspace_topology X TX A"
              proof (rule subspace_topology_self)
                show "\<forall>U\<in>subspace_topology X TX A. U \<subseteq> A"
                  unfolding subspace_topology_def by (by100 blast)
              qed
              hence "top1_compact_on A (subspace_topology X TX A)"
                using \<open>top1_compact_on (h0 ` top1_unit_interval) _\<close> \<open>h0 ` top1_unit_interval = A\<close>
                by (by100 simp)
              have hX_haus: "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hX_strict: "is_topology_on_strict X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "closedin_on X TX A"
                by (rule compact_in_strict_hausdorff_closedin_on[OF hX_haus hX_strict \<open>A \<subseteq> X\<close>
                    \<open>top1_compact_on A (subspace_topology X TX A)\<close>])
              from Theorem_17_2[OF hX_top hY_sub, of "A \<inter> ?Y"]
              show "closedin_on ?Y ?TY (A \<inter> ?Y)" using \<open>closedin_on X TX A\<close> by (by100 blast)
            qed
            have hB_closed: "closedin_on ?Y ?TY (\<Union>A\<in>S. A \<inter> ?Y)"
              by (rule closedin_on_finite_indexed_Union[OF hTY_top hS_fin])
                 (use hS_AY_closed in \<open>by100 blast\<close>)
            \<comment> \<open>D\\_T, D\\_B closed in Y\\<times>I.\<close>
            have hfst_cont: "top1_continuous_map_on ?YI ?YItop ?Y ?TY fst"
            proof -
              from top1_continuous_pi1[OF hTY_top top1_unit_interval_topology_is_topology_on]
              show ?thesis unfolding pi1_def by (by100 simp)
            qed
            have hDT_closed: "closedin_on ?YI ?YItop D_T"
            proof -
              have "{p \<in> ?YI. fst p \<in> ?target} = D_T"
              proof (rule set_eqI, rule iffI)
                fix p assume "p \<in> {p \<in> ?YI. fst p \<in> ?target}"
                thus "p \<in> D_T" unfolding D_T_def by (by100 auto)
              next
                fix p assume "p \<in> D_T"
                thus "p \<in> {p \<in> ?YI. fst p \<in> ?target}"
                  unfolding D_T_def using htarget_sub by (by100 auto)
              qed
              moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> ?target}"
                by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont htarget_closed])
              ultimately show ?thesis by (by100 simp)
            qed
            have hDB_closed: "closedin_on ?YI ?YItop D_B"
            proof -
              have "{p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)} = D_B"
              proof (rule set_eqI, rule iffI)
                fix p assume "p \<in> {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
                thus "p \<in> D_B" unfolding D_B_def by (by100 auto)
              next
                fix p assume "p \<in> D_B"
                thus "p \<in> {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
                  unfolding D_B_def by (by100 auto)
              qed
              moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
                by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont hB_closed])
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>H on D\\_T = \\<pi>\\_1 (projection, continuous).\<close>
            have hH_img: "\<forall>p\<in>?YI. H_DR p \<in> ?Y"
            proof (intro ballI)
              fix p assume "p \<in> ?YI"
              then obtain x t where hxt: "p = (x, t)" "x \<in> ?Y" "t \<in> I_set" by (by100 blast)
              show "H_DR p \<in> ?Y"
              proof (cases "x \<in> ?target")
                case True
                have "H_DR p = x" unfolding H_DR_def hxt(1) using True by (by100 simp)
                moreover have "x \<in> ?Y" using True htarget_sub by (by100 blast)
                ultimately show ?thesis by (by100 simp)
              next
                case False
                \<comment> \<open>H\\_DR(x,t) on half-arc. Image in Y from same argument as SC lemma.\<close>
                \<comment> \<open>x \\<notin> target. Find arc A \\<in> S containing x.\<close>
                have "x \<in> X" using hxt(2) by (by100 blast)
                hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
                then obtain Ax where "Ax \<in> \<A>" "x \<in> Ax" by (by100 blast)
                have "Ax \<in> S"
                proof (rule ccontr)
                  assume "Ax \<notin> S"
                  show False
                  proof (cases "Ax \<subseteq> T")
                    case True thus False using \<open>x \<in> Ax\<close> False by (by100 blast)
                  next
                    case aF: False
                    hence "Ax \<in> ?NT - S" using \<open>Ax \<in> \<A>\<close> \<open>Ax \<notin> S\<close> by (by100 blast)
                    thus False using \<open>x \<in> Ax\<close> False by (by100 blast)
                  qed
                qed
                \<comment> \<open>H\\_DR(x,t) = hAc Ax (param). param \\<in> [0,1], param \\<noteq> tAc Ax.
                   Hence hAc(param) \\<in> Ax, hAc(param) \\<noteq> ps(Ax).
                   And hAc(param) \\<notin> ps(A') for A'\\<noteq>Ax (graph intersection + endpoints \\<in> T).\<close>
                \<comment> \<open>THE uniqueness: Ax is the unique arc in S containing x.\<close>
                have "Ax \<in> ?NT" using hS_sub \<open>Ax \<in> S\<close> by (by100 blast)
                have "x \<notin> top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                  using hNT_endpoints[rule_format, OF \<open>Ax \<in> ?NT\<close>] False by (by100 blast)
                hence hx_int: "x \<in> Ax - top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                  using \<open>x \<in> Ax\<close> by (by100 blast)
                have hTHE_Ax: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Ax"
                proof (rule the_equality)
                  show "Ax \<in> S \<and> x \<in> Ax - top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                    using \<open>Ax \<in> S\<close> hx_int by (by100 blast)
                next
                  fix A' assume "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                  hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
                  show "A' = Ax"
                  proof (rule ccontr)
                    assume "A' \<noteq> Ax"
                    from h\<A>_inter[rule_format, OF \<open>Ax \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Ax\<close>[symmetric]]
                    show False using \<open>x \<in> Ax\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on Ax _\<close> by (by100 blast)
                  qed
                qed
                \<comment> \<open>H\\_DR(x,t) = hAc Ax (param). Show param \\<in> [0,1] and hAc(param) \\<in> Y.\<close>
                have hbij_Ax: "bij_betw (hAc Ax) top1_unit_interval Ax"
                  using hhAc[OF \<open>Ax \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                have hinj_Ax: "inj_on (hAc Ax) top1_unit_interval"
                  using hbij_Ax unfolding bij_betw_def by (by100 blast)
                have himg_Ax: "hAc Ax ` top1_unit_interval = Ax"
                  using hbij_Ax unfolding bij_betw_def by (by100 blast)
                have "x \<in> hAc Ax ` top1_unit_interval" using \<open>x \<in> Ax\<close> himg_Ax by (by100 simp)
                define \<sigma>x where "\<sigma>x = inv_into top1_unit_interval (hAc Ax) x"
                define epx where "epx = (if \<sigma>x < tAc Ax then (0::real) else 1)"
                define param where "param = \<sigma>x + t * (epx - \<sigma>x)"
                have hH_eq: "H_DR (x, t) = hAc Ax param"
                  unfolding H_DR_def Let_def param_def epx_def \<sigma>x_def using False hTHE_Ax by (by100 simp)
                \<comment> \<open>param \\<in> [0,1].\<close>
                have h\<sigma>x_I: "\<sigma>x \<in> top1_unit_interval"
                  unfolding \<sigma>x_def by (rule inv_into_into[OF \<open>x \<in> hAc Ax ` top1_unit_interval\<close>])
                have h\<sigma>x_01: "0 \<le> \<sigma>x \<and> \<sigma>x \<le> 1" using h\<sigma>x_I unfolding top1_unit_interval_def by (by100 auto)
                have ht_01: "0 \<le> t \<and> t \<le> 1" using hxt(3) unfolding top1_unit_interval_def by (by100 auto)
                have hparam_I: "param \<in> top1_unit_interval"
                proof (cases "\<sigma>x < tAc Ax")
                  case True
                  hence "epx = 0" unfolding epx_def by (by100 simp)
                  hence "param = \<sigma>x + t * (0 - \<sigma>x)" unfolding param_def by (by100 simp)
                  have "t * \<sigma>x \<le> 1 * \<sigma>x"
                    by (rule mult_right_mono) (use ht_01 h\<sigma>x_01 in linarith)+
                  have "t * \<sigma>x \<ge> 0"
                    by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
                  have "param = \<sigma>x - t * \<sigma>x" using \<open>param = \<sigma>x + t * (0 - \<sigma>x)\<close> by (by100 simp)
                  thus ?thesis unfolding top1_unit_interval_def
                    using h\<sigma>x_01 \<open>t * \<sigma>x \<le> _\<close> \<open>t * \<sigma>x \<ge> 0\<close> by (by100 auto)
                next
                  case False
                  hence "epx = 1" unfolding epx_def by (by100 simp)
                  hence "param = \<sigma>x + t * (1 - \<sigma>x)" unfolding param_def by (by100 simp)
                  have "t * (1 - \<sigma>x) \<ge> 0"
                    by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
                  have "t * (1 - \<sigma>x) \<le> 1 * (1 - \<sigma>x)"
                    by (rule mult_right_mono) (use ht_01 h\<sigma>x_01 in linarith)+
                  hence "t * (1 - \<sigma>x) \<le> 1 - \<sigma>x" by (by100 simp)
                  hence "\<sigma>x + t * (1 - \<sigma>x) \<le> 1" by (by100 linarith)
                  thus ?thesis unfolding top1_unit_interval_def
                    using h\<sigma>x_01 \<open>t * (1 - \<sigma>x) \<ge> 0\<close> \<open>param = \<sigma>x + t * (1 - \<sigma>x)\<close> by (by100 auto)
                qed
                \<comment> \<open>param \\<noteq> tAc (since \\<sigma>x \\<noteq> tAc and param stays on same side).\<close>
                have h\<sigma>x_ne: "\<sigma>x \<noteq> tAc Ax"
                proof
                  assume "\<sigma>x = tAc Ax"
                  have "hAc Ax \<sigma>x = x"
                    unfolding \<sigma>x_def by (rule f_inv_into_f[OF \<open>x \<in> hAc Ax ` top1_unit_interval\<close>])
                  have "ps Ax \<in> hAc Ax ` top1_unit_interval"
                    using hps_loc \<open>Ax \<in> S\<close> himg_Ax by (by100 blast)
                  have "hAc Ax (tAc Ax) = ps Ax"
                    unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
                  hence "x = ps Ax" using \<open>hAc Ax \<sigma>x = x\<close> \<open>\<sigma>x = tAc Ax\<close> by (by100 simp)
                  hence "x \<in> ps ` S" using \<open>Ax \<in> S\<close> by (by100 blast)
                  thus False using hxt(2) by (by100 blast)
                qed
                have hparam_ne: "param \<noteq> tAc Ax"
                proof (cases "\<sigma>x < tAc Ax")
                  case True
                  hence "epx = 0" unfolding epx_def by (by100 simp)
                  hence "param = \<sigma>x + t * (0 - \<sigma>x)" unfolding param_def by (by100 simp)
                  have "param = \<sigma>x - t * \<sigma>x" using \<open>param = \<sigma>x + t * (0 - \<sigma>x)\<close> by (by100 simp)
                  have "t * \<sigma>x \<ge> 0"
                    by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
                  hence "param \<le> \<sigma>x" using \<open>param = \<sigma>x - t * \<sigma>x\<close> by (by100 linarith)
                  hence "param < tAc Ax" using True by (by100 linarith)
                  thus ?thesis by (by100 linarith)
                next
                  case False
                  hence "\<sigma>x > tAc Ax" using h\<sigma>x_ne by (by100 linarith)
                  hence "epx = 1" unfolding epx_def by (by100 simp)
                  hence "param = \<sigma>x + t * (1 - \<sigma>x)" unfolding param_def by (by100 simp)
                  have "t * (1 - \<sigma>x) \<ge> 0"
                    by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
                  hence "param \<ge> \<sigma>x" using \<open>param = \<sigma>x + t * (1 - \<sigma>x)\<close> by (by100 linarith)
                  hence "param > tAc Ax" using \<open>\<sigma>x > tAc Ax\<close> by (by100 linarith)
                  thus ?thesis by (by100 linarith)
                qed
                \<comment> \<open>hAc(param) \\<in> Ax.\<close>
                have "hAc Ax param \<in> Ax" using hparam_I himg_Ax by (by100 blast)
                hence "hAc Ax param \<in> X" using h\<A> \<open>Ax \<in> \<A>\<close> by (by100 blast)
                \<comment> \<open>hAc(param) \\<notin> ps ` S.\<close>
                have "hAc Ax param \<notin> ps ` S"
                proof
                  assume "hAc Ax param \<in> ps ` S"
                  then obtain A' where "A' \<in> S" "hAc Ax param = ps A'" by (by100 blast)
                  show False
                  proof (cases "A' = Ax")
                    case True
                    hence "hAc Ax param = ps Ax" using \<open>hAc Ax param = ps A'\<close> by (by100 simp)
                    have "ps Ax \<in> hAc Ax ` top1_unit_interval"
                      using hps_loc \<open>Ax \<in> S\<close> himg_Ax by (by100 blast)
                    have htAc_I: "tAc Ax \<in> top1_unit_interval"
                      unfolding tAc_def by (rule inv_into_into[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
                    have "hAc Ax (tAc Ax) = ps Ax"
                      unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
                    from inj_onD[OF hinj_Ax _ hparam_I htAc_I]
                    have "param = tAc Ax" using \<open>hAc Ax param = ps Ax\<close> \<open>hAc Ax (tAc Ax) = ps Ax\<close>
                      by (by100 simp)
                    thus False using hparam_ne by (by100 blast)
                  next
                    case hA'_ne: False
                    have "A' \<in> \<A>" using hS_sub \<open>A' \<in> S\<close> by (by100 blast)
                    have "ps A' \<in> A'" using hps_loc \<open>A' \<in> S\<close> by (by100 blast)
                    hence "hAc Ax param \<in> A'" using \<open>hAc Ax param = ps A'\<close> by (by100 simp)
                    have "hAc Ax param \<in> Ax \<inter> A'"
                      using \<open>hAc Ax param \<in> Ax\<close> \<open>hAc Ax param \<in> A'\<close> by (by100 blast)
                    hence "hAc Ax param \<in> top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                      using h\<A>_inter[rule_format, OF \<open>Ax \<in> \<A>\<close> \<open>A' \<in> \<A>\<close>] hA'_ne by (by100 blast)
                    hence "hAc Ax param \<in> T"
                      using hNT_endpoints[rule_format, OF \<open>Ax \<in> ?NT\<close>] by (by100 blast)
                    have "ps A' \<notin> T"
                    proof -
                      have "A' \<in> ?NT" using hS_sub \<open>A' \<in> S\<close> by (by100 blast)
                      from hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>]
                      have "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                        using \<open>A' \<in> ?NT\<close> by (by100 blast)
                      have "ps A' \<notin> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                        using hps_loc \<open>A' \<in> S\<close> by (by100 blast)
                      thus ?thesis using \<open>A' \<inter> T \<subseteq> _\<close> hps_loc \<open>A' \<in> S\<close> by (by100 blast)
                    qed
                    thus False using \<open>hAc Ax param \<in> T\<close> \<open>hAc Ax param = ps A'\<close> by (by100 simp)
                  qed
                qed
                have "hAc Ax param \<in> ?Y" using \<open>hAc Ax param \<in> X\<close> \<open>hAc Ax param \<notin> ps ` S\<close> by (by100 blast)
                show ?thesis using hH_eq \<open>hAc Ax param \<in> ?Y\<close> hxt(1) by (by100 simp)
              qed
            qed
            have hH_DT: "top1_continuous_map_on D_T (subspace_topology ?YI ?YItop D_T) ?Y ?TY H_DR"
            proof -
              have hfst_DT: "top1_continuous_map_on D_T (subspace_topology ?YI ?YItop D_T) ?Y ?TY fst"
              proof -
                have "D_T \<subseteq> ?YI" unfolding D_T_def using htarget_sub by (by100 blast)
                from top1_continuous_map_on_restrict_domain_simple[OF hfst_cont this]
                show ?thesis .
              qed
              have heq: "\<forall>p\<in>D_T. H_DR p = fst p" unfolding D_T_def H_DR_def by (by100 simp)
              have hDT_sub: "D_T \<subseteq> ?YI" unfolding D_T_def using htarget_sub by (by100 blast)
              have hDT_top: "is_topology_on D_T (subspace_topology ?YI ?YItop D_T)"
                by (rule subspace_topology_is_topology_on[OF hYI_top hDT_sub])
              have "\<forall>p\<in>D_T. H_DR p \<in> ?Y" using heq hfst_DT
                unfolding top1_continuous_map_on_def by (by100 auto)
              have "\<forall>V\<in>?TY. {p \<in> D_T. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_T"
              proof (intro ballI)
                fix V assume "V \<in> ?TY"
                have "{p \<in> D_T. H_DR p \<in> V} = {p \<in> D_T. fst p \<in> V}" using heq by (by100 auto)
                also have "... \<in> subspace_topology ?YI ?YItop D_T"
                  using hfst_DT \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                finally show "{p \<in> D_T. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_T" .
              qed
              thus ?thesis unfolding top1_continuous_map_on_def
                using hDT_top hTY_top \<open>\<forall>p\<in>D_T. H_DR p \<in> ?Y\<close> by (by100 blast)
            qed
            \<comment> \<open>H on D\\_B: composition chain per arc, same as SC lemma.\<close>
            \<comment> \<open>H|D\\_B continuous: per-arc pasting. D\\_B = \\<Union>{(A\\<cap>Y)\\<times>I | A \\<in> S}.
               On each (A\\<cap>Y)\\<times>I: H\\_DR = hAc \\<circ> (arith of inv\\_into\\<circ>\\<pi>\\_1 and \\<pi>\\_2).
               This is the SAME proof as the SC lemma's H|S\\_B (bck1384-bck1420)
               but with \\<pi>\\_1: Y\\<times>I \\<rightarrow> Y replacing f\\<circ>fst: I\\<times>I \\<rightarrow> Y.
               The proof is ~400 lines following the established pattern.\<close>
            have hH_DB: "top1_continuous_map_on D_B (subspace_topology ?YI ?YItop D_B) ?Y ?TY H_DR"
            proof -
              have hDB_sub: "D_B \<subseteq> ?YI" unfolding D_B_def by (by100 blast)
              have hDB_top: "is_topology_on D_B (subspace_topology ?YI ?YItop D_B)"
                by (rule subspace_topology_is_topology_on[OF hYI_top hDB_sub])
              have hH_img_DB: "\<forall>p\<in>D_B. H_DR p \<in> ?Y" using hH_img hDB_sub by (by100 blast)
              \<comment> \<open>Strategy: show preimage of every open V is open in D\\_B.
                 Complement of preimage = \\<Union>{(A\\<cap>Y)\\<times>I \\<cap> complement | A \\<in> S}.
                 Each (A\\<cap>Y)\\<times>I \\<cap> complement is closed in D\\_B (from per-arc continuity).
                 Finite union of closed = closed. Hence preimage is open.\<close>
              \<comment> \<open>Per-arc pieces.\<close>
              define QA where "QA \<equiv> \<lambda>A. (A \<inter> ?Y) \<times> I_set"
              have hQA_closed: "\<forall>A\<in>S. closedin_on ?YI ?YItop (QA A)"
              proof (intro ballI)
                fix A assume "A \<in> S"
                have "{p \<in> ?YI. fst p \<in> A \<inter> ?Y} = QA A"
                  unfolding QA_def by (by100 auto)
                moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> A \<inter> ?Y}"
                  by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont])
                     (use hS_AY_closed \<open>A \<in> S\<close> in \<open>by100 blast\<close>)
                ultimately show "closedin_on ?YI ?YItop (QA A)" by (by100 simp)
              qed
              have hDB_eq: "D_B = (\<Union>A\<in>S. QA A)" unfolding D_B_def QA_def by (by100 blast)
              \<comment> \<open>Per-arc continuity: H\\_DR continuous on each QA A.\<close>
              have hH_QA: "\<forall>A\<in>S. top1_continuous_map_on (QA A) (subspace_topology ?YI ?YItop (QA A)) ?Y ?TY H_DR"
              proof (intro ballI)
                fix Aq assume "Aq \<in> S"
                have hAq_sub: "Aq \<subseteq> X" using h\<A> hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                have hQA_sub: "QA Aq \<subseteq> ?YI" using hQA_closed \<open>Aq \<in> S\<close>
                  unfolding closedin_on_def by (by100 blast)
                \<comment> \<open>On QA Aq: H\\_DR equals hAc Aq \\<circ> g where g(x,t) = inv(hAc,x)+t*(ep-inv(hAc,x)).
                   When x \\<in> target: H\\_DR = x (identity). When x \\<notin> target: the formula.
                   Both branches produce values in Y. Both are continuous.\<close>
                \<comment> \<open>Show H\\_DR agrees with a continuous function on QA Aq.
                   The continuous function: hAc Aq \\<circ> arith \\<circ> (inv\\_into\\<circ>\\<pi>\\_1, \\<pi>\\_2).
                   But for x \\<in> target: H\\_DR = x while the formula gives hAc(\\<sigma>+t*(ep-\\<sigma>)).
                   At target points (endpoints): \\<sigma> = 0 or 1, so the formula also gives x. Good.\<close>
                show "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) ?Y ?TY H_DR"
                proof -
                  have hQA_top: "is_topology_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))"
                    by (rule subspace_topology_is_topology_on[OF hYI_top hQA_sub])
                  \<comment> \<open>Step 1: \\<pi>\\_1 restricted + codomain to Aq\\<cap>Y.\<close>
                  have hfst_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) ?Y ?TY fst"
                    by (rule top1_continuous_map_on_restrict_domain_simple[OF hfst_cont hQA_sub])
                  have hfst_img: "\<forall>p\<in>QA Aq. fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
                  have hAqY_sub: "Aq \<inter> ?Y \<subseteq> ?Y" by (by100 blast)
                  have hfst_AqY: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      (Aq \<inter> ?Y) (subspace_topology ?Y ?TY (Aq \<inter> ?Y)) fst"
                    by (rule continuous_map_restrict_codomain[OF hfst_QA hfst_img hAqY_sub])
                  \<comment> \<open>Step 2: inv\\_into continuous on Aq\\<cap>Y (topology matching).\<close>
                  have hinv_cont: "top1_continuous_map_on Aq (subspace_topology X TX Aq)
                      top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hAc Aq))"
                    using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hAq_sub_Aq: "Aq \<inter> ?Y \<subseteq> Aq" by (by100 blast)
                  have "subspace_topology ?Y ?TY (Aq \<inter> ?Y) = subspace_topology Aq (subspace_topology X TX Aq) (Aq \<inter> ?Y)"
                  proof -
                    have "subspace_topology ?Y ?TY (Aq \<inter> ?Y) = subspace_topology X TX (Aq \<inter> ?Y)"
                      by (rule subspace_topology_trans[OF hAqY_sub])
                    also have "... = subspace_topology Aq (subspace_topology X TX Aq) (Aq \<inter> ?Y)"
                      by (rule subspace_topology_trans[OF hAq_sub_Aq, symmetric])
                    finally show ?thesis .
                  qed
                  hence hinv_AqY: "top1_continuous_map_on (Aq \<inter> ?Y) (subspace_topology ?Y ?TY (Aq \<inter> ?Y))
                      top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hAc Aq))"
                    using top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hAq_sub_Aq] by (by100 simp)
                  \<comment> \<open>Step 3: compose inv\\_into \\<circ> fst.\<close>
                  from top1_continuous_map_on_comp[OF hfst_AqY hinv_AqY]
                  have hinv_fst: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      top1_unit_interval top1_unit_interval_topology
                      (\<lambda>p. inv_into top1_unit_interval (hAc Aq) (fst p))"
                    unfolding top1_continuous_map_on_def comp_def by (by100 auto)
                  \<comment> \<open>Step 4: \\<pi>\\_2 restricted.\<close>
                  have hsnd_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      top1_unit_interval top1_unit_interval_topology snd"
                  proof -
                    from top1_continuous_pi2[OF hTY_top top1_unit_interval_topology_is_topology_on]
                    have "top1_continuous_map_on ?YI ?YItop top1_unit_interval top1_unit_interval_topology snd"
                      unfolding pi2_def by (by100 simp)
                    from top1_continuous_map_on_restrict_domain_simple[OF this hQA_sub] show ?thesis .
                  qed
                  \<comment> \<open>Step 5: pair (inv\\<circ>fst, snd) \\<rightarrow> I\\<times>I.\<close>
                  have "\<And>p. pi1 ((\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)) p) =
                      inv_into top1_unit_interval (hAc Aq) (fst p)"
                    unfolding pi1_def by (by100 simp)
                  hence hc1: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      top1_unit_interval top1_unit_interval_topology
                      (pi1 \<circ> (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                    using hinv_fst unfolding top1_continuous_map_on_def comp_def pi1_def by (by100 auto)
                  have "\<And>p. pi2 ((\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)) p) = snd p"
                    unfolding pi2_def by (by100 simp)
                  hence hc2: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      top1_unit_interval top1_unit_interval_topology
                      (pi2 \<circ> (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                    using hsnd_QA unfolding top1_continuous_map_on_def comp_def pi2_def by (by100 auto)
                  let ?IItop = "product_topology_on top1_unit_interval_topology top1_unit_interval_topology"
                  from Theorem_18_4[OF hQA_top top1_unit_interval_topology_is_topology_on
                      top1_unit_interval_topology_is_topology_on,
                      of "\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)"]
                  have hpair_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                      (top1_unit_interval \<times> top1_unit_interval) ?IItop
                      (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                    using hc1 hc2 by (by100 blast)
                  \<comment> \<open>Step 6-8: arith + hAc + compose. Same as SC lemma.\<close>
                  \<comment> \<open>Need two arithmetic maps (for e\\_param=0 and e\\_param=1) and pasting.\<close>
                  \<comment> \<open>For now: sorry the final composition + H\\_DR=formula.\<close>
                  \<comment> \<open>Arithmetic: both halves (ep=0 and ep=1) continuous I\\<times>I \\<rightarrow> I.\<close>
                  have harith0: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
                      ?IItop top1_unit_interval top1_unit_interval_topology
                      (\<lambda>p. fst p + snd p * (0 - fst p))"
                  proof -
                    have "continuous_on (I_set \<times> I_set) (\<lambda>p :: real \<times> real. fst p - snd p * fst p)"
                      by (intro continuous_intros)
                    have "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p - snd p * fst p \<in> I_set"
                    proof -
                      fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                      then obtain a b where hp: "p = (a,b)" "a \<in> I_set" "b \<in> I_set" by (by100 blast)
                      have ha: "0 \<le> a" "a \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                      have hb: "0 \<le> b" "b \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                      have "b * a \<le> 1 * a" by (rule mult_right_mono) (use hb ha in linarith)+
                      have "b * a \<ge> 0" by (rule mult_nonneg_nonneg) (use hb ha in linarith)+
                      show "fst p - snd p * fst p \<in> I_set" unfolding hp(1) top1_unit_interval_def
                        using ha \<open>b * a \<le> _\<close> \<open>b * a \<ge> 0\<close> by (by100 auto)
                    qed
                    from top1_continuous_map_on_II_to_I[OF this \<open>continuous_on _ _\<close>, unfolded II_topology_def]
                    have "top1_continuous_map_on (I_set \<times> I_set) ?IItop I_set I_top
                        (\<lambda>p. fst p - snd p * fst p)" .
                    moreover have "\<And>p :: real \<times> real. fst p + snd p * (0 - fst p) = fst p - snd p * fst p"
                      by (by100 simp)
                    hence "\<And>p :: real \<times> real. {q \<in> I_set \<times> I_set. fst q + snd q * (0 - fst q) \<in> V}
                        = {q \<in> I_set \<times> I_set. fst q - snd q * fst q \<in> V}" for V by (by100 auto)
                    ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                  qed
                  have harith1: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
                      ?IItop top1_unit_interval top1_unit_interval_topology
                      (\<lambda>p. fst p + snd p * (1 - fst p))"
                  proof -
                    have "continuous_on (I_set \<times> I_set) (\<lambda>p :: real \<times> real. fst p + snd p * (1 - fst p))"
                      by (intro continuous_intros)
                    have "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p + snd p * (1 - fst p) \<in> I_set"
                    proof -
                      fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                      then obtain a b where hp: "p = (a,b)" "a \<in> I_set" "b \<in> I_set" by (by100 blast)
                      have ha: "0 \<le> a" "a \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                      have hb: "0 \<le> b" "b \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                      have "b * (1 - a) \<ge> 0" by (rule mult_nonneg_nonneg) (use hb ha in linarith)+
                      have "b * (1 - a) \<le> 1 * (1 - a)" by (rule mult_right_mono) (use hb ha in linarith)+
                      hence "b * (1 - a) \<le> 1 - a" by (by100 simp)
                      hence "a + b * (1 - a) \<le> 1" by (by100 linarith)
                      show "fst p + snd p * (1 - fst p) \<in> I_set" unfolding hp(1) top1_unit_interval_def
                        using ha \<open>b * (1 - a) \<ge> 0\<close> \<open>a + b * (1 - a) \<le> 1\<close> by (by100 auto)
                    qed
                    from top1_continuous_map_on_II_to_I[OF this \<open>continuous_on _ _\<close>, unfolded II_topology_def]
                    show ?thesis .
                  qed
                  \<comment> \<open>hAc continuous I \\<rightarrow> X.\<close>
                  have hhAc_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (hAc Aq)"
                  proof -
                    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                        Aq (subspace_topology X TX Aq) (hAc Aq)"
                      using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                    from top1_continuous_map_on_codomain_enlarge[OF this hAq_sub subset_refl]
                    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                        X (subspace_topology X TX X) (hAc Aq)" .
                    moreover have "subspace_topology X TX X = TX"
                    proof (rule subspace_topology_self)
                      have "is_topology_on_strict X TX"
                        using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                      thus "\<forall>U\<in>TX. U \<subseteq> X" unfolding is_topology_on_strict_def by (by100 blast)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                  \<comment> \<open>Compose pair + arith + hAc. Need to handle the if-then-else for ep.\<close>
                  \<comment> \<open>H\\_DR = formula on QA Aq + transfer continuity.\<close>
                  \<comment> \<open>Compose hpair\\_QA with appropriate arith and hAc.
                     Split QA into left half (\\<sigma> < tAc) and right half (\\<sigma> > tAc).
                     On left: use harith0. On right: use harith1. Paste.\<close>
                  define QA_L where "QA_L = {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq}"
                  define QA_R where "QA_R = {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq}"
                  have hQA_eq: "QA Aq = QA_L \<union> QA_R" unfolding QA_L_def QA_R_def by (by100 auto)
                  \<comment> \<open>On QA\\_L: g = harith0 \\<circ> pair. On QA\\_R: g = harith1 \\<circ> pair.\<close>
                  \<comment> \<open>Compose: hAc \\<circ> harith0 \\<circ> pair (left), hAc \\<circ> harith1 \\<circ> pair (right).\<close>
                  have hstep_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) X TX
                      (\<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                           snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p))))"
                  proof -
                    have "QA_L \<subseteq> QA Aq" unfolding QA_L_def by (by100 blast)
                    hence "QA_L \<subseteq> ?YI" using hQA_sub by (by100 blast)
                    have hpair_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                        (top1_unit_interval \<times> top1_unit_interval) ?IItop
                        (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                    proof -
                      from top1_continuous_map_on_restrict_domain_simple[OF hpair_QA \<open>QA_L \<subseteq> QA Aq\<close>]
                      have "top1_continuous_map_on QA_L
                          (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L)
                          (top1_unit_interval \<times> top1_unit_interval) ?IItop
                          (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))" .
                      moreover have "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L
                          = subspace_topology ?YI ?YItop QA_L"
                        by (rule subspace_topology_trans[OF \<open>QA_L \<subseteq> QA Aq\<close>])
                      ultimately show ?thesis by (by100 simp)
                    qed
                    have harith_pair_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                        top1_unit_interval top1_unit_interval_topology
                        ((\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                      by (rule top1_continuous_map_on_comp[OF hpair_L harith0])
                    have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) X TX
                        (hAc Aq \<circ> ((\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))))"
                      by (rule top1_continuous_map_on_comp[OF harith_pair_L hhAc_cont_X])
                    moreover have "\<And>p. (hAc Aq \<circ> (\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))) p =
                        hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                           snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                      unfolding comp_def by (by100 simp)
                    ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                  qed
                  have hstep_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) X TX
                      (\<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                           snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p))))"
                  proof -
                    have "QA_R \<subseteq> QA Aq" unfolding QA_R_def by (by100 blast)
                    hence "QA_R \<subseteq> ?YI" using hQA_sub by (by100 blast)
                    have hpair_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                        (top1_unit_interval \<times> top1_unit_interval) ?IItop
                        (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                    proof -
                      from top1_continuous_map_on_restrict_domain_simple[OF hpair_QA \<open>QA_R \<subseteq> QA Aq\<close>]
                      have "top1_continuous_map_on QA_R
                          (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R)
                          (top1_unit_interval \<times> top1_unit_interval) ?IItop
                          (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))" .
                      moreover have "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R
                          = subspace_topology ?YI ?YItop QA_R"
                        by (rule subspace_topology_trans[OF \<open>QA_R \<subseteq> QA Aq\<close>])
                      ultimately show ?thesis by (by100 simp)
                    qed
                    have harith_pair_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                        top1_unit_interval top1_unit_interval_topology
                        ((\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                      by (rule top1_continuous_map_on_comp[OF hpair_R harith1])
                    have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) X TX
                        (hAc Aq \<circ> ((\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))))"
                      by (rule top1_continuous_map_on_comp[OF harith_pair_R hhAc_cont_X])
                    moreover have "\<And>p. (hAc Aq \<circ> (\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                         (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))) p =
                        hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                           snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                      unfolding comp_def by (by100 simp)
                    ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                  qed
                  \<comment> \<open>QA\\_L, QA\\_R closed in Y\\<times>I. H\\_DR = formula. Pasting + codomain restrict.\<close>
                  \<comment> \<open>QA\\_L, QA\\_R closed in QA (preimage of closed interval).\<close>
                  have hQA_L_closed: "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L"
                  proof -
                    have hcl_I: "closedin_on top1_unit_interval top1_unit_interval_topology
                        {x \<in> top1_unit_interval. x \<le> tAc Aq}"
                    proof -
                      have "top1_unit_interval - {x \<in> top1_unit_interval. x \<le> tAc Aq}
                          = {x \<in> top1_unit_interval. x > tAc Aq}" by (by100 auto)
                      moreover have "{x \<in> top1_unit_interval. x > tAc Aq} \<in> top1_unit_interval_topology"
                      proof -
                        have "{x :: real. tAc Aq < x} \<in> top1_open_sets"
                        proof -
                          have "open {x :: real. tAc Aq < x}" using open_greaterThan
                            unfolding greaterThan_def by (by100 blast)
                          thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                        qed
                        have "{x \<in> top1_unit_interval. x > tAc Aq} = top1_unit_interval \<inter> {x. tAc Aq < x}"
                          by (by100 auto)
                        thus ?thesis
                          using \<open>{x. tAc Aq < x} \<in> top1_open_sets\<close>
                          unfolding top1_unit_interval_topology_def top1_unit_interval_def
                            subspace_topology_def by (by100 auto)
                      qed
                      ultimately have "top1_unit_interval - {x \<in> top1_unit_interval. x \<le> tAc Aq}
                          \<in> top1_unit_interval_topology" by (by100 simp)
                      moreover have "{x \<in> top1_unit_interval. x \<le> tAc Aq} \<subseteq> top1_unit_interval"
                        by (by100 blast)
                      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                    qed
                    from continuous_preimage_closedin[OF
                        subspace_topology_is_topology_on[OF hYI_top hQA_sub]
                        top1_unit_interval_topology_is_topology_on hinv_fst hcl_I]
                    have "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                        {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}" .
                    moreover have "{p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                        \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}} = QA_L"
                    proof (rule set_eqI, rule iffI)
                      fix p assume "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}"
                      thus "p \<in> QA_L" unfolding QA_L_def by (by100 blast)
                    next
                      fix p assume "p \<in> QA_L"
                      hence hp: "p \<in> QA Aq" "inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq"
                        unfolding QA_L_def by (by100 blast)+
                      have "fst p \<in> Aq \<inter> ?Y" using hp(1) unfolding QA_def by (by100 auto)
                      hence "fst p \<in> hAc Aq ` top1_unit_interval"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                        by (by100 blast)
                      hence "inv_into top1_unit_interval (hAc Aq) (fst p) \<in> top1_unit_interval"
                        by (rule inv_into_into)
                      thus "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}"
                        using hp by (by100 blast)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                  have hQA_R_closed: "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R"
                  proof -
                    have hcl_I: "closedin_on top1_unit_interval top1_unit_interval_topology
                        {x \<in> top1_unit_interval. x \<ge> tAc Aq}"
                    proof -
                      have "top1_unit_interval - {x \<in> top1_unit_interval. x \<ge> tAc Aq}
                          = {x \<in> top1_unit_interval. x < tAc Aq}" by (by100 auto)
                      moreover have "{x \<in> top1_unit_interval. x < tAc Aq} \<in> top1_unit_interval_topology"
                      proof -
                        have "{x :: real. x < tAc Aq} \<in> top1_open_sets"
                        proof -
                          have "open {x :: real. x < tAc Aq}" using open_lessThan
                            unfolding lessThan_def by (by100 blast)
                          thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                        qed
                        have "{x \<in> top1_unit_interval. x < tAc Aq} = top1_unit_interval \<inter> {x. x < tAc Aq}"
                          by (by100 auto)
                        thus ?thesis
                          using \<open>{x. x < tAc Aq} \<in> top1_open_sets\<close>
                          unfolding top1_unit_interval_topology_def top1_unit_interval_def
                            subspace_topology_def by (by100 auto)
                      qed
                      ultimately have "top1_unit_interval - {x \<in> top1_unit_interval. x \<ge> tAc Aq}
                          \<in> top1_unit_interval_topology" by (by100 simp)
                      moreover have "{x \<in> top1_unit_interval. x \<ge> tAc Aq} \<subseteq> top1_unit_interval"
                        by (by100 blast)
                      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                    qed
                    from continuous_preimage_closedin[OF
                        subspace_topology_is_topology_on[OF hYI_top hQA_sub]
                        top1_unit_interval_topology_is_topology_on hinv_fst hcl_I]
                    have "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                        {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}" .
                    moreover have "{p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                        \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}} = QA_R"
                    proof (rule set_eqI, rule iffI)
                      fix p assume "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}"
                      thus "p \<in> QA_R" unfolding QA_R_def by (by100 blast)
                    next
                      fix p assume "p \<in> QA_R"
                      hence hp: "p \<in> QA Aq" "inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq"
                        unfolding QA_R_def by (by100 blast)+
                      have "fst p \<in> Aq \<inter> ?Y" using hp(1) unfolding QA_def by (by100 auto)
                      hence "fst p \<in> hAc Aq ` top1_unit_interval"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                        by (by100 blast)
                      hence "inv_into top1_unit_interval (hAc Aq) (fst p) \<in> top1_unit_interval"
                        by (rule inv_into_into)
                      thus "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                          \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}"
                        using hp by (by100 blast)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                  \<comment> \<open>H\\_DR agrees with hstep\\_L on QA\\_L and hstep\\_R on QA\\_R.\<close>
                  have hH_img_QA: "\<forall>p\<in>QA Aq. H_DR p \<in> ?Y"
                    using hH_img hQA_sub by (by100 blast)
                  have hH_L_eq: "\<forall>p\<in>QA_L. H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                  proof (intro ballI)
                    fix p assume "p \<in> QA_L"
                    hence "p \<in> QA Aq" using hQA_eq by (by100 blast)
                    hence "fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
                    have hinv_le: "inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq"
                      using \<open>p \<in> QA_L\<close> unfolding QA_L_def by (by100 blast)
                    show "H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                         snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                    proof (cases "fst p \<in> ?target")
                      case True
                      \<comment> \<open>fst(p) \\<in> target: H\\_DR = fst(p). And \\<sigma>=0 (left endpoint), formula gives hAc(0)=fst(p).\<close>
                      have hHDR_eq: "H_DR p = fst p"
                      proof -
                        obtain x t where hxt: "p = (x, t)" by (cases p)
                        have "x \<in> ?target" using True hxt by (by100 simp)
                        thus ?thesis unfolding H_DR_def hxt by (by100 simp)
                      qed
                      have hfp_Aq: "fst p \<in> Aq" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                      have hfp_T: "fst p \<in> T"
                      proof -
                        from True have "fst p \<in> T \<or> fst p \<in> \<Union>(?NT - S)" by (by100 blast)
                        thus ?thesis
                        proof
                          assume "fst p \<in> T" thus ?thesis .
                        next
                          assume "fst p \<in> \<Union>(?NT - S)"
                          then obtain A' where "A' \<in> ?NT - S" "fst p \<in> A'" by (by100 blast)
                          have "A' \<in> \<A>" using \<open>A' \<in> ?NT - S\<close> by (by100 blast)
                          have "A' \<noteq> Aq" using \<open>A' \<in> ?NT - S\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                          have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                          have "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                            using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close> by (by100 blast)
                          have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          have "\<forall>e\<in>top1_arc_endpoints_on Aq (subspace_topology X TX Aq). e \<in> T"
                            using hNT_endpoints \<open>Aq \<in> ?NT\<close> by (by100 blast)
                          thus ?thesis using \<open>fst p \<in> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                        qed
                      qed
                      have hbij_Aq_loc: "bij_betw (hAc Aq) top1_unit_interval Aq"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                      have himg_Aq_loc: "hAc Aq ` top1_unit_interval = Aq"
                        using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                      have hfp_img: "fst p \<in> hAc Aq ` top1_unit_interval"
                        using hfp_Aq himg_Aq_loc by (by100 simp)
                      have hAc_inv: "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                        by (rule f_inv_into_f) (use hfp_img in blast)
                      \<comment> \<open>Show \\<sigma> = 0: fst p is an endpoint of Aq (T \\<cap> non-tree arc \\<subseteq> endpoints),
                         endpoints = {hAc 0, hAc 1}, and \\<sigma> \\<le> tAc < 1 rules out \\<sigma> = 1.\<close>
                      let ?\<sigma> = "inv_into top1_unit_interval (hAc Aq) (fst p)"
                      have h\<sigma>_0: "?\<sigma> = 0"
                      proof -
                        have hAq_in_A: "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                        have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                        hence "\<not> Aq \<subseteq> T" by (by100 blast)
                        from hT_subgraph[rule_format, OF hAq_in_A] \<open>\<not> Aq \<subseteq> T\<close>
                        have "Aq \<inter> T \<subseteq> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)" by (by100 blast)
                        hence hfp_ep: "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using hfp_T hfp_Aq by (by100 blast)
                        have hX_strict: "is_topology_on_strict X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hX_haus: "is_hausdorff_on X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have "Aq \<subseteq> X" using h\<A> hAq_in_A by (by100 blast)
                        have harc: "top1_is_arc_on Aq (subspace_topology X TX Aq)"
                          using h\<A> hAq_in_A by (by100 blast)
                        from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Aq \<subseteq> X\<close> harc hhAc[OF \<open>Aq \<in> S\<close>]]
                        have hep: "top1_arc_endpoints_on Aq (subspace_topology X TX Aq) = {hAc Aq 0, hAc Aq 1}" .
                        from hfp_ep hep have "fst p = hAc Aq 0 \<or> fst p = hAc Aq 1" by (by100 blast)
                        have hinj: "inj_on (hAc Aq) top1_unit_interval"
                          using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                        have h0_I: "(0::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have h1_I: "(1::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have h\<sigma>_I: "?\<sigma> \<in> top1_unit_interval"
                          using inv_into_into[OF hfp_img] by (by100 blast)
                        have "fst p \<noteq> hAc Aq 1"
                        proof
                          assume "fst p = hAc Aq 1"
                          hence "hAc Aq ?\<sigma> = hAc Aq 1" using hAc_inv by (by100 simp)
                          hence "?\<sigma> = 1" using hinj h\<sigma>_I h1_I unfolding inj_on_def by (by100 blast)
                          have "tAc Aq \<noteq> 1"
                          proof
                            assume "tAc Aq = 1"
                            have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                              using hps_loc \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                            have "hAc Aq (tAc Aq) = ps Aq"
                              unfolding tAc_def by (rule f_inv_into_f[OF hps_img])
                            hence "hAc Aq 1 = ps Aq" using \<open>tAc Aq = 1\<close> by (by100 simp)
                            hence "ps Aq \<in> {hAc Aq 0, hAc Aq 1}" by (by100 simp)
                            hence "ps Aq \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                              using hep by (by100 simp)
                            thus False using hps_loc \<open>Aq \<in> S\<close> by (by100 blast)
                          qed
                          have hps_img2: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                            using hps_loc \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                          have "tAc Aq \<in> top1_unit_interval"
                            using inv_into_into[OF hps_img2] unfolding tAc_def by (by100 blast)
                          hence "tAc Aq \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                          hence "tAc Aq < 1" using \<open>tAc Aq \<noteq> 1\<close> by (by100 linarith)
                          thus False using hinv_le \<open>?\<sigma> = 1\<close> by (by100 linarith)
                        qed
                        hence "fst p = hAc Aq 0" using \<open>fst p = hAc Aq 0 \<or> fst p = hAc Aq 1\<close> by (by100 blast)
                        hence "hAc Aq ?\<sigma> = hAc Aq 0" using hAc_inv by (by100 simp)
                        thus "?\<sigma> = 0" using hinj h\<sigma>_I h0_I unfolding inj_on_def by (by100 blast)
                      qed
                      show ?thesis using hHDR_eq hAc_inv h\<sigma>_0 by (by100 simp)
                    next
                      case False
                      \<comment> \<open>fst(p) \\<notin> target: THE = Aq, \\<sigma> < tAc, ep=0. Formula matches H\\_DR.\<close>
                      have hAq_NT: "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      have "fst p \<notin> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                        using hNT_endpoints[rule_format, OF hAq_NT] False by (by100 blast)
                      have hTHE: "(THE A. A \<in> S \<and> fst p \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Aq"
                      proof (rule the_equality)
                        show "Aq \<in> S \<and> fst p \<in> Aq - top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using \<open>Aq \<in> S\<close> \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close>
                          by (by100 blast)
                      next
                        fix A' assume "A' \<in> S \<and> fst p \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                        hence "A' \<in> \<A>" "fst p \<in> A'" using hS_sub by (by100 blast)+
                        show "A' = Aq"
                        proof (rule ccontr)
                          assume "A' \<noteq> Aq"
                          have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                          show False using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close>
                            \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                        qed
                      qed
                      have "fst p \<in> hAc Aq ` top1_unit_interval"
                      proof -
                        have hbij_loc2: "bij_betw (hAc Aq) top1_unit_interval Aq"
                          using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                        show ?thesis using \<open>fst p \<in> Aq \<inter> ?Y\<close> hbij_loc2 unfolding bij_betw_def by (by100 blast)
                      qed
                      have "fst p \<in> ?Y" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                      have h\<sigma>_ne: "inv_into top1_unit_interval (hAc Aq) (fst p) \<noteq> tAc Aq"
                      proof
                        assume "inv_into top1_unit_interval (hAc Aq) (fst p) = tAc Aq"
                        have "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                          by (rule f_inv_into_f[OF \<open>fst p \<in> hAc Aq ` top1_unit_interval\<close>])
                        have "ps Aq \<in> hAc Aq ` top1_unit_interval"
                        proof -
                          have himg_loc3: "hAc Aq ` top1_unit_interval = Aq"
                            using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                            by (by100 blast)
                          show ?thesis using hps_loc \<open>Aq \<in> S\<close> himg_loc3 by (by100 blast)
                        qed
                        have "hAc Aq (tAc Aq) = ps Aq"
                          unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Aq \<in> hAc Aq ` _\<close>])
                        hence "fst p = ps Aq"
                          using \<open>hAc Aq _ = fst p\<close> \<open>inv_into _ _ (fst p) = tAc Aq\<close> by (by100 simp)
                        thus False using \<open>fst p \<in> ?Y\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                      qed
                      hence "inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq"
                        using hinv_le by (by100 linarith)
                      hence "(if inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq then (0::real) else 1) = 0"
                        by (by100 simp)
                      obtain x t where hxt2: "p = (x, t)" by (cases p)
                      have "x \<notin> ?target" using False hxt2 by (by100 simp)
                      show ?thesis unfolding H_DR_def Let_def hxt2
                        using \<open>x \<notin> ?target\<close> hTHE \<open>(if _ then (0::real) else 1) = 0\<close>
                        hxt2 by (by100 simp)
                    qed
                  qed
                  have hH_R_eq: "\<forall>p\<in>QA_R. H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                  proof (intro ballI)
                    fix p assume "p \<in> QA_R"
                    hence "p \<in> QA Aq" using hQA_eq by (by100 blast)
                    hence "fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
                    have hinv_ge: "inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq"
                      using \<open>p \<in> QA_R\<close> unfolding QA_R_def by (by100 blast)
                    show "H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                         snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                    proof (cases "fst p \<in> ?target")
                      case True
                      have hHDR_eq: "H_DR p = fst p"
                      proof -
                        obtain x t where hxt: "p = (x, t)" by (cases p)
                        have "x \<in> ?target" using True hxt by (by100 simp)
                        thus ?thesis unfolding H_DR_def hxt by (by100 simp)
                      qed
                      have hfp_Aq: "fst p \<in> Aq" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                      have hfp_T: "fst p \<in> T"
                      proof -
                        from True have "fst p \<in> T \<or> fst p \<in> \<Union>(?NT - S)" by (by100 blast)
                        thus ?thesis
                        proof
                          assume "fst p \<in> T" thus ?thesis .
                        next
                          assume "fst p \<in> \<Union>(?NT - S)"
                          then obtain A' where "A' \<in> ?NT - S" "fst p \<in> A'" by (by100 blast)
                          have "A' \<in> \<A>" using \<open>A' \<in> ?NT - S\<close> by (by100 blast)
                          have "A' \<noteq> Aq" using \<open>A' \<in> ?NT - S\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                          have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                          have "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                            using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close> by (by100 blast)
                          have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          thus ?thesis using hNT_endpoints \<open>Aq \<in> ?NT\<close>
                            \<open>fst p \<in> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                        qed
                      qed
                      have hbij_Aq_loc: "bij_betw (hAc Aq) top1_unit_interval Aq"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                      have himg_Aq_loc: "hAc Aq ` top1_unit_interval = Aq"
                        using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                      have hfp_img: "fst p \<in> hAc Aq ` top1_unit_interval"
                        using hfp_Aq himg_Aq_loc by (by100 simp)
                      have hAc_inv: "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                        by (rule f_inv_into_f) (use hfp_img in blast)
                      let ?\<sigma> = "inv_into top1_unit_interval (hAc Aq) (fst p)"
                      have h\<sigma>_1: "?\<sigma> = 1"
                      proof -
                        have hAq_in_A: "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                        have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                        hence "\<not> Aq \<subseteq> T" by (by100 blast)
                        from hT_subgraph[rule_format, OF hAq_in_A] \<open>\<not> Aq \<subseteq> T\<close>
                        have "Aq \<inter> T \<subseteq> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)" by (by100 blast)
                        hence hfp_ep: "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using hfp_T hfp_Aq by (by100 blast)
                        have hX_strict: "is_topology_on_strict X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hX_haus: "is_hausdorff_on X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have "Aq \<subseteq> X" using h\<A> hAq_in_A by (by100 blast)
                        have harc: "top1_is_arc_on Aq (subspace_topology X TX Aq)"
                          using h\<A> hAq_in_A by (by100 blast)
                        from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Aq \<subseteq> X\<close> harc hhAc[OF \<open>Aq \<in> S\<close>]]
                        have hep: "top1_arc_endpoints_on Aq (subspace_topology X TX Aq) = {hAc Aq 0, hAc Aq 1}" .
                        from hfp_ep hep have "fst p = hAc Aq 0 \<or> fst p = hAc Aq 1" by (by100 blast)
                        have hinj: "inj_on (hAc Aq) top1_unit_interval"
                          using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                        have h0_I: "(0::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have h1_I: "(1::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have h\<sigma>_I: "?\<sigma> \<in> top1_unit_interval"
                          using inv_into_into[OF hfp_img] by (by100 blast)
                        have "fst p \<noteq> hAc Aq 0"
                        proof
                          assume "fst p = hAc Aq 0"
                          hence "hAc Aq ?\<sigma> = hAc Aq 0" using hAc_inv by (by100 simp)
                          hence "?\<sigma> = 0" using hinj h\<sigma>_I h0_I unfolding inj_on_def by (by100 blast)
                          have "tAc Aq \<noteq> 0"
                          proof
                            assume "tAc Aq = 0"
                            have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                              using hps_loc \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                            have "hAc Aq (tAc Aq) = ps Aq"
                              unfolding tAc_def by (rule f_inv_into_f[OF hps_img])
                            hence "hAc Aq 0 = ps Aq" using \<open>tAc Aq = 0\<close> by (by100 simp)
                            hence "ps Aq \<in> {hAc Aq 0, hAc Aq 1}" by (by100 simp)
                            hence "ps Aq \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                              using hep by (by100 simp)
                            thus False using hps_loc \<open>Aq \<in> S\<close> by (by100 blast)
                          qed
                          have "tAc Aq \<in> top1_unit_interval"
                          proof -
                            have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                              using hps_loc \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                            show ?thesis using inv_into_into[OF hps_img] unfolding tAc_def by (by100 blast)
                          qed
                          hence "tAc Aq \<ge> 0" unfolding top1_unit_interval_def by (by100 simp)
                          hence "tAc Aq > 0" using \<open>tAc Aq \<noteq> 0\<close> by (by100 linarith)
                          thus False using hinv_ge \<open>?\<sigma> = 0\<close> by (by100 linarith)
                        qed
                        hence "fst p = hAc Aq 1" using \<open>fst p = hAc Aq 0 \<or> fst p = hAc Aq 1\<close> by (by100 blast)
                        hence "hAc Aq ?\<sigma> = hAc Aq 1" using hAc_inv by (by100 simp)
                        thus "?\<sigma> = 1" using hinj h\<sigma>_I h1_I unfolding inj_on_def by (by100 blast)
                      qed
                      show ?thesis using hHDR_eq hAc_inv h\<sigma>_1 by (by100 simp)
                    next
                      case False
                      have hAq_NT: "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      have "fst p \<notin> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                        using hNT_endpoints[rule_format, OF hAq_NT] False by (by100 blast)
                      have hTHE: "(THE A. A \<in> S \<and> fst p \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Aq"
                      proof (rule the_equality)
                        show "Aq \<in> S \<and> fst p \<in> Aq - top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using \<open>Aq \<in> S\<close> \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close>
                          by (by100 blast)
                      next
                        fix A' assume "A' \<in> S \<and> fst p \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                        hence "A' \<in> \<A>" "fst p \<in> A'" using hS_sub by (by100 blast)+
                        show "A' = Aq"
                        proof (rule ccontr)
                          assume "A' \<noteq> Aq"
                          have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                          from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                          show False using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close>
                            \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                        qed
                      qed
                      have "fst p \<in> hAc Aq ` top1_unit_interval"
                      proof -
                        have hbij_loc2: "bij_betw (hAc Aq) top1_unit_interval Aq"
                          using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                        show ?thesis using \<open>fst p \<in> Aq \<inter> ?Y\<close> hbij_loc2 unfolding bij_betw_def by (by100 blast)
                      qed
                      have "fst p \<in> ?Y" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                      have h\<sigma>_ne: "inv_into top1_unit_interval (hAc Aq) (fst p) \<noteq> tAc Aq"
                      proof
                        assume "inv_into top1_unit_interval (hAc Aq) (fst p) = tAc Aq"
                        have "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                          by (rule f_inv_into_f[OF \<open>fst p \<in> hAc Aq ` top1_unit_interval\<close>])
                        have "ps Aq \<in> hAc Aq ` top1_unit_interval"
                        proof -
                          have himg_loc3: "hAc Aq ` top1_unit_interval = Aq"
                            using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                            by (by100 blast)
                          show ?thesis using hps_loc \<open>Aq \<in> S\<close> himg_loc3 by (by100 blast)
                        qed
                        have "hAc Aq (tAc Aq) = ps Aq"
                          unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Aq \<in> hAc Aq ` _\<close>])
                        hence "fst p = ps Aq"
                          using \<open>hAc Aq _ = fst p\<close> \<open>inv_into _ _ (fst p) = tAc Aq\<close> by (by100 simp)
                        thus False using \<open>fst p \<in> ?Y\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                      qed
                      hence "inv_into top1_unit_interval (hAc Aq) (fst p) > tAc Aq"
                        using hinv_ge by (by100 linarith)
                      hence "(if inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq then (0::real) else 1) = 1"
                        by (by100 simp)
                      obtain x t where hxt2: "p = (x, t)" by (cases p)
                      have "x \<notin> ?target" using False hxt2 by (by100 simp)
                      show ?thesis unfolding H_DR_def Let_def hxt2
                        using \<open>x \<notin> ?target\<close> hTHE \<open>(if _ then (0::real) else 1) = 1\<close>
                        hxt2 by (by100 simp)
                    qed
                  qed
                  \<comment> \<open>hstep\\_L/R restricted to QA\\_L/R in QA's subspace.\<close>
                  \<comment> \<open>H\\_DR continuous on QA\\_L (from hstep\\_L + formula equality + codomain restrict).\<close>
                  have hstep_L_QA: "top1_continuous_map_on QA_L
                      (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L) ?Y ?TY H_DR"
                  proof -
                    have hQA_L_sub: "QA_L \<subseteq> QA Aq" unfolding QA_L_def by (by100 blast)
                    have htop_L: "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L
                        = subspace_topology ?YI ?YItop QA_L"
                      by (rule subspace_topology_trans[OF hQA_L_sub])
                    have "\<forall>p\<in>QA_L. H_DR p \<in> ?Y" using hH_img_QA hQA_eq by (by100 blast)
                    \<comment> \<open>hstep\\_L gives the formula continuous QA\\_L \\<rightarrow> X. Restrict to Y.\<close>
                    define fL where "fL \<equiv> \<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                         snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                    have hfL_cont: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                        X TX fL" using hstep_L unfolding fL_def .
                    have hfL_img_Y: "\<forall>p\<in>QA_L. fL p \<in> ?Y"
                      using hH_L_eq \<open>\<forall>p\<in>QA_L. H_DR p \<in> ?Y\<close> unfolding fL_def by (by100 auto)
                    from continuous_map_restrict_codomain[OF hfL_cont hfL_img_Y hY_sub]
                    have hfL_cont_Y: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                        ?Y ?TY fL" .
                    have hH_fL: "\<forall>p\<in>QA_L. H_DR p = fL p" using hH_L_eq unfolding fL_def by (by100 auto)
                    have "\<forall>V\<in>?TY. {p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L"
                    proof (intro ballI)
                      fix V assume "V \<in> ?TY"
                      have "{p \<in> QA_L. H_DR p \<in> V} = {p \<in> QA_L. fL p \<in> V}" using hH_fL by (by100 auto)
                      also have "... \<in> subspace_topology ?YI ?YItop QA_L"
                        using hfL_cont_Y \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                      finally show "{p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L" .
                    qed
                    have hQA_L_sub2: "QA_L \<subseteq> ?YI" using hQA_sub hQA_eq by (by100 blast)
                    have "is_topology_on QA_L (subspace_topology ?YI ?YItop QA_L)"
                      by (rule subspace_topology_is_topology_on[OF hYI_top hQA_L_sub2])
                    have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) ?Y ?TY H_DR"
                      unfolding top1_continuous_map_on_def
                      using \<open>is_topology_on QA_L _\<close> hTY_top \<open>\<forall>p\<in>QA_L. H_DR p \<in> ?Y\<close>
                      \<open>\<forall>V\<in>?TY. {p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L\<close>
                      by (by100 blast)
                    show ?thesis
                    proof -
                      have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) ?Y ?TY H_DR"
                        using \<open>top1_continuous_map_on QA_L _ ?Y ?TY H_DR\<close> .
                      thus ?thesis unfolding htop_L .
                    qed
                  qed
                  have hstep_R_QA: "top1_continuous_map_on QA_R
                      (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R) ?Y ?TY H_DR"
                  proof -
                    have hQA_R_sub: "QA_R \<subseteq> QA Aq" unfolding QA_R_def by (by100 blast)
                    have htop_R: "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R
                        = subspace_topology ?YI ?YItop QA_R"
                      by (rule subspace_topology_trans[OF hQA_R_sub])
                    have "\<forall>p\<in>QA_R. H_DR p \<in> ?Y" using hH_img_QA hQA_eq by (by100 blast)
                    define fR where "fR \<equiv> \<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                         snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                    have hfR_cont: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                        X TX fR" using hstep_R unfolding fR_def .
                    have hfR_img_Y: "\<forall>p\<in>QA_R. fR p \<in> ?Y"
                      using hH_R_eq \<open>\<forall>p\<in>QA_R. H_DR p \<in> ?Y\<close> unfolding fR_def by (by100 auto)
                    from continuous_map_restrict_codomain[OF hfR_cont hfR_img_Y hY_sub]
                    have hfR_cont_Y: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                        ?Y ?TY fR" .
                    have hH_fR: "\<forall>p\<in>QA_R. H_DR p = fR p" using hH_R_eq unfolding fR_def by (by100 auto)
                    have "\<forall>V\<in>?TY. {p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R"
                    proof (intro ballI)
                      fix V assume "V \<in> ?TY"
                      have "{p \<in> QA_R. H_DR p \<in> V} = {p \<in> QA_R. fR p \<in> V}" using hH_fR by (by100 auto)
                      also have "... \<in> subspace_topology ?YI ?YItop QA_R"
                        using hfR_cont_Y \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                      finally show "{p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R" .
                    qed
                    have hQA_R_sub2: "QA_R \<subseteq> ?YI" using hQA_sub hQA_eq by (by100 blast)
                    have "is_topology_on QA_R (subspace_topology ?YI ?YItop QA_R)"
                      by (rule subspace_topology_is_topology_on[OF hYI_top hQA_R_sub2])
                    have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) ?Y ?TY H_DR"
                      unfolding top1_continuous_map_on_def
                      using \<open>is_topology_on QA_R _\<close> hTY_top \<open>\<forall>p\<in>QA_R. H_DR p \<in> ?Y\<close>
                      \<open>\<forall>V\<in>?TY. {p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R\<close>
                      by (by100 blast)
                    show ?thesis
                    proof -
                      have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) ?Y ?TY H_DR"
                        using \<open>top1_continuous_map_on QA_R _ ?Y ?TY H_DR\<close> .
                      thus ?thesis unfolding htop_R .
                    qed
                  qed
                  \<comment> \<open>Pasting QA\\_L and QA\\_R.\<close>
                  show ?thesis
                    by (rule pasting_lemma_two_closed[OF hQA_top hTY_top
                        hQA_L_closed hQA_R_closed hQA_eq[symmetric] hH_img_QA
                        hstep_L_QA hstep_R_QA])
                qed
              qed
              \<comment> \<open>Finite pasting: D\\_B = \\<Union>{QA A | A \\<in> S}, each closed, H cont on each.\<close>
              have "\<forall>V\<in>?TY. {p \<in> D_B. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_B"
              proof (intro ballI)
                fix V assume "V \<in> ?TY"
                \<comment> \<open>Complement: D\\_B - preimage = \\<Union>{QA A - preimage | A \\<in> S}.\<close>
                have "D_B - {p \<in> D_B. H_DR p \<in> V} = (\<Union>A\<in>S. QA A - {p \<in> QA A. H_DR p \<in> V})"
                  using hDB_eq by (by100 blast)
                \<comment> \<open>Each QA A - preimage is closed in Y\\<times>I.\<close>
                have hcompl_closed: "\<forall>A\<in>S. closedin_on ?YI ?YItop (QA A - {p \<in> QA A. H_DR p \<in> V})"
                proof (intro ballI)
                  fix A assume "A \<in> S"
                  have "{p \<in> QA A. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop (QA A)"
                    using hH_QA \<open>A \<in> S\<close> \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                  have hQA_sub: "QA A \<subseteq> ?YI" using hQA_closed \<open>A \<in> S\<close>
                    unfolding closedin_on_def by (by100 blast)
                  have hQA_top: "is_topology_on (QA A) (subspace_topology ?YI ?YItop (QA A))"
                    by (rule subspace_topology_is_topology_on[OF hYI_top hQA_sub])
                  have "QA A - {p \<in> QA A. H_DR p \<in> V} \<subseteq> QA A" by (by100 blast)
                  moreover have "QA A - (QA A - {p \<in> QA A. H_DR p \<in> V}) = {p \<in> QA A. H_DR p \<in> V}"
                    by (by100 blast)
                  hence "QA A - (QA A - {p \<in> QA A. H_DR p \<in> V}) \<in> subspace_topology ?YI ?YItop (QA A)"
                    using \<open>{p \<in> QA A. H_DR p \<in> V} \<in> _\<close> by (by100 simp)
                  ultimately have "closedin_on (QA A) (subspace_topology ?YI ?YItop (QA A))
                      (QA A - {p \<in> QA A. H_DR p \<in> V})"
                    unfolding closedin_on_def by (by100 blast)
                  from Theorem_17_3[OF hYI_top _ this]
                  show "closedin_on ?YI ?YItop (QA A - {p \<in> QA A. H_DR p \<in> V})"
                    using hQA_closed \<open>A \<in> S\<close> by (by100 blast)
                qed
                have "closedin_on ?YI ?YItop (\<Union>A\<in>S. QA A - {p \<in> QA A. H_DR p \<in> V})"
                  by (rule closedin_on_finite_indexed_Union[OF hYI_top hS_fin])
                     (use hcompl_closed in \<open>by100 blast\<close>)
                hence "closedin_on ?YI ?YItop (D_B - {p \<in> D_B. H_DR p \<in> V})"
                  using \<open>D_B - {p \<in> D_B. H_DR p \<in> V} = _\<close> by (by100 simp)
                \<comment> \<open>Closed in D\\_B (from closed in Y\\<times>I via Theorem\\_17\\_2).\<close>
                from Theorem_17_2[OF hYI_top hDB_sub, of "D_B - {p \<in> D_B. H_DR p \<in> V}"]
                have "closedin_on D_B (subspace_topology ?YI ?YItop D_B)
                    (D_B - {p \<in> D_B. H_DR p \<in> V})"
                  using \<open>closedin_on ?YI ?YItop (D_B - {p \<in> D_B. H_DR p \<in> V})\<close> by (by100 blast)
                hence "D_B - (D_B - {p \<in> D_B. H_DR p \<in> V}) \<in> subspace_topology ?YI ?YItop D_B"
                  unfolding closedin_on_def by (by100 blast)
                moreover have "D_B - (D_B - {p \<in> D_B. H_DR p \<in> V}) = {p \<in> D_B. H_DR p \<in> V}"
                  by (by100 blast)
                ultimately show "{p \<in> D_B. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_B"
                  by (by100 simp)
              qed
              show ?thesis unfolding top1_continuous_map_on_def
                using hDB_top hTY_top hH_img_DB \<open>\<forall>V\<in>?TY. _\<close> by (by100 blast)
            qed
            \<comment> \<open>Pasting D\\_T and D\\_B.\<close>
            show ?thesis
              by (rule pasting_lemma_two_closed[OF hYI_top hTY_top hDT_closed hDB_closed
                  hcover hH_img hH_DT hH_DB])
          qed
          ultimately show "top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H_DR
              \<and> (\<forall>x\<in>?Y. H_DR (x, 0) = x) \<and> (\<forall>x\<in>?Y. H_DR (x, 1) \<in> ?target)
              \<and> (\<forall>a\<in>?target. \<forall>t\<in>I_set. H_DR (a, t) = a)" by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>The proof depends on whether ?NT is finite or infinite.\\<close>
    show ?thesis
    proof (cases "finite ?NT")
      case True
      \<comment> \<open>Finite case: induction on card ?NT.\\<close>
      \<comment> \<open>Use strong induction on card(NT). The IH needs the full graph structure.\<close>
      \<comment> \<open>Finite case: induction on card NT using SvK.
         Key tools: hdr (ZERO SORRY), graph\\_remove\\_interior\\_points\\_sc (ZERO SORRY),
         Theorem\\_58\\_3 (DR \\<rightarrow> \\<pi>\\_1 iso), svk\\_free\\_product\\_free.\<close>
      have hNT_ne: "?NT \<noteq> {}" using False by (by100 blast)
      then obtain A1 where hA1: "A1 \<in> ?NT" by (by100 blast)
      show ?thesis
      proof (cases "card ?NT = 1")
        case True
        \<comment> \<open>Base case: exactly 1 non-tree arc. \\<pi>\\_1(X) is free on 1 generator.\<close>
        \<comment> \<open>Book Step 2: exactly 1 non-tree arc D = A1.
           U = Int(D) = D - endpoints (open arc, simply connected).
           V = X - {p} for interior p of D (DR onto T, simply connected).
           U \\<inter> V = U - {p}: two path components A, B.
           Theorem 63.1: [\\<alpha>*\\<beta>] generates \\<pi>\\_1(X) and has infinite order.
           Hence \\<pi>\\_1(X) \\<cong> \\<Z> = free on 1 generator.\<close>
        have hNT_singleton: "?NT = {A1}"
        proof -
          from card_1_singletonE[OF True] obtain B where hB: "?NT = {B}" by (by100 blast)
          hence "A1 = B" using hA1 by (by100 blast)
          thus ?thesis using hB by (by100 simp)
        qed
        \<comment> \<open>A1 endpoints in T.\<close>
        have hA1_arc: "top1_is_arc_on A1 (subspace_topology X TX A1)"
          using h\<A> hA1 by (by100 blast)
        have hA1_sub: "A1 \<subseteq> X" using h\<A> hA1 by (by100 blast)
        \<comment> \<open>X = T \\<union> A1 (since NT = {A1}, all other arcs \\<subseteq> T).\<close>
        have hX_eq: "X = T \<union> A1"
        proof -
          have "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A = A1"
          proof (intro ballI)
            fix A assume "A \<in> \<A>"
            show "A \<subseteq> T \<or> A = A1"
            proof (cases "A \<subseteq> T")
              case True thus ?thesis by (by100 blast)
            next
              case False
              hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
              thus ?thesis using hNT_singleton by (by100 blast)
            qed
          qed
          hence "\<Union>\<A> \<subseteq> T \<union> A1" by (by100 blast)
          hence "X \<subseteq> T \<union> A1" using h\<A>_cover by (by100 simp)
          moreover have "T \<union> A1 \<subseteq> X" using hT_sub hA1_sub by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        \<comment> \<open>\\<pi>\\_1(X, x0) \\<cong> \\<Z>: use Theorem 63.1 machinery.
           The key: U = Int(A1) open arc (simply connected),
           V = X - {p} DR onto T (simply connected),
           U \\<inter> V has two path components.\<close>
        have hpi1_iso_Z: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
            top1_Z_group top1_Z_mul"
        proof -
          \<comment> \<open>Book Step 2: X = T \\<union> A1 with 1 non-tree arc A1.
             Set up Lemma 84.6: U = Int(A1), V = X - {p}, apply two-component SvK.\<close>
          have hX_strict: "is_topology_on_strict X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          \<comment> \<open>Get homeomorphism h: [0,1] \\<rightarrow> A1.\<close>
          obtain hA where hhA: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A1 (subspace_topology X TX A1) hA"
            using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
          \<comment> \<open>Endpoints and midpoint.\<close>
          let ?ep_l = "hA 0" and ?ep_r = "hA 1" and ?mid = "hA (1/2)"
          \<comment> \<open>U = Int(A1) = A1 - {endpoints}.\<close>
          let ?U = "A1 - {?ep_l, ?ep_r}"
          \<comment> \<open>V = X - {midpoint}.\<close>
          let ?V = "X - {?mid}"
          \<comment> \<open>Choose a basepoint a in the intersection.\<close>
          let ?pt_a = "hA (1/4)"
          \<comment> \<open>Intermediate point.\<close>
          let ?pt_b = "hA (3/4)"
          \<comment> \<open>All the setup for Lemma 84.6.\<close>
          have hU_open_loc: "openin_on X TX ?U"
          proof -
            \<comment> \<open>Show X - U is closed via coherent topology.\<close>
            have "X - ?U \<subseteq> X" by (by100 blast)
            have "\<forall>B\<in>\<A>. closedin_on B (subspace_topology X TX B) (B \<inter> (X - ?U))"
            proof (intro ballI)
              fix B assume "B \<in> \<A>"
              have "B \<subseteq> X" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
              show "closedin_on B (subspace_topology X TX B) (B \<inter> (X - ?U))"
              proof (cases "B = A1")
                case True
                \<comment> \<open>B = A1: B \\<inter> (X-U) = {hA 0, hA 1}, finite \\<Rightarrow> closed in Hausdorff.\<close>
                have "B \<inter> (X - ?U) = {?ep_l, ?ep_r}"
                proof -
                  have "?U = A1 - {?ep_l, ?ep_r}" by (by100 blast)
                  have "hA 0 \<in> A1 \<and> hA 1 \<in> A1"
                  proof -
                    have hbij0: "bij_betw hA top1_unit_interval A1"
                      using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
                    have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    show ?thesis using hbij0 \<open>(0::real) \<in> _\<close> \<open>(1::real) \<in> _\<close> unfolding bij_betw_def by (by100 blast)
                  qed
                  hence "{?ep_l, ?ep_r} \<subseteq> X" using hA1_sub by (by100 blast)
                  have "X - ?U = (X - A1) \<union> {?ep_l, ?ep_r}"
                    using \<open>{?ep_l, ?ep_r} \<subseteq> X\<close> by (by100 blast)
                  have "A1 \<inter> ((X - A1) \<union> {?ep_l, ?ep_r}) = {?ep_l, ?ep_r} \<inter> A1" by (by100 blast)
                  have "hA 0 \<in> A1 \<and> hA 1 \<in> A1"
                  proof -
                    have hbij: "bij_betw hA top1_unit_interval A1"
                      using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
                    have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    show ?thesis using hbij \<open>(0::real) \<in> _\<close> \<open>(1::real) \<in> _\<close> unfolding bij_betw_def by (by100 blast)
                  qed
                  thus ?thesis using True \<open>X - ?U = _\<close> by (by100 blast)
                qed
                have hX_haus_loc: "is_hausdorff_on X TX"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have "is_hausdorff_on B (subspace_topology X TX B)"
                  using conjunct2[OF conjunct2[OF Theorem_17_11]] hX_haus_loc \<open>B \<subseteq> X\<close> by (by100 blast)
                have hfin_ep: "finite {?ep_l, ?ep_r}" by (by100 simp)
                have "{?ep_l, ?ep_r} \<subseteq> B"
                proof -
                  have hbij: "bij_betw hA top1_unit_interval A1"
                    using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
                  have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                  have "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                  have "hA 0 \<in> A1" using hbij \<open>(0::real) \<in> _\<close> unfolding bij_betw_def by (by100 blast)
                  have "hA 1 \<in> A1" using hbij \<open>(1::real) \<in> _\<close> unfolding bij_betw_def by (by100 blast)
                  thus ?thesis using True \<open>hA 0 \<in> A1\<close> \<open>hA 1 \<in> A1\<close> by (by100 blast)
                qed
                from Theorem_17_8[OF \<open>is_hausdorff_on B _\<close> hfin_ep this]
                have "closedin_on B (subspace_topology X TX B) {?ep_l, ?ep_r}" .
                thus ?thesis using \<open>B \<inter> (X - ?U) = _\<close> by (by100 simp)
              next
                case False
                \<comment> \<open>B \\<noteq> A1: B \\<inter> (A1 - endpoints) = \\<emptyset>, so B \\<inter> (X-U) = B, closed.\<close>
                have "A1 \<in> \<A>" using hA1 by (by100 blast)
                from h\<A>_inter[rule_format, OF \<open>A1 \<in> \<A>\<close> \<open>B \<in> \<A>\<close> False[symmetric]]
                have "A1 \<inter> B \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)" by (by100 blast)
                have hep_eq: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {?ep_l, ?ep_r}"
                proof -
                  have "is_hausdorff_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  show ?thesis by (rule arc_endpoints_are_boundary[OF hX_strict \<open>is_hausdorff_on X TX\<close> hA1_sub hA1_arc hhA])
                qed
                have "B \<inter> (A1 - {?ep_l, ?ep_r}) = {}"
                  using \<open>A1 \<inter> B \<subseteq> top1_arc_endpoints_on A1 _\<close> hep_eq by (by100 blast)
                hence "B \<inter> (X - ?U) = B"
                proof -
                  \<comment> \<open>B \\<inter> (A1 - {ep}) = \\<emptyset> means B has no interior points of A1.
                     So every point of B is either not in A1, or is an endpoint of A1.\<close>
                  have "\<forall>x. x \<in> B \<longrightarrow> x \<notin> A1 \<or> x \<in> {?ep_l, ?ep_r}"
                    using \<open>B \<inter> (A1 - {?ep_l, ?ep_r}) = {}\<close> by (by100 blast)
                  hence "\<forall>x. x \<in> B \<longrightarrow> x \<notin> A1 - {?ep_l, ?ep_r}" by (by100 blast)
                  thus ?thesis using \<open>B \<subseteq> X\<close> by (by100 blast)
                qed
                thus ?thesis
                  using closedin_carrier[OF subspace_topology_is_topology_on[OF
                      is_topology_on_strict_imp[OF hX_strict] \<open>B \<subseteq> X\<close>]]
                  by (by100 simp)
              qed
            qed
            from h\<A>_coh[rule_format, OF \<open>X - ?U \<subseteq> X\<close>] this
            have "closedin_on X TX (X - ?U)" by (by100 blast)
            hence "X - (X - ?U) \<in> TX" unfolding closedin_on_def by (by100 blast)
            have "?U \<subseteq> X" using hA1_sub by (by100 blast)
            hence "X - (X - ?U) = ?U" by (by100 blast)
            thus ?thesis unfolding openin_on_def using \<open>X - (X - ?U) \<in> TX\<close> \<open>?U \<subseteq> X\<close>
              \<open>X - (X - ?U) = ?U\<close> by (by100 simp)
          qed
          have hV_open_loc: "openin_on X TX ?V"
          proof -
            have hX_haus: "is_hausdorff_on X TX"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            have hmid_X: "?mid \<in> X"
            proof -
              have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              hence "hA (1/2) \<in> A1"
                using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis using hA1_sub by (by100 blast)
            qed
            have "finite {?mid}" by (by100 simp)
            have "closedin_on X TX {?mid}"
              using Theorem_17_8[OF hX_haus \<open>finite {?mid}\<close>] hmid_X by (by100 blast)
            thus ?thesis unfolding openin_on_def closedin_on_def by (by100 blast)
          qed
          have hcover_loc: "?U \<union> ?V = X"
          proof -
            have hinj: "inj_on hA top1_unit_interval"
              using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h12_I: "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "hA (1/2) \<noteq> hA 0"
            proof
              assume "hA (1/2) = hA 0"
              hence "(1/2::real) = 0" using hinj h12_I h0_I unfolding inj_on_def by (by100 blast)
              thus False by (by100 simp)
            qed
            have "hA (1/2) \<noteq> hA 1"
            proof
              assume "hA (1/2) = hA 1"
              hence "(1/2::real) = 1" using hinj h12_I h1_I unfolding inj_on_def by (by100 blast)
              thus False by (by100 simp)
            qed
            show ?thesis
            proof (rule set_eqI, rule iffI)
              fix x assume "x \<in> ?U \<union> ?V" thus "x \<in> X" using hX_eq by (by100 blast)
            next
              fix x assume "x \<in> X"
              show "x \<in> ?U \<union> ?V"
              proof (cases "x = hA (1/2)")
                case True
                hence "x \<in> A1" using hhA unfolding top1_homeomorphism_on_def bij_betw_def
                  top1_unit_interval_def by (by100 auto)
                moreover have "x \<noteq> hA 0" "x \<noteq> hA 1"
                  using True \<open>hA (1/2) \<noteq> hA 0\<close> \<open>hA (1/2) \<noteq> hA 1\<close> by (by100 simp)+
                ultimately show ?thesis by (by100 blast)
              next
                case False thus ?thesis using \<open>x \<in> X\<close> by (by100 blast)
              qed
            qed
          qed
          \<comment> \<open>U \\<inter> V has two path components A, B.\<close>
          let ?A_comp = "hA ` {t. 0 < t \<and> t < 1/2}"
          let ?B_comp = "hA ` {t. 1/2 < t \<and> t < 1}"
          have hUV_split: "?U \<inter> ?V = ?A_comp \<union> ?B_comp"
          proof -
            have hbij: "bij_betw hA top1_unit_interval A1"
              using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj: "inj_on hA top1_unit_interval"
              using hbij unfolding bij_betw_def by (by100 blast)
            have himg: "hA ` top1_unit_interval = A1"
              using hbij unfolding bij_betw_def by (by100 blast)
            \<comment> \<open>?U \\<inter> ?V = A1 - {hA 0, hA 1, hA(1/2)} = hA \\` ((0,1) - {1/2})\<close>
            have "?U \<inter> ?V = A1 - {hA 0, hA 1, hA (1/2)}"
              using hA1_sub by (by100 blast)
            moreover have "A1 - {hA 0, hA 1, hA (1/2)} = hA ` ({t. 0 < t \<and> t < 1} - {1/2})"
            proof (rule set_eqI, rule iffI)
              fix x assume "x \<in> A1 - {hA 0, hA 1, hA (1/2)}"
              hence hx_A1: "x \<in> A1" and hx_ne: "x \<noteq> hA 0" "x \<noteq> hA 1" "x \<noteq> hA (1/2)"
                by (by100 blast)+
              have "x \<in> hA ` top1_unit_interval" using himg hx_A1 by (by100 simp)
              then obtain t where ht: "t \<in> top1_unit_interval" "x = hA t" by (by100 blast)
              have "t \<noteq> 0"
              proof assume "t = 0" thus False using hx_ne(1) ht(2) by (by100 simp) qed
              have "t \<noteq> 1"
              proof assume "t = 1" thus False using hx_ne(2) ht(2) by (by100 simp) qed
              have "t \<noteq> 1/2"
              proof assume "t = 1/2" thus False using hx_ne(3) ht(2) by (by100 simp) qed
              have "0 \<le> t" "t \<le> 1"
                using ht(1) unfolding top1_unit_interval_def by (by100 simp)+
              hence "0 < t \<and> t < 1" using \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close> by (by100 linarith)
              thus "x \<in> hA ` ({t. 0 < t \<and> t < 1} - {1/2})"
                using ht(2) \<open>t \<noteq> 1/2\<close> by (by100 blast)
            next
              fix x assume "x \<in> hA ` ({t. 0 < t \<and> t < 1} - {1/2})"
              then obtain t where ht: "0 < t" "t < 1" "t \<noteq> 1/2" "x = hA t" by (by100 blast)
              have "t \<in> top1_unit_interval"
                unfolding top1_unit_interval_def using ht(1,2) by (by100 simp)
              hence "x \<in> A1" using himg ht(4) by (by100 blast)
              have h0_I: "(0::real) \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 simp)
              have h1_I: "(1::real) \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 simp)
              have h12_I: "(1/2::real) \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 simp)
              have "x \<noteq> hA 0" using ht(1,4) hinj \<open>t \<in> _\<close> h0_I
                unfolding inj_on_def by (by100 blast)
              have "x \<noteq> hA 1" using ht(2,4) hinj \<open>t \<in> _\<close> h1_I
                unfolding inj_on_def by (by100 blast)
              have "x \<noteq> hA (1/2)" using ht(3,4) hinj \<open>t \<in> _\<close> h12_I
                unfolding inj_on_def by (by100 blast)
              thus "x \<in> A1 - {hA 0, hA 1, hA (1/2)}"
                using \<open>x \<in> A1\<close> \<open>x \<noteq> hA 0\<close> \<open>x \<noteq> hA 1\<close> by (by100 blast)
            qed
            moreover have "{t::real. 0 < t \<and> t < 1} - {1/2} =
                {t. 0 < t \<and> t < 1/2} \<union> {t. 1/2 < t \<and> t < 1}" by (by100 auto)
            moreover have "hA ` ({t. 0 < t \<and> t < 1/2} \<union> {t. 1/2 < t \<and> t < 1}) =
                hA ` {t. 0 < t \<and> t < 1/2} \<union> hA ` {t. 1/2 < t \<and> t < 1}"
              by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          have hAB_disj: "?A_comp \<inter> ?B_comp = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain x where "x \<in> ?A_comp" "x \<in> ?B_comp" by (by100 blast)
            then obtain s t where hs: "0 < s" "s < 1/2" "x = hA s"
                and ht: "1/2 < t" "t < 1" "x = hA t" by (by100 blast)
            have "hA s = hA t" using hs(3) ht(3) by (by100 simp)
            have "s \<in> top1_unit_interval" using hs(1,2) unfolding top1_unit_interval_def by (by100 simp)
            have "t \<in> top1_unit_interval" using ht(1,2) unfolding top1_unit_interval_def by (by100 simp)
            have hinj: "inj_on hA top1_unit_interval"
              using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            have "s = t" using inj_onD[OF hinj \<open>hA s = hA t\<close> \<open>s \<in> _\<close> \<open>t \<in> _\<close>] .
            thus False using hs(2) ht(1) by (by100 linarith)
          qed
          have hA_open_loc: "openin_on X TX ?A_comp" sorry
          have hB_open_loc: "openin_on X TX ?B_comp" sorry
          have hA_pc_loc: "top1_path_connected_on ?A_comp (subspace_topology X TX ?A_comp)"
          proof -
            let ?I_A = "{t::real. 0 < t \<and> t < 1/2}"
            let ?TI_A = "subspace_topology (UNIV::real set) top1_open_sets ?I_A"
            have hI_A_ne: "?I_A \<noteq> {}"
            proof - have "(1/4::real) \<in> ?I_A" by (by100 simp) thus ?thesis by (by100 blast) qed
            have hI_A_conv: "\<And>x y t. x \<in> ?I_A \<Longrightarrow> y \<in> ?I_A \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1
                \<Longrightarrow> (1 - t) * x + t * y \<in> ?I_A"
            proof -
              fix x y t :: real
              assume hx: "x \<in> ?I_A" and hy: "y \<in> ?I_A" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
              have "0 < x" "x < 1/2" "0 < y" "y < 1/2" using hx hy by (by100 simp)+
              have h1t: "1 - t \<ge> 0" using ht1 by (by100 linarith)
              have "(1 - t) * x \<ge> 0" using h1t \<open>0 < x\<close> by (by100 simp)
              have "t * y \<ge> 0" using ht0 \<open>0 < y\<close> by (by100 simp)
              have "t * y > 0 \<or> (1 - t) * x > 0"
              proof (cases "t = 0")
                case True thus ?thesis using h1t \<open>0 < x\<close> by (by100 simp)
              next
                case False hence "t > 0" using ht0 by (by100 linarith)
                thus ?thesis using \<open>0 < y\<close> by (by100 simp)
              qed
              hence "(1 - t) * x + t * y > 0"
                using \<open>(1-t)*x \<ge> 0\<close> \<open>t*y \<ge> 0\<close> by (by100 linarith)
              moreover have "(1 - t) * x \<le> (1 - t) * (1/2)"
                using mult_left_mono[OF less_imp_le[OF \<open>x < 1/2\<close>] h1t] by (by100 simp)
              moreover have "t * y \<le> t * (1/2)"
                using mult_left_mono[OF less_imp_le[OF \<open>y < 1/2\<close>] ht0] by (by100 simp)
              ultimately have "(1 - t) * x + t * y \<le> (1-t)*(1/2) + t*(1/2)"
                by (by100 linarith)
              have "(1-t)*(1/2) + t*(1/2) = (1/2::real)"
                using distrib_right[of "1-t" t "1/2::real"] by (by100 simp)
              hence "(1 - t) * x + t * y \<le> 1/2"
                using \<open>(1-t)*x + t*y \<le> (1-t)*(1/2) + t*(1/2)\<close> by (by100 linarith)
              moreover have "(1 - t) * x + t * y \<noteq> 1/2"
              proof
                assume heq: "(1 - t) * x + t * y = 1/2"
                have "(1-t)*(1/2) + t*(1/2) = (1/2::real)"
                  using distrib_right[of "1-t" t "1/2::real"] by (by100 simp)
                hence "(1-t)*x + t*y = (1-t)*(1/2) + t*(1/2)" using heq by (by100 linarith)
                hence "(1-t)*(1/2) - (1-t)*x = t*y - t*(1/2)" by (by100 linarith)
                have hge: "(1-t)*(1/2) - (1-t)*x \<ge> 0"
                  using \<open>(1-t)*x \<le> (1-t)*(1/2)\<close> by (by100 linarith)
                have hle: "t*y - t*(1/2) \<le> 0" using \<open>t*y \<le> t*(1/2)\<close> by (by100 linarith)
                hence "(1-t)*(1/2) - (1-t)*x = 0" "t*y - t*(1/2) = 0"
                  using \<open>(1-t)*(1/2) - (1-t)*x = t*y - t*(1/2)\<close> hge hle by (by100 linarith)+
                hence "(1-t)*x = (1-t)*(1/2)" "t*y = t*(1/2)" by (by100 linarith)+
                show False
                proof (cases "t < 1")
                  case True hence "1 - t > 0" by (by100 linarith)
                  hence "x = 1/2"
                    using \<open>(1-t)*x = (1-t)*(1/2)\<close> by (by100 simp)
                  thus False using \<open>x < 1/2\<close> by (by100 linarith)
                next
                  case False hence "t = 1" using ht1 by (by100 linarith)
                  hence "1 * y = 1 * (1/2)" using \<open>t*y = t*(1/2)\<close> by (by100 simp)
                  hence "y = 1/2" by (by100 simp)
                  thus False using \<open>y < 1/2\<close> by (by100 linarith)
                qed
              qed
              ultimately have "(1 - t) * x + t * y < 1/2" by (by100 linarith)
              thus "(1 - t) * x + t * y \<in> ?I_A" using \<open>(1 - t) * x + t * y > 0\<close> by (by100 simp)
            qed
            from convex_real_subspace_path_connected[OF hI_A_ne hI_A_conv]
            have hI_A_pc: "top1_path_connected_on ?I_A ?TI_A" by (by100 simp)
            have hI_A_sub: "?I_A \<subseteq> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 auto)
            have hhA_cont_A1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                A1 (subspace_topology X TX A1) hA"
              using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
            have hhA_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX hA"
            proof -
              from top1_continuous_map_on_codomain_enlarge[OF hhA_cont_A1 hA1_sub subset_refl]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X (subspace_topology X TX X) hA" .
              moreover have "\<forall>U\<in>TX. U \<subseteq> X"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              hence "subspace_topology X TX X = TX" by (rule subspace_topology_self)
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>Restrict hA to ?I\\_A \\<subseteq> [0,1].\<close>
            have "?I_A \<subseteq> top1_unit_interval" using hI_A_sub .
            have hI_A_sub_R: "?I_A \<subseteq> (UNIV::real set)" by (by100 blast)
            have hI_top_eq: "subspace_topology top1_unit_interval top1_unit_interval_topology ?I_A = ?TI_A"
            proof -
              have "subspace_topology top1_unit_interval
                  (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval) ?I_A
                  = subspace_topology (UNIV::real set) top1_open_sets ?I_A"
                by (rule subspace_topology_trans[OF hI_A_sub])
              moreover have "top1_unit_interval_topology =
                  subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval"
                unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            have hhA_rest: "top1_continuous_map_on ?I_A ?TI_A X TX hA"
            proof -
              from top1_continuous_map_on_restrict_domain_simple[OF hhA_cont hI_A_sub]
              have "top1_continuous_map_on ?I_A (subspace_topology top1_unit_interval top1_unit_interval_topology ?I_A) X TX hA" .
              thus ?thesis using hI_top_eq by (by100 simp)
            qed
            have himg: "hA ` ?I_A = ?A_comp" by (by100 blast)
            have hA_sub_X: "?A_comp \<subseteq> X"
            proof -
              have "hA ` ?I_A \<subseteq> hA ` top1_unit_interval" using hI_A_sub by (by100 blast)
              have himg_full: "hA ` top1_unit_interval = A1"
                using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              have "hA ` ?I_A \<subseteq> A1" using \<open>hA ` ?I_A \<subseteq> hA ` top1_unit_interval\<close> himg_full by (by100 blast)
              thus ?thesis using hA1_sub by (by100 blast)
            qed
            have hTX_loc: "is_topology_on X TX"
              using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
            have "\<forall>x\<in>?I_A. hA x \<in> X"
            proof (intro ballI)
              fix x assume "x \<in> ?I_A"
              hence "x \<in> top1_unit_interval" using hI_A_sub by (by100 blast)
              thus "hA x \<in> X" using hhA_cont unfolding top1_continuous_map_on_def by (by100 blast)
            qed
            show ?thesis
              using top1_path_connected_continuous_image[OF hI_A_pc hhA_rest]
                \<open>\<forall>x\<in>?I_A. hA x \<in> X\<close> himg hA_sub_X hTX_loc by (by100 blast)
          qed
          have hB_pc_loc: "top1_path_connected_on ?B_comp (subspace_topology X TX ?B_comp)"
          proof -
            let ?I_B = "{t::real. 1/2 < t \<and> t < 1}"
            let ?TI_B = "subspace_topology (UNIV::real set) top1_open_sets ?I_B"
            have hI_B_ne: "?I_B \<noteq> {}"
              proof - have "(3/4::real) \<in> ?I_B" by (by100 simp) thus ?thesis by (by100 blast) qed
            have hI_B_conv: "\<And>x y t. x \<in> ?I_B \<Longrightarrow> y \<in> ?I_B \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1
                \<Longrightarrow> (1 - t) * x + t * y \<in> ?I_B"
            proof -
              fix x y t :: real
              assume hx: "x \<in> ?I_B" and hy: "y \<in> ?I_B" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
              have "1/2 < x" "x < 1" "1/2 < y" "y < 1" using hx hy by (by100 simp)+
              have h1t: "1 - t \<ge> 0" using ht1 by (by100 linarith)
              \<comment> \<open>Lower bound: (1-t)*x + t*y > 1/2.\<close>
              have "(1 - t) * x \<ge> (1 - t) * (1/2)"
                using mult_left_mono[OF less_imp_le[OF \<open>1/2 < x\<close>] h1t] by (by100 simp)
              have "t * y \<ge> t * (1/2)"
                using mult_left_mono[OF less_imp_le[OF \<open>1/2 < y\<close>] ht0] by (by100 simp)
              have "(1 - t) * x + t * y \<ge> (1-t)*(1/2) + t*(1/2)"
                using \<open>(1-t)*x \<ge> (1-t)*(1/2)\<close> \<open>t*y \<ge> t*(1/2)\<close> by (by100 linarith)
              have "(1-t)*(1/2) + t*(1/2) = (1/2::real)"
                using distrib_right[of "1-t" t "1/2::real"] by (by100 simp)
              hence h_lb_le: "(1 - t) * x + t * y \<ge> 1/2"
                using \<open>(1-t)*x + t*y \<ge> (1-t)*(1/2) + t*(1/2)\<close> by (by100 linarith)
              have "(1 - t) * x + t * y \<noteq> 1/2"
              proof
                assume "(1 - t) * x + t * y = 1/2"
                hence "(1-t)*x + t*y = (1-t)*(1/2) + t*(1/2)"
                  using \<open>(1-t)*(1/2) + t*(1/2) = 1/2\<close> by (by100 linarith)
                hence "(1-t)*(1/2) - (1-t)*x = t*y - t*(1/2)" by (by100 linarith)
                have hge_d: "(1-t)*(1/2) - (1-t)*x \<le> 0"
                  using \<open>(1-t)*x \<ge> (1-t)*(1/2)\<close> by (by100 linarith)
                have hle_d: "t*y - t*(1/2) \<ge> 0" using \<open>t*y \<ge> t*(1/2)\<close> by (by100 linarith)
                hence "(1-t)*x = (1-t)*(1/2)" "t*y = t*(1/2)"
                  using \<open>(1-t)*(1/2) - (1-t)*x = t*y - t*(1/2)\<close> hge_d hle_d by (by100 linarith)+
                show False
                proof (cases "t = 0")
                  case True hence "x = 1/2" using \<open>(1-t)*x = (1-t)*(1/2)\<close> by (by100 simp)
                  thus False using \<open>1/2 < x\<close> by (by100 linarith)
                next
                  case False hence "t > 0" using ht0 by (by100 linarith)
                  hence "y = 1/2" using \<open>t*y = t*(1/2)\<close> by (by100 simp)
                  thus False using \<open>1/2 < y\<close> by (by100 linarith)
                qed
              qed
              hence h_lb: "(1 - t) * x + t * y > 1/2" using h_lb_le by (by100 linarith)
              \<comment> \<open>Upper bound: (1-t)*x + t*y < 1.\<close>
              have "(1 - t) * x \<le> (1 - t) * 1"
                using mult_left_mono[OF less_imp_le[OF \<open>x < 1\<close>] h1t] by (by100 simp)
              hence "(1 - t) * x \<le> 1 - t" by (by100 simp)
              have "t * y \<le> t * 1" using mult_left_mono[OF less_imp_le[OF \<open>y < 1\<close>] ht0] by (by100 simp)
              hence "t * y \<le> t" by (by100 simp)
              have "(1 - t) * x + t * y \<le> (1 - t) + t" using \<open>(1-t)*x \<le> 1-t\<close> \<open>t*y \<le> t\<close> by (by100 linarith)
              hence h_ub_le: "(1 - t) * x + t * y \<le> 1" by (by100 linarith)
              have "(1 - t) * x + t * y \<noteq> 1"
              proof
                assume "(1 - t) * x + t * y = 1"
                hence "(1-t)*x = 1 - t" "t*y = t"
                  using \<open>(1-t)*x \<le> 1-t\<close> \<open>t*y \<le> t\<close> by (by100 linarith)+
                show False
                proof (cases "t < 1")
                  case True hence "1 - t > 0" by (by100 linarith)
                  hence "x = 1" using \<open>(1-t)*x = 1-t\<close> by (by100 simp)
                  thus False using \<open>x < 1\<close> by (by100 linarith)
                next
                  case False hence "t = 1" using ht1 by (by100 linarith)
                  hence "y = 1" using \<open>t*y = t\<close> by (by100 simp)
                  thus False using \<open>y < 1\<close> by (by100 linarith)
                qed
              qed
              hence h_ub: "(1 - t) * x + t * y < 1" using h_ub_le by (by100 linarith)
              show "(1 - t) * x + t * y \<in> ?I_B" using h_lb h_ub by (by100 simp)
            qed
            from convex_real_subspace_path_connected[OF hI_B_ne hI_B_conv]
            have hI_B_pc: "top1_path_connected_on ?I_B ?TI_B" by (by100 simp)
            have hI_B_sub: "?I_B \<subseteq> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 auto)
            have hI_B_top_eq: "subspace_topology top1_unit_interval top1_unit_interval_topology ?I_B = ?TI_B"
            proof -
              have "subspace_topology top1_unit_interval
                  (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval) ?I_B
                  = subspace_topology (UNIV::real set) top1_open_sets ?I_B"
                by (rule subspace_topology_trans[OF hI_B_sub])
              moreover have "top1_unit_interval_topology =
                  subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval"
                unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            have hhA_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX hA"
            proof -
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  A1 (subspace_topology X TX A1) hA"
                using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
              from top1_continuous_map_on_codomain_enlarge[OF this hA1_sub subset_refl]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X (subspace_topology X TX X) hA" .
              moreover have "\<forall>U\<in>TX. U \<subseteq> X"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              hence "subspace_topology X TX X = TX" by (rule subspace_topology_self)
              ultimately show ?thesis by (by100 simp)
            qed
            from top1_continuous_map_on_restrict_domain_simple[OF hhA_cont_X hI_B_sub]
            have hhA_rest_B: "top1_continuous_map_on ?I_B ?TI_B X TX hA"
              using hI_B_top_eq by (by100 simp)
            have himg_B: "hA ` ?I_B = ?B_comp" by (by100 blast)
            have hB_sub_X: "?B_comp \<subseteq> X"
            proof -
              have "hA ` ?I_B \<subseteq> hA ` top1_unit_interval" using hI_B_sub by (by100 blast)
              have "hA ` top1_unit_interval = A1"
                using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              have "hA ` ?I_B \<subseteq> A1" using \<open>hA ` ?I_B \<subseteq> hA ` top1_unit_interval\<close> \<open>_ = A1\<close> by (by100 blast)
              thus ?thesis using hA1_sub by (by100 blast)
            qed
            have "\<forall>x\<in>?I_B. hA x \<in> X"
              using hhA_cont_X unfolding top1_continuous_map_on_def
              using hI_B_sub by (by100 blast)
            show ?thesis
              using top1_path_connected_continuous_image[OF hI_B_pc hhA_rest_B]
                \<open>\<forall>x\<in>?I_B. hA x \<in> X\<close> himg_B hB_sub_X
            proof -
              have "is_topology_on X TX"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              thus ?thesis using top1_path_connected_continuous_image[OF hI_B_pc hhA_rest_B]
                \<open>\<forall>x\<in>?I_B. hA x \<in> X\<close> himg_B hB_sub_X by (by100 blast)
            qed
          qed
          have ha_A: "?pt_a \<in> ?A_comp"
          proof - have "(1/4::real) \<in> {t. 0 < t \<and> t < 1/2}" by (by100 simp) thus ?thesis by (by100 blast) qed
          have hb_B: "?pt_b \<in> ?B_comp"
          proof - have "(3/4::real) \<in> {t. 1/2 < t \<and> t < 1}" by (by100 simp) thus ?thesis by (by100 blast) qed
          \<comment> \<open>V deformation retracts onto T (for path-connectedness and simple connectedness).\<close>
          define ps_bc where "ps_bc A = (if A = A1 then hA (1/2) else undefined)" for A
          \<comment> \<open>ps\\_bc gives interior points for hdr\\_helper (shared between DR and SC proofs).\<close>
          have hps_bc_shared: "\<forall>A\<in>{A1}. ps_bc A \<in> A \<and>
              ps_bc A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
          proof (intro ballI conjI)
            fix A assume "A \<in> {A1}" hence "A = A1" by (by100 blast)
            have h12_I: "(1/2::real) \<in> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 simp)
            have hbij: "bij_betw hA top1_unit_interval A1"
              using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
            have "hA (1/2) \<in> A1" using hbij h12_I unfolding bij_betw_def by (by100 blast)
            show "ps_bc A \<in> A" using \<open>A = A1\<close> \<open>hA (1/2) \<in> A1\<close> unfolding ps_bc_def by (by100 simp)
            have hep: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {hA 0, hA 1}"
            proof -
              have "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              show ?thesis by (rule arc_endpoints_are_boundary[OF hX_strict \<open>is_hausdorff_on X TX\<close> hA1_sub hA1_arc hhA])
            qed
            have hinj: "inj_on hA top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "hA (1/2) \<noteq> hA 0"
            proof assume "hA (1/2) = hA 0"
              hence "(1/2::real) = 0" using hinj h12_I h0_I unfolding inj_on_def by (by100 blast)
              thus False by (by100 simp)
            qed
            moreover have "hA (1/2) \<noteq> hA 1"
            proof assume "hA (1/2) = hA 1"
              hence "(1/2::real) = 1" using hinj h12_I h1_I unfolding inj_on_def by (by100 blast)
              thus False by (by100 simp)
            qed
            ultimately have "hA (1/2) \<notin> {hA 0, hA 1}" by (by100 blast)
            hence "hA (1/2) \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
              using hep by (by100 simp)
            thus "ps_bc A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A = A1\<close> unfolding ps_bc_def by (by100 simp)
          qed
          have hV_dr_T_early: "top1_deformation_retract_of_on ?V (subspace_topology X TX ?V) T"
          proof -
            have "{A1} \<subseteq> ?NT" using hA1 by (by100 blast)
            from hdr_helper[OF _ \<open>{A1} \<subseteq> ?NT\<close> hps_bc_shared]
            have "top1_deformation_retract_of_on (X - ps_bc ` {A1})
                (subspace_topology X TX (X - ps_bc ` {A1})) (T \<union> \<Union>(?NT - {A1}))"
              by (by100 simp)
            have "?NT - {A1} = {}" using hNT_singleton by (by100 blast)
            hence "T \<union> \<Union>(?NT - {A1}) = T" by (by100 blast)
            have "ps_bc ` {A1} = {hA (1/2)}" unfolding ps_bc_def by (by100 simp)
            hence "X - ps_bc ` {A1} = ?V" by (by100 simp)
            thus ?thesis using \<open>top1_deformation_retract_of_on (X - ps_bc ` {A1}) _ _\<close>
                \<open>T \<union> \<Union>(?NT - {A1}) = T\<close> by (by100 simp)
          qed
          have hV_top_early: "is_topology_on ?V (subspace_topology X TX ?V)"
          proof -
            have hTX_t: "is_topology_on X TX"
              using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
            have "?V \<subseteq> X" by (by100 blast)
            from subspace_topology_is_topology_on[OF hTX_t \<open>?V \<subseteq> X\<close>] show ?thesis .
          qed
          have hT_pc_early: "top1_path_connected_on T (subspace_topology ?V (subspace_topology X TX ?V) T)"
          proof -
            have "T \<subseteq> ?V"
              using conjunct1[OF hV_dr_T_early[unfolded top1_deformation_retract_of_on_def]]
              by (by100 blast)
            have "subspace_topology ?V (subspace_topology X TX ?V) T = subspace_topology X TX T"
              by (rule subspace_topology_trans[OF \<open>T \<subseteq> ?V\<close>])
            have "top1_path_connected_on T (subspace_topology X TX T)"
              using tree_simply_connected[OF hT_tree] top1_simply_connected_on_path_connected by (by100 blast)
            thus ?thesis using \<open>subspace_topology ?V _ T = _\<close> by (by100 simp)
          qed
          have hV_pc_early: "top1_path_connected_on ?V (subspace_topology X TX ?V)"
            by (rule deformation_retract_path_connected[OF hV_dr_T_early hV_top_early hT_pc_early])
          \<comment> \<open>Paths \\<alpha> (in U from a to b) and \\<beta> (in V from b to a).\<close>
          have halpha_loc: "\<exists>\<alpha>. top1_is_path_on ?U (subspace_topology X TX ?U) ?pt_a ?pt_b \<alpha>" sorry
          have hbeta_loc: "\<exists>\<beta>. top1_is_path_on ?V (subspace_topology X TX ?V) ?pt_b ?pt_a \<beta>"
          proof -
            \<comment> \<open>Both pt\\_a and pt\\_b are in V (they're in A1 but \\<noteq> hA(1/2)).\<close>
            have hpta_V: "?pt_a \<in> ?V"
            proof -
              have hinj: "inj_on hA top1_unit_interval"
                using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              have "(1/4::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "(1/4::real) \<noteq> 1/2" by (by100 simp)
              hence "hA (1/4) \<noteq> hA (1/2)"
                using hinj \<open>(1/4::real) \<in> _\<close> \<open>(1/2::real) \<in> _\<close> unfolding inj_on_def by (by100 blast)
              have "hA (1/4) \<in> A1"
                using hhA \<open>(1/4::real) \<in> _\<close>
                unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis using \<open>hA (1/4) \<noteq> hA (1/2)\<close> hA1_sub by (by100 blast)
            qed
            have hptb_V: "?pt_b \<in> ?V"
            proof -
              have hinj: "inj_on hA top1_unit_interval"
                using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              have "(3/4::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "(1/2::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "(3/4::real) \<noteq> 1/2" by (by100 simp)
              hence "hA (3/4) \<noteq> hA (1/2)"
                using hinj \<open>(3/4::real) \<in> _\<close> \<open>(1/2::real) \<in> _\<close> unfolding inj_on_def by (by100 blast)
              have "hA (3/4) \<in> A1"
                using hhA \<open>(3/4::real) \<in> top1_unit_interval\<close>
                unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis using \<open>hA (3/4) \<noteq> hA (1/2)\<close> hA1_sub by (by100 blast)
            qed
            \<comment> \<open>V is path-connected (already proved above as hV\\_pc\\_bc inside V SC).\<close>
            have hV_pc_here: "top1_path_connected_on ?V (subspace_topology X TX ?V)"
              using hV_pc_early .
            from hV_pc_here hptb_V hpta_V
            show ?thesis unfolding top1_path_connected_on_def by (by100 blast)
          qed
          \<comment> \<open>U and V simply connected.\<close>
          have hU_sc_loc: "top1_simply_connected_on ?U (subspace_topology X TX ?U)" sorry
          have hV_sc_loc: "top1_simply_connected_on ?V (subspace_topology X TX ?V)"
          proof -
            \<comment> \<open>Use shared hV\\_dr\\_T\\_early. T is SC. V DR onto T \\<Rightarrow> V SC.\<close>
            have hT_sc: "top1_simply_connected_on T (subspace_topology X TX T)"
              using hT_tree unfolding top1_is_tree_on_def by (by100 blast)
            have hV_top_bc: "is_topology_on ?V (subspace_topology X TX ?V)"
            proof -
              have "?V \<subseteq> X" by (by100 blast)
              have hTX_t: "is_topology_on X TX"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              thus ?thesis using subspace_topology_is_topology_on[OF hTX_t] \<open>?V \<subseteq> X\<close> by (by100 blast)
            qed
            have hT_pc_V: "top1_path_connected_on T (subspace_topology ?V (subspace_topology X TX ?V) T)"
            proof -
              have "T \<subseteq> ?V"
                using conjunct1[OF hV_dr_T_early[unfolded top1_deformation_retract_of_on_def]]
                by (by100 blast)
              have "subspace_topology ?V (subspace_topology X TX ?V) T = subspace_topology X TX T"
                by (rule subspace_topology_trans[OF \<open>T \<subseteq> ?V\<close>])
              thus ?thesis using hT_pc_early by (by100 simp)
            qed
            have hV_pc_bc: "top1_path_connected_on ?V (subspace_topology X TX ?V)"
              by (rule deformation_retract_path_connected[OF hV_dr_T_early hV_top_bc hT_pc_V])
            \<comment> \<open>All loops in V are null-homotopic (\\<pi>\\_1(V) \\<cong> \\<pi>\\_1(T) = trivial).\<close>
            \<comment> \<open>Use Theorem\\_58\\_3: \\<pi>\\_1(T) \\<cong> \\<pi>\\_1(V). T SC \\<Rightarrow> \\<pi>\\_1(T) trivial.
               Hence \\<pi>\\_1(V) trivial at x0. V PC + trivial \\<pi>\\_1 at x0 \\<Rightarrow> V SC.\<close>
            have hx0_V_bc: "x0 \<in> ?V"
            proof -
              have "x0 \<in> T" using hx0_T .
              have "T \<subseteq> ?V" using conjunct1[OF hV_dr_T_early[unfolded top1_deformation_retract_of_on_def]]
                by (by100 blast)
              thus ?thesis using \<open>x0 \<in> T\<close> by (by100 blast)
            qed
            have hx0_T_bc: "x0 \<in> T" using hx0_T .
            \<comment> \<open>Theorem\\_58\\_3: \\<pi>\\_1(T, sub(V,...,T), x0) \\<cong> \\<pi>\\_1(V, sub(X,TX,V), x0).\<close>
            from Theorem_58_3[OF hV_dr_T_early hV_top_bc hx0_T_bc]
            have hiso_TV: "top1_groups_isomorphic_on
                (top1_fundamental_group_carrier T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)
                (top1_fundamental_group_mul T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)
                (top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0)
                (top1_fundamental_group_mul ?V (subspace_topology X TX ?V) x0)" .
            \<comment> \<open>T SC at x0 \\<Rightarrow> \\<pi>\\_1(T, sub(V,...,T), x0) = {id}.\<close>
            have hT_triv: "top1_fundamental_group_carrier T
                (subspace_topology ?V (subspace_topology X TX ?V) T) x0 =
                {top1_fundamental_group_id T (subspace_topology ?V (subspace_topology X TX ?V) T) x0}"
            proof -
              have "T \<subseteq> ?V" using conjunct1[OF hV_dr_T_early[unfolded top1_deformation_retract_of_on_def]]
                by (by100 blast)
              have hTT: "subspace_topology ?V (subspace_topology X TX ?V) T = subspace_topology X TX T"
                by (rule subspace_topology_trans[OF \<open>T \<subseteq> ?V\<close>])
              have "top1_simply_connected_on T (subspace_topology ?V (subspace_topology X TX ?V) T)"
                using hT_sc hTT by (by100 simp)
              from simply_connected_trivial_carrier[OF this hx0_T_bc]
              show ?thesis .
            qed
            \<comment> \<open>iso maps trivial to trivial \\<Rightarrow> \\<pi>\\_1(V, x0) = {id\\_V}.\<close>
            have hV_triv: "top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0 =
                {top1_fundamental_group_id ?V (subspace_topology X TX ?V) x0}"
            proof -
              \<comment> \<open>Extract iso function from hiso\\_TV.\<close>
              from hiso_TV obtain \<phi> where h\<phi>: "top1_group_iso_on
                  (top1_fundamental_group_carrier T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)
                  (top1_fundamental_group_mul T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)
                  (top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0)
                  (top1_fundamental_group_mul ?V (subspace_topology X TX ?V) x0) \<phi>"
                unfolding top1_groups_isomorphic_on_def by (by100 blast)
              \<comment> \<open>\\<phi> is a bijection from {id\\_T} to \\<pi>\\_1(V).\<close>
              have hbij: "bij_betw \<phi>
                  (top1_fundamental_group_carrier T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)
                  (top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0)"
                using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
              have "top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0 =
                  \<phi> ` (top1_fundamental_group_carrier T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)"
                using hbij unfolding bij_betw_def by (by100 blast)
              hence "top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0 =
                  \<phi> ` {top1_fundamental_group_id T (subspace_topology ?V (subspace_topology X TX ?V) T) x0}"
                using hT_triv by (by100 simp)
              hence hV_singleton: "top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0 =
                  {\<phi> (top1_fundamental_group_id T (subspace_topology ?V (subspace_topology X TX ?V) T) x0)}"
                by (by100 simp)
              \<comment> \<open>\\<phi>(id\\_T) = id\\_V (group homomorphisms map identity to identity).\<close>
              have "\<phi> (top1_fundamental_group_id T (subspace_topology ?V (subspace_topology X TX ?V) T) x0) =
                  top1_fundamental_group_id ?V (subspace_topology X TX ?V) x0"
              proof -
                let ?TT_V = "subspace_topology ?V (subspace_topology X TX ?V) T"
                have h\<phi>_hom: "top1_group_hom_on
                    (top1_fundamental_group_carrier T ?TT_V x0)
                    (top1_fundamental_group_mul T ?TT_V x0)
                    (top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0)
                    (top1_fundamental_group_mul ?V (subspace_topology X TX ?V) x0) \<phi>"
                  using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
                have hgrp_T: "top1_is_group_on
                    (top1_fundamental_group_carrier T ?TT_V x0)
                    (top1_fundamental_group_mul T ?TT_V x0)
                    (top1_fundamental_group_id T ?TT_V x0)
                    (top1_fundamental_group_invg T ?TT_V x0)"
                proof -
                  have "T \<subseteq> ?V" using conjunct1[OF hV_dr_T_early[unfolded top1_deformation_retract_of_on_def]]
                    by (by100 blast)
                  have hTT_eq: "?TT_V = subspace_topology X TX T"
                    by (rule subspace_topology_trans[OF \<open>T \<subseteq> ?V\<close>])
                  have hTX_bc2: "is_topology_on X TX"
                    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
                  have "is_topology_on T ?TT_V"
                    using hTT_eq subspace_topology_is_topology_on[OF hTX_bc2 hT_sub]
                    by (by100 simp)
                  from top1_fundamental_group_is_group[OF this hx0_T_bc] show ?thesis .
                qed
                have hgrp_V: "top1_is_group_on
                    (top1_fundamental_group_carrier ?V (subspace_topology X TX ?V) x0)
                    (top1_fundamental_group_mul ?V (subspace_topology X TX ?V) x0)
                    (top1_fundamental_group_id ?V (subspace_topology X TX ?V) x0)
                    (top1_fundamental_group_invg ?V (subspace_topology X TX ?V) x0)"
                  by (rule top1_fundamental_group_is_group[OF hV_top_bc hx0_V_bc])
                from hom_preserves_id[OF hgrp_T hgrp_V h\<phi>_hom]
                show ?thesis .
              qed
              thus ?thesis using hV_singleton by (by100 simp)
            qed
            \<comment> \<open>\\<pi>\\_1(V) trivial + V PC \\<Rightarrow> V SC.
               Uses top1\\_simply\\_connected\\_from\\_one\\_point + hV\\_triv.\<close>
            show ?thesis
              by (rule trivial_pi1_imp_simply_connected[OF hV_top_bc hV_pc_early hx0_V_bc hV_triv])
          qed
          \<comment> \<open>Apply Lemma 84.6.\<close>
          from halpha_loc hbeta_loc obtain \<alpha> \<beta> where
            h\<alpha>: "top1_is_path_on ?U (subspace_topology X TX ?U) ?pt_a ?pt_b \<alpha>" and
            h\<beta>: "top1_is_path_on ?V (subspace_topology X TX ?V) ?pt_b ?pt_a \<beta>"
            by (by100 blast)
          from Lemma_84_6_two_component_generation[OF hX_strict hU_open_loc hV_open_loc hcover_loc
              hUV_split hAB_disj hA_open_loc hB_open_loc hA_pc_loc hB_pc_loc
              ha_A hb_B h\<alpha> h\<beta> hU_sc_loc hV_sc_loc]
          have hpi1_a_Z: "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier X TX ?pt_a) (top1_fundamental_group_mul X TX ?pt_a)
              top1_Z_group top1_Z_mul" .
          \<comment> \<open>Transfer from basepoint hA(1/4) to x0.\<close>
          have ha_X: "?pt_a \<in> X"
          proof -
            have "(1/4::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            hence "hA (1/4) \<in> A1"
              using hhA unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            thus ?thesis using hA1_sub by (by100 blast)
          qed
          \<comment> \<open>X is path-connected (tree \\<union> one arc, proved above).\<close>
          have hX_pc: "top1_path_connected_on X TX"
          proof -
            have "top1_path_connected_on (T \<union> A1) (subspace_topology X TX (T \<union> A1))"
            proof -
              have "\<forall>A\<in>{A1}. top1_is_arc_on A (subspace_topology X TX A) \<and> A \<subseteq> X"
                using hA1_arc hA1_sub by (by100 blast)
              have "\<forall>A\<in>{A1}. \<exists>e. e \<in> T \<and> e \<in> A"
              proof -
                have "A1 \<in> ?NT" using hA1 by (by100 blast)
                obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology A1 (subspace_topology X TX A1) h'"
                  using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
                have "is_hausdorff_on X TX"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                from arc_endpoints_are_boundary[OF hX_strict
                    \<open>is_hausdorff_on X TX\<close> hA1_sub hA1_arc hh']
                have "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {h' 0, h' 1}" .
                have "h' 0 \<in> T"
                  using hNT_endpoints[rule_format, OF \<open>A1 \<in> ?NT\<close>] \<open>_ = {h' 0, h' 1}\<close> by (by100 simp)
                have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                have "h' 0 \<in> A1"
                  using hh' \<open>(0::real) \<in> top1_unit_interval\<close>
                  unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                thus ?thesis using \<open>h' 0 \<in> T\<close> \<open>h' 0 \<in> A1\<close> by (by100 blast)
              qed
              have hTX_t: "is_topology_on X TX"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              have "finite ({A1} :: 'a set set)" by (by100 simp)
              have hA1_arc_pc: "\<forall>A\<in>{A1}. top1_is_arc_on A (subspace_topology X TX A) \<and> A \<subseteq> X"
                using hA1_arc hA1_sub by (by100 blast)
              have hA1_endpt: "\<forall>A\<in>{A1}. \<exists>e. e \<in> T \<and> e \<in> A"
              proof -
                have "A1 \<in> ?NT" using hA1 by (by100 blast)
                have "is_hausdorff_on X TX"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology A1 (subspace_topology X TX A1) h'"
                  using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
                from arc_endpoints_are_boundary[OF hX_strict \<open>is_hausdorff_on X TX\<close> hA1_sub hA1_arc hh']
                have "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {h' 0, h' 1}" .
                have "h' 0 \<in> T"
                  using hNT_endpoints[rule_format, OF \<open>A1 \<in> ?NT\<close>]
                  \<open>top1_arc_endpoints_on A1 _ = {h' 0, h' 1}\<close> by (by100 simp)
                have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                have "h' 0 \<in> A1"
                  using hh' \<open>(0::real) \<in> top1_unit_interval\<close>
                  unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                thus ?thesis using \<open>h' 0 \<in> T\<close> by (by100 blast)
              qed
              from tree_union_arcs_path_connected[OF hTX_t hT_tree hT_sub
                  \<open>finite {A1}\<close> hA1_arc_pc hA1_endpt hx0_T]
              show ?thesis by (by100 simp)
            qed
            moreover have "T \<union> A1 = X" using hX_eq by (by100 blast)
            moreover have "subspace_topology X TX X = TX"
            proof -
              have "\<forall>U\<in>TX. U \<subseteq> X"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              thus ?thesis by (rule subspace_topology_self)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Path from a to x0 in X.\<close>
          have "\<exists>\<gamma>. top1_is_path_on X TX ?pt_a x0 \<gamma>"
            using hX_pc ha_X assms(3) unfolding top1_path_connected_on_def by (by100 blast)
          then obtain \<gamma> where h\<gamma>: "top1_is_path_on X TX ?pt_a x0 \<gamma>" by (by100 blast)
          have hTX_top_loc: "is_topology_on X TX"
            using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
          from basepoint_change_iso_via_path[OF hTX_top_loc h\<gamma>]
          have hbc: "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier X TX ?pt_a) (top1_fundamental_group_mul X TX ?pt_a)
              (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)" .
          \<comment> \<open>Reverse basepoint change: iso(\\<pi>\\_1(x0), \\<pi>\\_1(hA(1/4))).\<close>
          have hpi1_x0_grp: "top1_is_group_on
              (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
              (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
            by (rule top1_fundamental_group_is_group[OF hTX_top_loc assms(3)])
          have hpi1_a_grp: "top1_is_group_on
              (top1_fundamental_group_carrier X TX ?pt_a) (top1_fundamental_group_mul X TX ?pt_a)
              (top1_fundamental_group_id X TX ?pt_a) (top1_fundamental_group_invg X TX ?pt_a)"
            by (rule top1_fundamental_group_is_group[OF hTX_top_loc ha_X])
          from top1_groups_isomorphic_on_sym[OF hbc hpi1_a_grp hpi1_x0_grp]
          have "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
              (top1_fundamental_group_carrier X TX ?pt_a) (top1_fundamental_group_mul X TX ?pt_a)" .
          from groups_isomorphic_trans_fwd[OF this hpi1_a_Z]
          show ?thesis .
        qed
        \<comment> \<open>\\<Z> is free on 1 generator.\<close>
        have hZ_free: "top1_is_free_group_full_on top1_Z_group top1_Z_mul
            top1_Z_id top1_Z_invg (\<lambda>(_::nat). (1::int)) {0::nat}"
          by (rule Z_is_free_on_one_generator)
        \<comment> \<open>Compose: \\<pi>\\_1(X) \\<cong> \\<Z> and \\<Z> free \\<Rightarrow> \\<exists>G. free(G) \\<and> iso(G, \\<pi>\\_1(X)).\<close>
        \<comment> \<open>iso is symmetric: \\<pi>\\_1(X) \\<cong> \\<Z> \\<Rightarrow> \\<Z> \\<cong> \\<pi>\\_1(X).\<close>
        have hTX_top_bc: "is_topology_on X TX"
          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
        have hpi1_grp: "top1_is_group_on
            (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
            (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
          by (rule top1_fundamental_group_is_group[OF hTX_top_bc assms(3)])
        have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
          using hZ_free unfolding top1_is_free_group_full_on_def by (by100 blast)
        have hZ_iso_pi1: "top1_groups_isomorphic_on top1_Z_group top1_Z_mul
            (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)"
          by (rule top1_groups_isomorphic_on_sym[OF hpi1_iso_Z hpi1_grp hZ_grp])
        show ?thesis
          apply (rule exI[of _ top1_Z_group], rule exI[of _ top1_Z_mul],
                 rule exI[of _ top1_Z_id], rule exI[of _ top1_Z_invg],
                 rule exI[of _ "\<lambda>(_::nat). (1::int)"], rule exI[of _ "{0::nat}"])
          using hZ_free hZ_iso_pi1 by (by100 blast)
      next
        case hcard_ge2: False
        hence hcard_gt1: "card ?NT > 1"
        proof -
          have "card ?NT \<noteq> 0" using \<open>finite ?NT\<close> hNT_ne by (by100 auto)
          moreover have "card ?NT \<noteq> 1" using hcard_ge2 by (by100 blast)
          ultimately show ?thesis by (by100 linarith)
        qed
        \<comment> \<open>Induction step: card(NT) > 1. Split using SvK.
           Pick A1 \\<in> NT. Choose interior point p1 of A1.
           U = X - ps\\`(NT - {A1}), V = X - {p1}.
           U \\<cap> V = X - ps\\`NT is simply connected (SC lemma).
           U deformation retracts onto T \\<union> A1 (hdr with S = NT-{A1}).
           V deformation retracts onto T \\<union> \\<Union>(NT-{A1}) (hdr with S = {A1}).
           Apply IH to the DR targets (which are graphs with fewer non-tree arcs).\<close>
        \<comment> \<open>Choose interior points for each non-tree arc.\<close>
        have hint_pts: "\<forall>A\<in>?NT. \<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof (intro ballI)
          fix A assume "A \<in> ?NT"
          hence "A \<in> \<A>" by (by100 blast)
          have harc: "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h" using harc unfolding top1_is_arc_on_def by (by100 blast)
          have hbij: "bij_betw h top1_unit_interval A"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have hX_strict: "is_topology_on_strict X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          have hX_haus: "is_hausdorff_on X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close> harc hh]
          have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}" .
          have h12_I: "(1/2::real) \<in> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 simp)
          have "h (1/2) \<in> A" using hbij h12_I unfolding bij_betw_def by (by100 blast)
          moreover have "h (1/2) \<notin> {h 0, h 1}"
          proof -
            have hinj: "inj_on h top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "(1/2::real) \<noteq> 0" by (by100 simp)
            hence "h (1/2) \<noteq> h 0" using hinj h12_I h0_I unfolding inj_on_def by (by100 blast)
            have "(1/2::real) \<noteq> 1" by (by100 simp)
            hence "h (1/2) \<noteq> h 1" using hinj h12_I h1_I unfolding inj_on_def by (by100 blast)
            thus ?thesis using \<open>h (1/2) \<noteq> h 0\<close> by (by100 blast)
          qed
          ultimately show "\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hep by (by100 blast)
        qed
        have "\<exists>ps. \<forall>A\<in>?NT. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof -
          have "\<forall>A. A \<in> ?NT \<longrightarrow> (\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology X TX A))"
            using hint_pts by (by100 blast)
          hence "\<exists>f. \<forall>A. A \<in> ?NT \<longrightarrow> f A \<in> A \<and> f A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            by (rule choice_iff'[THEN iffD1])
          thus ?thesis by (by100 blast)
        qed
        then obtain ps where hps: "\<forall>A\<in>?NT. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
          by (by5000 blast)
        \<comment> \<open>Define U, V, and their intersection.\<close>
        let ?S_U = "?NT - {A1}" \<comment> \<open>arcs to remove from for U\<close>
        let ?S_V = "{A1}" \<comment> \<open>arcs to remove from for V\<close>
        let ?U = "X - ps ` ?S_U"
        let ?V = "X - ps ` ?S_V"
        let ?UV = "X - ps ` ?NT"
        \<comment> \<open>U \\<union> V = X, U \\<cap> V = X - ps\\`NT.\<close>
        have hUV_eq: "?U \<inter> ?V = ?UV"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> ?U \<inter> ?V"
          hence "x \<in> X" "x \<notin> ps ` (?NT - {A1})" "x \<notin> ps ` {A1}" by (by100 blast)+
          hence "x \<notin> ps ` ?NT"
          proof -
            have "?NT = (?NT - {A1}) \<union> {A1}" using hA1 by (by100 blast)
            hence "ps ` ?NT = ps ` (?NT - {A1}) \<union> ps ` {A1}"
              using image_Un[of ps "?NT - {A1}" "{A1}"] by (by100 simp)
            thus ?thesis using \<open>x \<notin> ps ` (?NT - {A1})\<close> \<open>x \<notin> ps ` {A1}\<close> by (by100 blast)
          qed
          thus "x \<in> ?UV" using \<open>x \<in> X\<close> by (by100 blast)
        next
          fix x assume "x \<in> ?UV"
          hence "x \<in> X" "x \<notin> ps ` ?NT" by (by100 blast)+
          have "x \<notin> ps ` (?NT - {A1})" using \<open>x \<notin> ps ` ?NT\<close> by (by100 blast)
          have "x \<notin> ps ` {A1}" using \<open>x \<notin> ps ` ?NT\<close> hA1 by (by100 blast)
          thus "x \<in> ?U \<inter> ?V" using \<open>x \<in> X\<close> \<open>x \<notin> ps ` (?NT - {A1})\<close> \<open>x \<notin> ps ` {A1}\<close>
            by (by100 blast)
        qed
        have hUV_cover: "?U \<union> ?V = X"
        proof -
          \<comment> \<open>Need: ps(A1) \\<notin> ps\\`(NT-{A1}), i.e. ps injective on NT.
             Interior points are distinct (in different arcs, arcs pairwise disjoint on interiors).\<close>
          have "ps ` (?NT - {A1}) \<inter> ps ` {A1} = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain B where "B \<in> ?NT - {A1}" "ps B = ps A1" by (by100 blast)
            have "B \<in> \<A>" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
            have "B \<noteq> A1" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
            have "A1 \<in> \<A>" using hA1 by (by100 blast)
            have "ps B \<in> B" using hps \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
            have "ps B \<notin> top1_arc_endpoints_on B (subspace_topology X TX B)"
              using hps \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
            have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
            have "ps B \<in> A1" using \<open>ps B = ps A1\<close> \<open>ps A1 \<in> A1\<close> by (by100 simp)
            have "ps B \<in> B \<inter> A1" using \<open>ps B \<in> B\<close> \<open>ps B \<in> A1\<close> by (by100 blast)
            from h\<A>_inter[rule_format, OF \<open>A1 \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>B \<noteq> A1\<close>[symmetric]]
            have "B \<inter> A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)
                \<and> B \<inter> A1 \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)" by (by100 blast)
            hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
              using \<open>ps B \<in> B \<inter> A1\<close> by (by100 blast)
            thus False using \<open>ps B \<notin> _\<close> by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        \<comment> \<open>U and V are open (finite points removed from Hausdorff).\<close>
        have hX_haus_g: "is_hausdorff_on X TX"
          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
        have hU_open: "openin_on X TX ?U"
        proof -
          have "finite (ps ` ?S_U)" using \<open>finite ?NT\<close> by (by100 blast)
          moreover have "ps ` ?S_U \<subseteq> X"
          proof
            fix x assume "x \<in> ps ` ?S_U"
            then obtain A where "A \<in> ?S_U" "x = ps A" by (by100 blast)
            hence "A \<in> ?NT" by (by100 blast)
            hence "A \<in> \<A>" by (by100 blast)
            have "ps A \<in> A" using hps \<open>A \<in> ?NT\<close> by (by100 blast)
            have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            thus "x \<in> X" using \<open>x = ps A\<close> \<open>ps A \<in> A\<close> \<open>A \<subseteq> X\<close> by (by100 blast)
          qed
          ultimately have "closedin_on X TX (ps ` ?S_U)"
            using Theorem_17_8[OF hX_haus_g] by (by100 blast)
          thus ?thesis unfolding openin_on_def closedin_on_def by (by100 blast)
        qed
        have hV_open: "openin_on X TX ?V"
        proof -
          have "finite (ps ` ?S_V)" by (by100 simp)
          moreover have "ps ` ?S_V \<subseteq> X"
          proof
            fix x assume "x \<in> ps ` ?S_V"
            hence "x = ps A1" by (by100 blast)
            have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
            have "A1 \<subseteq> X" using h\<A> hA1 by (by100 blast)
            thus "x \<in> X" using \<open>x = ps A1\<close> \<open>ps A1 \<in> A1\<close> \<open>A1 \<subseteq> X\<close> by (by100 blast)
          qed
          ultimately have "closedin_on X TX (ps ` ?S_V)"
            using Theorem_17_8[OF hX_haus_g] by (by100 blast)
          thus ?thesis unfolding openin_on_def closedin_on_def by (by100 blast)
        qed
        \<comment> \<open>U \\<cap> V is simply connected (SC lemma).\<close>
        have hUV_sc: "top1_simply_connected_on ?UV (subspace_topology X TX ?UV)"
        proof -
          \<comment> \<open>Need hvertices\\_T: all arc endpoints are in T.\<close>
          have hvert_T: "\<forall>A\<in>\<A>. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> T"
          proof (intro ballI)
            fix A e assume "A \<in> \<A>" "e \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
            show "e \<in> T"
            proof (cases "A \<subseteq> T")
              case True
              have "e \<in> A" using \<open>e \<in> top1_arc_endpoints_on A _\<close>
                unfolding top1_arc_endpoints_on_def by (by100 blast)
              thus ?thesis using True by (by100 blast)
            next
              case False
              hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
              thus ?thesis using hNT_endpoints \<open>e \<in> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          have h\<A>_inter': "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
              A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using h\<A>_inter by (by100 blast)
          have hNT_eq: "?NT = {A \<in> \<A>. \<not> A \<subseteq> T}" by (by100 blast)
          show ?thesis
            using graph_remove_interior_points_sc[OF assms(1) h\<A> h\<A>_cover h\<A>_inter' hT_tree hT_sub
                hT_subgraph hNT_eq \<open>finite ?NT\<close> hps hvert_T hx0_T h\<A>_coh] by (by100 blast)
        qed
        \<comment> \<open>U deformation retracts onto T \\<union> A1 (target for S = NT-{A1}).\<close>
        let ?target_U = "T \<union> \<Union>(?NT - ?S_U)"
        have "?target_U = T \<union> A1"
        proof -
          have "?NT - ?S_U = {A1}" using hA1 by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        have hU_dr: "top1_deformation_retract_of_on ?U (subspace_topology X TX ?U) ?target_U"
        proof -
          have "finite ?S_U" using \<open>finite ?NT\<close> by (by100 blast)
          have "?S_U \<subseteq> ?NT" by (by100 blast)
          have "\<forall>A\<in>?S_U. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hps by (by100 blast)
          from hdr_helper[OF \<open>finite ?S_U\<close> \<open>?S_U \<subseteq> ?NT\<close> this]
          show ?thesis .
        qed
        \<comment> \<open>V deformation retracts onto T \\<union> \\<Union>(NT - {A1}) (target for S = {A1}).\<close>
        let ?target_V = "T \<union> \<Union>(?NT - ?S_V)"
        have hV_dr: "top1_deformation_retract_of_on ?V (subspace_topology X TX ?V) ?target_V"
        proof -
          have "finite ?S_V" by (by100 simp)
          have "?S_V \<subseteq> ?NT" using hA1 by (by100 blast)
          have "\<forall>A\<in>?S_V. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hps hA1 by (by100 blast)
          from hdr_helper[OF \<open>finite ?S_V\<close> \<open>?S_V \<subseteq> ?NT\<close> this]
          show ?thesis .
        qed
        \<comment> \<open>\\<pi>\\_1(U) \\<cong> \\<pi>\\_1(target\\_U) which is free (1 non-tree arc, base case or IH).\<close>
        \<comment> \<open>Theorem\\_58\\_3: DR gives \\<pi>\\_1 iso. Since U/V DR onto their targets,
           \\<pi>\\_1(U) \\<cong> \\<pi>\\_1(target\\_U) and \\<pi>\\_1(V) \\<cong> \\<pi>\\_1(target\\_V).\<close>
        have hx0_U: "x0 \<in> ?U"
        proof -
          have "x0 \<in> T" using hx0_T .
          have "\<forall>A\<in>?NT - {A1}. ps A \<noteq> x0"
          proof (intro ballI)
            fix A assume "A \<in> ?NT - {A1}"
            hence "A \<in> ?NT" by (by100 blast)
            have "A \<in> \<A>" using \<open>A \<in> ?NT\<close> by (by100 blast)
            have "\<not> A \<subseteq> T" using \<open>A \<in> ?NT\<close> by (by100 blast)
            from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
            have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using hps \<open>A \<in> ?NT\<close> by (by100 blast)
            hence "ps A \<notin> T" using \<open>A \<inter> T \<subseteq> _\<close> hps \<open>A \<in> ?NT\<close> by (by100 blast)
            thus "ps A \<noteq> x0" using \<open>x0 \<in> T\<close> by (by100 blast)
          qed
          hence "x0 \<notin> ps ` (?NT - {A1})" by (by100 blast)
          thus ?thesis using \<open>x0 \<in> T\<close> hT_sub by (by100 blast)
        qed
        have hx0_V: "x0 \<in> ?V"
        proof -
          have "ps A1 \<noteq> x0"
          proof -
            have "A1 \<in> \<A>" using hA1 by (by100 blast)
            have "\<not> A1 \<subseteq> T" using hA1 by (by100 blast)
            from hT_subgraph[rule_format, OF \<open>A1 \<in> \<A>\<close>] \<open>\<not> A1 \<subseteq> T\<close>
            have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)" by (by100 blast)
            have "ps A1 \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
              using hps hA1 by (by100 blast)
            hence "ps A1 \<notin> T" using \<open>A1 \<inter> T \<subseteq> _\<close> hps hA1 by (by100 blast)
            thus ?thesis using hx0_T by (by100 blast)
          qed
          thus ?thesis using hx0_T hT_sub by (by100 blast)
        qed
        have hTX_top: "is_topology_on X TX"
          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
        have hU_sub: "?U \<subseteq> X" by (by100 blast)
        have hV_sub: "?V \<subseteq> X" by (by100 blast)
        have hU_top: "is_topology_on ?U (subspace_topology X TX ?U)"
          by (rule subspace_topology_is_topology_on[OF hTX_top hU_sub])
        have hV_top: "is_topology_on ?V (subspace_topology X TX ?V)"
          by (rule subspace_topology_is_topology_on[OF hTX_top hV_sub])
        have hx0_tU: "x0 \<in> ?target_U" using hx0_T by (by100 blast)
        have hx0_tV: "x0 \<in> ?target_V" using hx0_T by (by100 blast)
        let ?TU = "subspace_topology X TX ?U"
        let ?TV = "subspace_topology X TX ?V"
        have hpi1_U_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            (top1_fundamental_group_mul ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            (top1_fundamental_group_carrier ?U ?TU x0)
            (top1_fundamental_group_mul ?U ?TU x0)"
          by (rule Theorem_58_3[OF hU_dr hU_top hx0_tU])
        have htU_sub_U: "?target_U \<subseteq> ?U"
          using conjunct1[OF hU_dr[unfolded top1_deformation_retract_of_on_def]]
          by (by100 blast)
        have hTU_trans: "subspace_topology ?U ?TU ?target_U = subspace_topology X TX ?target_U"
          by (rule subspace_topology_trans[OF htU_sub_U])
        have hpi1_V_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            (top1_fundamental_group_mul ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            (top1_fundamental_group_carrier ?V ?TV x0)
            (top1_fundamental_group_mul ?V ?TV x0)"
          by (rule Theorem_58_3[OF hV_dr hV_top hx0_tV])
        have htV_sub_V: "?target_V \<subseteq> ?V"
          using conjunct1[OF hV_dr[unfolded top1_deformation_retract_of_on_def]]
          by (by100 blast)
        have hTV_trans: "subspace_topology ?V ?TV ?target_V = subspace_topology X TX ?target_V"
          by (rule subspace_topology_trans[OF htV_sub_V])
        \<comment> \<open>target\\_U = T \\<union> A1 has free \\<pi>\\_1 (base case: 1 non-tree arc).\<close>
        have htU_free: "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int) S'.
            top1_is_free_group_full_on G mul e invg \<iota> S'
          \<and> top1_groups_isomorphic_on G mul
              (top1_fundamental_group_carrier ?target_U (subspace_topology ?U ?TU ?target_U) x0)
              (top1_fundamental_group_mul ?target_U (subspace_topology ?U ?TU ?target_U) x0)"
          sorry \<comment> \<open>Base case: T \\<union> A1 is a graph with 1 non-tree arc \\<Rightarrow> free on 1 gen.
             Uses hTU\\_trans to match topology.\<close>
        \<comment> \<open>target\\_V has free \\<pi>\\_1 (IH: n-1 non-tree arcs).\<close>
        have htV_free: "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int) S'.
            top1_is_free_group_full_on G mul e invg \<iota> S'
          \<and> top1_groups_isomorphic_on G mul
              (top1_fundamental_group_carrier ?target_V (subspace_topology ?V ?TV ?target_V) x0)
              (top1_fundamental_group_mul ?target_V (subspace_topology ?V ?TV ?target_V) x0)"
          sorry \<comment> \<open>IH: target\\_V is a graph with card(NT)-1 non-tree arcs.
             Uses hTV\\_trans to match topology.\<close>
        \<comment> \<open>Transfer freeness via the DR iso to U and V.\<close>
        \<comment> \<open>Transfer freeness to \\<pi>\\_1(U) and \\<pi>\\_1(V) directly
           (needed for svk\\_free\\_product\\_free).\<close>
        have hU_free_direct: "\<exists>(\<iota>U::nat \<Rightarrow> _) S1. top1_is_free_group_full_on
            (top1_fundamental_group_carrier ?U ?TU x0)
            (top1_fundamental_group_mul ?U ?TU x0)
            (top1_fundamental_group_id ?U ?TU x0)
            (top1_fundamental_group_invg ?U ?TU x0)
            \<iota>U S1"
        proof -
          have hpi1_U_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?U ?TU x0) (top1_fundamental_group_mul ?U ?TU x0)
              (top1_fundamental_group_id ?U ?TU x0) (top1_fundamental_group_invg ?U ?TU x0)"
            by (rule top1_fundamental_group_is_group[OF hU_top hx0_U])
          \<comment> \<open>Chain: htU\\_free gives G free + iso(G, \\<pi>\\_1(tU)).
             Compose with hpi1\\_U\\_iso, then free\\_group\\_iso\\_transfer.\<close>
          \<comment> \<open>Use the existing hU\\_free (which already composed the isos).\<close>
          show ?thesis
            using htU_free hpi1_U_iso hpi1_U_grp
            apply (elim exE conjE)
            apply (drule groups_isomorphic_trans_fwd, assumption)
            apply (drule free_group_iso_transfer, assumption, assumption)
            apply (elim exE, rule exI, rule exI, assumption)
            done
        qed
        have hV_free_direct: "\<exists>(\<iota>V::nat \<Rightarrow> _) S2. top1_is_free_group_full_on
            (top1_fundamental_group_carrier ?V ?TV x0)
            (top1_fundamental_group_mul ?V ?TV x0)
            (top1_fundamental_group_id ?V ?TV x0)
            (top1_fundamental_group_invg ?V ?TV x0)
            \<iota>V S2"
        proof -
          have hpi1_V_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?V ?TV x0) (top1_fundamental_group_mul ?V ?TV x0)
              (top1_fundamental_group_id ?V ?TV x0) (top1_fundamental_group_invg ?V ?TV x0)"
            by (rule top1_fundamental_group_is_group[OF hV_top hx0_V])
          show ?thesis
            using htV_free hpi1_V_iso hpi1_V_grp
            apply (elim exE conjE)
            apply (drule groups_isomorphic_trans_fwd, assumption)
            apply (drule free_group_iso_transfer, assumption, assumption)
            apply (elim exE, rule exI, rule exI, assumption)
            done
        qed
        \<comment> \<open>U and V are path-connected.\<close>
        \<comment> \<open>Helper: DR + target path-connected \\<Rightarrow> space path-connected.
           Proof: H(x,\\<cdot>) gives a path from x to H(x,1) \\<in> A. A path-connected connects them.\<close>
        note hdr_pc = deformation_retract_path_connected
        have hU_pc: "top1_path_connected_on ?U (subspace_topology X TX ?U)"
        proof -
          have htarget_U_pc: "top1_path_connected_on ?target_U (subspace_topology ?U ?TU ?target_U)"
          proof -
            \<comment> \<open>Rewrite topology: subspace of U restricted to target\\_U = subspace of X.\<close>
            have "subspace_topology ?U ?TU ?target_U = subspace_topology X TX ?target_U"
              by (rule subspace_topology_trans[OF htU_sub_U])
            \<comment> \<open>T is path-connected (tree \\<Rightarrow> simply connected \\<Rightarrow> PC).\<close>
            have hT_pc: "top1_path_connected_on T (subspace_topology X TX T)"
              using tree_simply_connected[OF hT_tree] top1_simply_connected_on_path_connected by (by100 blast)
            \<comment> \<open>A1 is path-connected (arc \\<cong> [0,1] which is convex \\<Rightarrow> PC).\<close>
            have hA1_pc: "top1_path_connected_on A1 (subspace_topology X TX A1)"
            proof -
              have hA1_arc_loc: "top1_is_arc_on A1 (subspace_topology X TX A1)"
                using h\<A> hA1 by (by100 blast)
              obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A1 (subspace_topology X TX A1) h"
                using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
              have hI_pc: "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
              proof -
                have hne: "top1_unit_interval \<noteq> {}"
                  unfolding top1_unit_interval_def by (by100 auto)
                have hconv: "\<And>x y t. x \<in> top1_unit_interval \<Longrightarrow> y \<in> top1_unit_interval \<Longrightarrow>
                    0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> (1 - t) * x + t * y \<in> top1_unit_interval"
                proof -
                  fix x y t :: real
                  assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
                      and ht0: "0 \<le> t" and ht1: "t \<le> 1"
                  have "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
                    using hx hy unfolding top1_unit_interval_def by (by100 simp)+
                  have h1t: "1 - t \<ge> 0" using ht1 by (by100 linarith)
                  have "(1 - t) * x \<ge> 0" using h1t \<open>0 \<le> x\<close> by (by100 simp)
                  have "t * y \<ge> 0" using ht0 \<open>0 \<le> y\<close> by (by100 simp)
                  have "(1 - t) * x + t * y \<ge> 0" using \<open>(1-t)*x \<ge> 0\<close> \<open>t*y \<ge> 0\<close> by (by100 linarith)
                  moreover have "(1 - t) * x + t * y \<le> 1"
                  proof -
                    have "(1 - t) * x \<le> (1 - t)"
                      using mult_left_mono[OF \<open>x \<le> 1\<close> h1t] by (by100 simp)
                    moreover have "t * y \<le> t"
                      using mult_left_mono[OF \<open>y \<le> 1\<close> ht0] by (by100 simp)
                    ultimately show ?thesis by (by100 linarith)
                  qed
                  ultimately show "(1 - t) * x + t * y \<in> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 simp)
                qed
                from convex_real_subspace_path_connected[OF hne hconv] show ?thesis
                  unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
              qed
              from homeomorphism_preserves_path_connected[OF hh hI_pc] show ?thesis .
            qed
            \<comment> \<open>Endpoints of A1 are in T, so there's a common point.\<close>
            have "\<exists>p. p \<in> T \<and> p \<in> A1"
            proof -
              have "A1 \<in> ?NT" using hA1 by (by100 blast)
              have hA1_arc_here: "top1_is_arc_on A1 (subspace_topology X TX A1)"
                using h\<A> hA1 by (by100 blast)
              obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A1 (subspace_topology X TX A1) h'"
                using hA1_arc_here unfolding top1_is_arc_on_def by (by100 blast)
              have hX_strict: "is_topology_on_strict X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hX_haus: "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "A1 \<subseteq> X" using h\<A> hA1 by (by100 blast)
              from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A1 \<subseteq> X\<close> hA1_arc_here hh']
              have hep: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {h' 0, h' 1}" .
              have "h' 0 \<in> T" using hNT_endpoints[rule_format, OF \<open>A1 \<in> ?NT\<close>] hep by (by100 simp)
              have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "h' 0 \<in> A1"
                using hh' h0_I unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              thus ?thesis using \<open>h' 0 \<in> T\<close> by (by100 blast)
            qed
            then obtain p0 where hp0_T: "p0 \<in> T" and hp0_A1: "p0 \<in> A1" by (by100 blast)
            \<comment> \<open>Apply finite union with common point.\<close>
            have hA1_sub_X: "A1 \<subseteq> X" using h\<A> hA1 by (by100 blast)
            have htU_top: "is_topology_on ?target_U (subspace_topology X TX ?target_U)"
            proof -
              have "?target_U \<subseteq> X" using hT_sub hA1_sub_X by (by100 blast)
              thus ?thesis using subspace_topology_is_topology_on[OF hTX_top] by (by100 blast)
            qed
            have "top1_path_connected_on ?target_U (subspace_topology X TX ?target_U)"
            proof -
              have "?target_U = T \<union> A1"
                using \<open>?target_U = T \<union> A1\<close> .
              let ?F = "{T, A1}"
              have "finite ?F" by (by100 simp)
              have "\<forall>A\<in>?F. A \<subseteq> ?target_U"
                using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
              have "\<forall>A\<in>?F. A \<subseteq> X" using hT_sub hA1_sub_X by (by100 blast)
              have "?target_U = \<Union>?F" using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
              have "\<forall>A\<in>?F. top1_path_connected_on A (subspace_topology X TX A)"
                using hT_pc hA1_pc by (by100 blast)
              \<comment> \<open>Transfer PC from subspace of X to subspace of target\\_U.\<close>
              have "\<forall>A\<in>?F. top1_path_connected_on A (subspace_topology ?target_U (subspace_topology X TX ?target_U) A)"
              proof (intro ballI)
                fix A assume hA_F: "A \<in> ?F"
                hence hA_sub_tU: "A \<subseteq> ?target_U" using \<open>\<forall>A\<in>?F. A \<subseteq> ?target_U\<close> by (by100 blast)
                have hA_eq: "subspace_topology ?target_U (subspace_topology X TX ?target_U) A = subspace_topology X TX A"
                  by (rule subspace_topology_trans[OF hA_sub_tU])
                have "top1_path_connected_on A (subspace_topology X TX A)"
                  using \<open>\<forall>A\<in>?F. top1_path_connected_on A (subspace_topology X TX A)\<close> hA_F by (by100 blast)
                thus "top1_path_connected_on A (subspace_topology ?target_U (subspace_topology X TX ?target_U) A)"
                  using hA_eq by (by100 simp)
              qed
              have "\<forall>A\<in>?F. p0 \<in> A" using hp0_T hp0_A1 by (by100 blast)
              from path_connected_finite_union_common_point[OF htU_top \<open>finite ?F\<close>
                  \<open>\<forall>A\<in>?F. A \<subseteq> ?target_U\<close>
                  \<open>\<forall>A\<in>?F. top1_path_connected_on A (subspace_topology ?target_U _ A)\<close>
                  \<open>\<forall>A\<in>?F. p0 \<in> A\<close> \<open>?target_U = \<Union>?F\<close>]
              show ?thesis .
            qed
            thus ?thesis using \<open>subspace_topology ?U ?TU ?target_U = subspace_topology X TX ?target_U\<close>
              by (by100 simp)
          qed
          show ?thesis by (rule hdr_pc[OF hU_dr hU_top htarget_U_pc])
        qed
        have hV_pc: "top1_path_connected_on ?V (subspace_topology X TX ?V)"
        proof -
          have htarget_V_pc: "top1_path_connected_on ?target_V (subspace_topology ?V ?TV ?target_V)"
          proof -
            have "subspace_topology ?V ?TV ?target_V = subspace_topology X TX ?target_V"
              by (rule subspace_topology_trans[OF htV_sub_V])
            have "?target_V = T \<union> \<Union>(?NT - {A1})" by (by100 blast)
            have "finite (?NT - {A1})" using \<open>finite ?NT\<close> by (by100 blast)
            have "\<forall>A\<in>?NT - {A1}. top1_is_arc_on A (subspace_topology X TX A) \<and> A \<subseteq> X"
              using h\<A> by (by100 blast)
            have "\<forall>A\<in>?NT - {A1}. \<exists>e. e \<in> T \<and> e \<in> A"
            proof (intro ballI)
              fix Aj assume "Aj \<in> ?NT - {A1}"
              hence "Aj \<in> ?NT" by (by100 blast)
              have "Aj \<in> \<A>" using \<open>Aj \<in> ?NT\<close> by (by100 blast)
              have hAj_arc: "top1_is_arc_on Aj (subspace_topology X TX Aj)"
                using h\<A> \<open>Aj \<in> \<A>\<close> by (by100 blast)
              have hAj_sub: "Aj \<subseteq> X" using h\<A> \<open>Aj \<in> \<A>\<close> by (by100 blast)
              obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology Aj (subspace_topology X TX Aj) hj"
                using hAj_arc unfolding top1_is_arc_on_def by (by100 blast)
              have hX_strict: "is_topology_on_strict X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hX_haus: "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hX_strict hX_haus hAj_sub hAj_arc hhj]
              have "top1_arc_endpoints_on Aj (subspace_topology X TX Aj) = {hj 0, hj 1}" .
              have "hj 0 \<in> T"
                using hNT_endpoints[rule_format, OF \<open>Aj \<in> ?NT\<close>] \<open>top1_arc_endpoints_on Aj _ = _\<close>
                by (by100 simp)
              have "hj 0 \<in> Aj"
              proof -
                have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                thus ?thesis using hhj unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              qed
              thus "\<exists>e. e \<in> T \<and> e \<in> Aj" using \<open>hj 0 \<in> T\<close> by (by100 blast)
            qed
            from tree_union_arcs_path_connected[OF hTX_top hT_tree hT_sub
                \<open>finite (?NT - {A1})\<close> \<open>\<forall>A\<in>?NT - {A1}. _ \<and> _\<close>
                \<open>\<forall>A\<in>?NT - {A1}. \<exists>e. _\<close> hx0_T]
            have "top1_path_connected_on ?target_V (subspace_topology X TX ?target_V)"
              using \<open>?target_V = T \<union> \<Union>(?NT - {A1})\<close> by (by100 simp)
            thus ?thesis using \<open>subspace_topology ?V ?TV ?target_V = _\<close> by (by100 simp)
          qed
          show ?thesis by (rule hdr_pc[OF hV_dr hV_top htarget_V_pc])
        qed
        \<comment> \<open>x0 \\<in> U \\<cap> V.\<close>
        have hx0_UV: "x0 \<in> ?UV"
        proof -
          have "x0 \<in> T" using hx0_T .
          have "x0 \<notin> ps ` ?NT"
          proof
            assume "x0 \<in> ps ` ?NT"
            then obtain A where "A \<in> ?NT" "ps A = x0" by (by100 blast)
            have "A \<in> \<A>" using \<open>A \<in> ?NT\<close> by (by100 blast)
            have "\<not> A \<subseteq> T" using \<open>A \<in> ?NT\<close> by (by100 blast)
            from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
            have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using hps \<open>A \<in> ?NT\<close> by (by100 blast)
            hence "x0 \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>ps A = x0\<close> by (by100 simp)
            hence "x0 \<notin> A \<inter> T"
              using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close> by (by100 blast)
            have "x0 \<in> A" using hps \<open>A \<in> ?NT\<close> \<open>ps A = x0\<close> by (by100 blast)
            thus False using \<open>x0 \<notin> A \<inter> T\<close> \<open>x0 \<in> T\<close> by (by100 blast)
          qed
          thus ?thesis using \<open>x0 \<in> T\<close> hT_sub by (by100 blast)
        qed
        \<comment> \<open>Apply SvK free product to get \\<pi>\\_1(X) free.\<close>
        show ?thesis sorry \<comment> \<open>Assemble: svk\\_free\\_product\\_free\\_with\\_generators
           with U, V, U\\<cap>V simply connected, U/V path-connected, \\<pi>\\_1 free.\<close>
      qed
    next
      case InfFalse: False
      \<comment> \<open>Infinite case: any loop in finitely many arcs (compactness).\\<close>
      show ?thesis sorry \<comment> \<open>Compactness reduction: any loop in X lies in T \\<union> (finitely many arcs).
         Apply finite case to the subgraph T \\<union> {finite arcs}.
         Book reference: Munkres 84.7 Step 3.\\<close>
    qed
  qed
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
      and "e0' \<in> E'" and hE'_strict: "is_topology_on_strict E' TE'"
    sorry \<comment> \<open>Existence of covering space (Theorem 82.1) for the H-image in \<pi>_1(X).
       The covering construction gives strict topology on E'.\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2: covering of graph is graph).
     \<pi>_1(E) is free (Theorem 84.7: fund group of connected graph is free).
     p_* injective (covering maps induce injections on \<pi>_1).
     H iso p_*(pi1(E)) which is free (subgroup of free = free via injection).\<close>
  have hE'_graph: "top1_is_graph_on E' TE'"
    by (rule graph_covering_is_graph[OF \<open>top1_is_graph_on X TX\<close>
        \<open>top1_covering_map_on E' TE' X TX p'\<close> hE'_strict])
  \<comment> \<open>Step 3b: \\<pi>\\_1(E') is free (Theorem 84.7).\<close>
  from Theorem_84_7_fund_group_graph_is_free[OF hE'_graph
      \<open>top1_connected_on E' TE'\<close> \<open>e0' \<in> E'\<close>]
  obtain G_E :: "int set" and mul_E e_E invg_E and \<iota>_E :: "nat \<Rightarrow> int" and S_E
    where hfree_E: "top1_is_free_group_full_on G_E mul_E e_E invg_E \<iota>_E S_E"
      and hiso_E: "top1_groups_isomorphic_on G_E mul_E
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0')"
    by (by100 blast)
  \<comment> \<open>Step 3c: H is free. From p'* injective + H iso p'*(pi1(E')).\<close>
  show ?thesis sorry \<comment> \<open>Need: H corresponds to p'*(pi1(E')) under iso G = pi1(X).
     This requires the covering E' to satisfy p'*(pi1(E')) = image of H.
     Then: H iso pi1(E') (p'* injective) iso G\_E (free).
     Missing ingredient: sorry at 20302 needs to export the H-correspondence.\<close>
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
  proof -
    have "finite S" using assms(2) by (cases "finite S", by100 simp, by100 simp)
    note hrealiz = free_group_realized_by_wedge[OF assms(1) this]
    from hrealiz obtain X' :: "'a set" and TX' :: "'a set set" and x0' :: 'a where
      hconj: "top1_is_graph_on X' TX' \<and> top1_connected_on X' TX' \<and> x0' \<in> X'
      \<and> top1_groups_isomorphic_on F mul
          (top1_fundamental_group_carrier X' TX' x0') (top1_fundamental_group_mul X' TX' x0')"
      by (by5000 fast)
    show ?thesis
      apply (rule that[of X' TX' x0'])
      using hconj by (by100 blast)+
  qed
  \<comment> \<open>Step 2: H \<le> F corresponds to a k-sheeted covering E of X.
     By Theorem 82.1, there exists a covering E with p_*(\<pi>_1(E)) = H-image.\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a" and e0' :: 'b
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
      and he0': "e0' \<in> E'"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).
       E' is nonempty (covering of connected nonempty X).\<close>
  \<comment> \<open>Step 3a: pi1(E') is free (Theorem 84.7).\<close>
  from Theorem_84_7_fund_group_graph_is_free[OF hE'_graph hE'_conn he0']
  obtain G_E :: "int set" and mul_E e_E invg_E and \<iota>_E :: "nat \<Rightarrow> int" and S_E
    where hfree_E: "top1_is_free_group_full_on G_E mul_E e_E invg_E \<iota>_E S_E"
      and hiso_E: "top1_groups_isomorphic_on G_E mul_E
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0')"
    by (by100 blast)
  \<comment> \<open>Step 3b: H free with rank kn+1 (Euler characteristic argument).\<close>
  have hE'_free: "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
      top1_is_free_group_full_on H mul e invg \<iota>H SH \<and> card SH = k * n + 1"
    sorry \<comment> \<open>Euler char: X has 1 vertex + (n+1) edges, chi(X) = -n.
       E' has k sheets: chi(E') = k*chi(X) = -kn.
       rank(pi1(E')) = 1-chi(E') = kn+1.
       H iso pi1(E') (from covering + p* injective) with same rank.\<close>
  show ?thesis using hE'_free by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end

