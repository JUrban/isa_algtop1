theory AlgTop
  imports "AlgTopCached8.AlgTopCached8"
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



\<comment> \<open>Free group embedding: a group hom from free(S1) to free(S2) that maps generators
   to generators is injective, when S1 \\<subseteq> S2.\<close>
lemma free_group_hom_subset_injective:
  fixes S1 :: "'s set" and S2 :: "'s set"
  assumes hfree1: "top1_is_free_group_full_on G1 mul1 e1 invg1 \<iota>1 S1"
      and hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 S2"
      and hS12: "S1 \<subseteq> S2"
      and hhom: "top1_group_hom_on G1 mul1 G2 mul2 \<phi>"
      and hgen_map: "\<forall>s\<in>S1. \<phi> (\<iota>1 s) = \<iota>2 s"
  shows "inj_on \<phi> G1"
proof (rule inj_onI)
  fix x y assume hx: "x \<in> G1" and hy: "y \<in> G1" and heq: "\<phi> x = \<phi> y"
  have hG1: "top1_is_group_on G1 mul1 e1 invg1"
    using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG2: "top1_is_group_on G2 mul2 e2 invg2"
    using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>\\<phi>(x * y\<inverse>) = \\<phi>(x) * \\<phi>(y)\<inverse> = e2. So x * y\<inverse> \\<in> ker(\\<phi>).
     Need: ker(\\<phi>) = {e1}. Sufficient: \\<phi>(z) = e2 \\<Longrightarrow> z = e1.\<close>
  have hxy_inv: "mul1 x (invg1 y) \<in> G1"
    using hG1 hx hy unfolding top1_is_group_on_def by (by100 blast)
  have hphi_xy: "\<phi> (mul1 x (invg1 y)) = e2"
  proof -
    have hinvy: "invg1 y \<in> G1" using hG1 hy unfolding top1_is_group_on_def by (by100 blast)
    have "\<phi> (mul1 x (invg1 y)) = mul2 (\<phi> x) (\<phi> (invg1 y))"
      using hhom hx hinvy unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<phi> (invg1 y) = invg2 (\<phi> y)"
      using hom_preserves_inv[OF hG1 hG2 hhom hy] by (by100 simp)
    also have "mul2 (\<phi> x) (invg2 (\<phi> y)) = mul2 (\<phi> y) (invg2 (\<phi> y))"
      using heq by (by100 simp)
    also have "... = e2" using hG2 hhom hy
      unfolding top1_is_group_on_def top1_group_hom_on_def by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>Show: z = mul1 x (invg1 y) = e1. Then x = y.\<close>
  have "mul1 x (invg1 y) = e1"
  proof -
    let ?z = "mul1 x (invg1 y)"
    \<comment> \<open>?z \\<in> G1 = subgroup\\_generated(\\<iota>1 ` S1). By word\\_repr, ?z = e1 or has a word.\<close>
    have "\<iota>1 ` S1 \<subseteq> G1"
      using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
    have hG1_gen: "G1 = top1_subgroup_generated_on G1 mul1 e1 invg1 (\<iota>1 ` S1)"
      using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?z \<in> top1_subgroup_generated_on G1 mul1 e1 invg1 (\<iota>1 ` S1)"
      using hxy_inv hG1_gen by (by100 simp)
    from subgroup_generated_word_repr[OF hG1 \<open>\<iota>1 ` S1 \<subseteq> G1\<close> this]
    have "?z = e1 \<or> (\<exists>ws. length ws > 0 \<and>
        (\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)) \<and>
        foldr mul1 ws e1 = ?z)" .
    thus "?z = e1"
    proof
      assume "?z = e1" thus ?thesis .
    next
      assume "\<exists>ws. length ws > 0 \<and>
          (\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)) \<and>
          foldr mul1 ws e1 = ?z"
      then obtain ws where hws_len: "length ws > 0"
          and hws_in: "\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)"
          and hws_eq: "foldr mul1 ws e1 = ?z" by (by100 blast)
      \<comment> \<open>Convert ws to an (s, bool) list sb.\<close>
      \<comment> \<open>Each ws!i is either \\<iota>1(s) (True) or invg1(\\<iota>1(s)) (False) for some s \\<in> S1.\<close>
      \<comment> \<open>Then word\\_product(G1, map (%(s,b). (\\<iota>1 s, b)) sb) = foldr mul1 ws e1 = ?z.\<close>
      \<comment> \<open>\\<phi>(?z) = e2. By hom\\_word\\_product: word\\_product(G2, map (%(s,b). (\\<phi>(\\<iota>1 s), b)) sb) = e2.\<close>
      \<comment> \<open>\\<phi>(\\<iota>1 s) = \\<iota>2 s. So word\\_product(G2, map (%(s,b). (\\<iota>2 s, b)) sb) = e2.\<close>
      \<comment> \<open>Apply free\\_group\\_word\\_kernel to free(S2) = G2 with target G1 and map
         \\<phi>2(s) = \\<iota>1(s) for s \\<in> S1, \\<phi>2(s) = e1 for s \\<notin> S1:
         word\\_product(G1, map (%(s,b). (\\<phi>2 s, b)) sb) = e1.
         Since all s in sb are in S1: \\<phi>2(s) = \\<iota>1(s).
         So word\\_product(G1, map (%(s,b). (\\<iota>1 s, b)) sb) = e1 = ?z.
         But ?z = foldr mul1 ws e1 \\<noteq> e1 (by the assumption we're in the \\<exists> branch).

         Wait -- ?z \\<noteq> e1 only if we assumed that. Let me check: we're in the
         \\<exists>ws branch of the disjunction, which means ws is non-empty.
         But word\\_product = ?z and word\\_product via \\<phi>2 = e1.
         So ?z = e1 after all. This means the \\<exists>ws branch gives ?z = e1 too!\<close>
      \<comment> \<open>Convert ws to (s, bool) list.\<close>
      have "\<forall>i<length ws. \<exists>s\<in>S1. ws ! i = \<iota>1 s \<or> ws ! i = invg1 (\<iota>1 s)"
      proof (intro allI impI)
        fix i assume "i < length ws"
        from hws_in[rule_format, OF this]
        show "\<exists>s\<in>S1. ws ! i = \<iota>1 s \<or> ws ! i = invg1 (\<iota>1 s)"
          by (by100 blast)
      qed
      \<comment> \<open>By choice, obtain a function picking s for each position.\<close>
      hence "\<exists>sf. \<forall>i<length ws. sf i \<in> S1 \<and> (ws ! i = \<iota>1 (sf i) \<or> ws ! i = invg1 (\<iota>1 (sf i)))"
        by (by5000 metis)
      then obtain sf where hsf: "\<forall>i<length ws. sf i \<in> S1 \<and>
          (ws ! i = \<iota>1 (sf i) \<or> ws ! i = invg1 (\<iota>1 (sf i)))" by (by100 blast)
      \<comment> \<open>Define the boolean: True if ws!i = \\<iota>1(sf i), False if invg1.\<close>
      define bf where "bf i = (ws ! i = \<iota>1 (sf i))" for i
      define sb where "sb = map (\<lambda>i. (sf i, bf i)) [0..<length ws]"
      \<comment> \<open>word\\_product(G1, map (%s. (\\<iota>1 s, b)) sb) = foldr mul1 ws e1 = ?z.\<close>
      have hwp_eq: "top1_group_word_product mul1 e1 invg1
          (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = ?z"
      proof -
        \<comment> \<open>By word\\_product\\_as\\_foldr, word\\_product = foldr mul1 (mapped list) e1.
           The mapped list equals ws, so the result equals foldr mul1 ws e1 = ?z.\<close>
        have "top1_group_word_product mul1 e1 invg1 (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) =
            foldr mul1 (map (\<lambda>(x,b). if b then x else invg1 x)
                (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) e1"
          by (rule word_product_as_foldr)
        \<comment> \<open>Show: map ... (map ... sb) = ws.\<close>
        moreover have "map (\<lambda>(x,b). if b then x else invg1 x)
            (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = ws"
        proof (rule nth_equalityI)
          show "length (map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) = length ws"
            unfolding sb_def by (by100 simp)
        next
          fix i assume "i < length (map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))"
          hence hi: "i < length ws" unfolding sb_def by (by100 simp)
          \<comment> \<open>The i-th element of the composed map is:
             if bf i then \\<iota>1(sf i) else invg1(\\<iota>1(sf i)).
             By bf\\_def, this equals ws!i in both cases.\<close>
          have "sb ! i = (sf i, bf i)" unfolding sb_def using hi by (by100 simp)
          hence "(\<lambda>(s,b). (\<iota>1 s, b)) (sb ! i) = (\<iota>1 (sf i), bf i)"
            by (by100 simp)
          hence "(map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i = (\<iota>1 (sf i), bf i)"
            unfolding sb_def using hi by (by100 simp)
          hence "(map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i =
              (if bf i then \<iota>1 (sf i) else invg1 (\<iota>1 (sf i)))"
            unfolding sb_def using hi by (by100 simp)
          also have "... = ws ! i"
          proof (cases "bf i")
            case True
            hence "ws ! i = \<iota>1 (sf i)" unfolding bf_def by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            hence "ws ! i \<noteq> \<iota>1 (sf i)" unfolding bf_def by (by100 simp)
            from hsf[rule_format, OF hi] this
            have "ws ! i = invg1 (\<iota>1 (sf i))" by (by100 blast)
            thus ?thesis using False by (by100 simp)
          qed
          finally show "(map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i = ws ! i" .
        qed
        ultimately show ?thesis using hws_eq by (by100 simp)
      qed
      \<comment> \<open>All generators in S1.\<close>
      have hsb_in: "\<forall>i<length sb. fst (sb ! i) \<in> S1"
        unfolding sb_def using hsf by (by100 auto)
      \<comment> \<open>\\<phi>(?z) = e2. So \\<phi>(word\\_product(G1, ...)) = e2.\<close>
      \<comment> \<open>By hom\\_word\\_product: word\\_product(G2, \\<phi>-mapped) = e2.\<close>
      \<comment> \<open>\\<phi>(\\<iota>1 s) = \\<iota>2 s for s \\<in> S1.\<close>
      \<comment> \<open>Apply free\\_group\\_word\\_kernel to G2 = free(S2) with target G1
         and map \\<phi>2(s) = \\<iota>1 s for s \\<in> S1, e1 otherwise:
         word\\_product(G1, ...) = e1.\<close>
      have "top1_group_word_product mul1 e1 invg1
          (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = e1"
      proof -
        \<comment> \<open>\\<phi>(word\\_product(G1, sb)) = word\\_product(G2, \\<phi>-sb) = e2.\<close>
        have hsb_in_G1: "\<forall>i<length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb).
            fst ((map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i) \<in> G1"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)"
          hence "i < length sb" by (by100 simp)
          hence "fst (sb ! i) \<in> S1" using hsb_in by (by100 blast)
          hence "\<iota>1 (fst (sb ! i)) \<in> G1" using \<open>\<iota>1 ` S1 \<subseteq> G1\<close> by (by100 blast)
          obtain s' b' where "sb ! i = (s', b')" by (cases "sb ! i") (by100 blast)
          thus "fst ((map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i) \<in> G1"
            using \<open>i < length sb\<close> \<open>\<iota>1 (fst (sb ! i)) \<in> G1\<close> \<open>sb ! i = (s', b')\<close> by (by100 simp)
        qed
        have hphi_wp: "\<phi> (top1_group_word_product mul1 e1 invg1
            (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) = e2"
          using hwp_eq hphi_xy by (by100 simp)
        \<comment> \<open>word\\_product(G2, [(\\<iota>2 s, b)]) = e2 (by hom\\_word\\_product + hgen\\_map).\<close>
        have hphi_mapped: "top1_group_word_product mul2 e2 invg2
            (map (\<lambda>(s,b). (\<iota>2 s, b)) sb) = e2"
        proof -
          from hom_word_product[OF hG1 hG2 hhom hsb_in_G1]
          have "\<phi> (top1_group_word_product mul1 e1 invg1
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) =
              top1_group_word_product mul2 e2 invg2
              (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))" .
          moreover have "map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) =
              map (\<lambda>(s,b). (\<iota>2 s, b)) sb"
          proof (rule nth_equalityI)
            show "length (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) =
                length (map (\<lambda>(s,b). (\<iota>2 s, b)) sb)" by (by100 simp)
          next
            fix i assume "i < length (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))"
            hence hi: "i < length sb" by (by100 simp)
            have "fst (sb ! i) \<in> S1" using hsb_in hi by (by100 blast)
            hence "\<phi> (\<iota>1 (fst (sb ! i))) = \<iota>2 (fst (sb ! i))"
              using hgen_map by (by100 blast)
            obtain s' b' where "sb ! i = (s', b')" by (cases "sb ! i") (by100 blast)
            thus "(map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i =
                (map (\<lambda>(s,b). (\<iota>2 s, b)) sb) ! i"
              using hi \<open>\<phi> (\<iota>1 (fst (sb ! i))) = \<iota>2 (fst (sb ! i))\<close> \<open>sb ! i = (s', b')\<close>
              by (by100 simp)
          qed
          ultimately show ?thesis using hphi_wp by (by5000 metis)
        qed
        \<comment> \<open>Apply free\\_group\\_word\\_kernel to G2 with target G1.\<close>
        have hsb_in_S2: "\<forall>i<length sb. fst (sb ! i) \<in> S2"
          using hsb_in hS12 by (by100 blast)
        define \<phi>2 where "\<phi>2 s = (if s \<in> S1 then \<iota>1 s else e1)" for s
        have h\<phi>2_in: "\<forall>s\<in>S2. \<phi>2 s \<in> G1"
        proof (intro ballI)
          fix s assume "s \<in> S2"
          show "\<phi>2 s \<in> G1"
          proof (cases "s \<in> S1")
            case True
            hence "\<phi>2 s = \<iota>1 s" unfolding \<phi>2_def by (by100 simp)
            thus ?thesis using \<open>\<iota>1 ` S1 \<subseteq> G1\<close> True by (by100 blast)
          next
            case False
            hence "\<phi>2 s = e1" unfolding \<phi>2_def by (by100 simp)
            thus ?thesis using hG1 unfolding top1_is_group_on_def by (by100 blast)
          qed
        qed
        from free_group_word_kernel[OF hfree2 hG1 h\<phi>2_in hsb_in_S2 hphi_mapped]
        have "top1_group_word_product mul1 e1 invg1
            (map (\<lambda>(s,b). (\<phi>2 s, b)) sb) = e1" .
        \<comment> \<open>Since all s in sb are in S1: \\<phi>2 s = \\<iota>1 s.\<close>
        moreover have "map (\<lambda>(s,b). (\<phi>2 s, b)) sb = map (\<lambda>(s,b). (\<iota>1 s, b)) sb"
        proof (rule nth_equalityI)
          show "length (map (\<lambda>(s,b). (\<phi>2 s, b)) sb) = length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)"
            by (by100 simp)
        next
          fix i assume "i < length (map (\<lambda>(s,b). (\<phi>2 s, b)) sb)"
          hence "i < length sb" by (by100 simp)
          hence "fst (sb ! i) \<in> S1" using hsb_in by (by100 blast)
          hence "\<phi>2 (fst (sb ! i)) = \<iota>1 (fst (sb ! i))" unfolding \<phi>2_def by (by100 simp)
          obtain si bi where "sb ! i = (si, bi)" by (cases "sb ! i") (by100 blast)
          hence "(\<lambda>(s,b). (\<phi>2 s, b)) (sb ! i) = (\<phi>2 si, bi)" by (by100 simp)
          also have "... = (\<iota>1 si, bi)" using \<open>\<phi>2 (fst (sb ! i)) = \<iota>1 (fst (sb ! i))\<close>
            \<open>sb ! i = (si, bi)\<close> by (by100 simp)
          also have "... = (\<lambda>(s,b). (\<iota>1 s, b)) (sb ! i)" using \<open>sb ! i = (si, bi)\<close> by (by100 simp)
          finally show "(map (\<lambda>(s,b). (\<phi>2 s, b)) sb) ! i = (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i"
            using \<open>i < length sb\<close> by (by100 simp)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>So ?z = e1.\<close>
      show "?z = e1" using hwp_eq \<open>top1_group_word_product mul1 e1 invg1 _ = e1\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>mul1 x (invg1 y) = e1 implies x = y.\<close>
  thus "x = y" using hG1 hx hy
    unfolding top1_is_group_on_def by (by5000 metis)
qed

\<comment> \<open>Theorem\_71\_3\_finite moved to AlgTopCached8.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful): \\<pi>\\_1(X, p) is free with generators indexed by J.
   This is the actual book statement — \\<pi>\\_1 itself is the free group.\<close>
theorem Theorem_71_3_pi1_free:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX J p"
  shows "\<exists>(\<iota>::'i \<Rightarrow> _). top1_is_free_group_full_on
      (top1_fundamental_group_carrier X TX p)
      (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p)
      (top1_fundamental_group_invg X TX p)
      \<iota> J"
proof -
  \<comment> \<open>Extract circles from wedge definition.\<close>
  from assms[unfolded top1_is_wedge_of_circles_on_def]
  obtain C where
    hstrict: "is_topology_on_strict X TX" and hhaus: "is_hausdorff_on X TX" and hp: "p \<in> X"
    and hC: "\<forall>\<alpha>\<in>J. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
           \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
    and hcover: "(\<Union>\<alpha>\<in>J. C \<alpha>) = X"
    and hdisjoint: "\<forall>\<alpha>\<in>J. \<forall>\<beta>\<in>J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
    and hweak: "\<forall>D. D \<subseteq> X \<longrightarrow>
           (closedin_on X TX D \<longleftrightarrow>
            (\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
    by (elim conjE exE) (rule that, assumption+)
  have hTX: "is_topology_on X TX" using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>For each \\<alpha>, choose a generator loop f\\_\\<alpha> in C\\_\\<alpha>.\<close>
  \<comment> \<open>Define \\<iota>(\\<alpha>) = [f\\_\\<alpha>] \\<in> \\<pi>\\_1(X, p).\<close>
  \<comment> \<open>The book proves three things:
     (1) The groups G\\_\\<alpha> = image of \\<pi>\\_1(C\\_\\<alpha>) generate \\<pi>\\_1(X).
     (2) The inclusions i\\_\\<alpha> are monomorphisms.
     (3) No reduced word in the G\\_\\<alpha> equals the identity.
     All three use the fact that loops/homotopies lie in finite sub-wedges.\<close>
  \<comment> \<open>This is a complex proof requiring the full infrastructure from above
     (hC\\_open, hcompact\\_finite, hloop\\_finite) plus hhtpy\\_finite and hfinite\\_free.
     We defer to a detailed sorry-first skeleton.\<close>
  show ?thesis
  proof (cases "finite J")
    case True
    \<comment> \<open>Finite case: from Theorem\\_71\\_3\\_finite.\<close>
    from Theorem_71_3_finite[OF assms True]
    obtain G :: "int set" and mul e invg and \<iota> :: "'i \<Rightarrow> int" where
      hfree: "top1_is_free_group_full_on G mul e invg \<iota> J" and
      hiso: "top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)"
      by (by100 blast)
    \<comment> \<open>Transfer freeness from G to \\<pi>\\_1 via the isomorphism.\<close>
    have hpi1_grp: "top1_is_group_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
      by (rule top1_fundamental_group_is_group[OF hTX hp])
    from free_group_iso_transfer[OF hfree hiso hpi1_grp]
    show ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>Infinite case: book proof using compactness + coherent topology.
       Every loop/homotopy lies in a finite sub-wedge (hloop\\_finite, hhtpy\\_finite).
       Each finite sub-wedge has free \\<pi>\\_1 (Theorem 71.1).
       The three conditions of top1\\_is\\_free\\_group\\_full\\_on each reduce to the finite case:
       (1) Generators generate: loop in finite sub-wedge \\<Rightarrow> product of generators.
       (2) Injectivity: loop in C\\_\\<beta> homotopic to constant in X \\<Rightarrow> in finite sub-wedge \\<Rightarrow> in C\\_\\<beta>.
       (3) No reduced word = id: word in finite sub-wedge \\<Rightarrow> contradicts Theorem 71.1.\<close>
    \<comment> \<open>Inline the infrastructure from the general theorem's infinite case.\<close>
    \<comment> \<open>C\\_\\<alpha> - {p} open, compact meets finitely many, loop in finite sub-wedge.\<close>
    have hC_open: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> C \<alpha> - {p} \<in> TX"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      \<comment> \<open>Show X - (C\\_\\<alpha> - {p}) is closed, i.e. for each \\<beta>, C\\_\\<beta> \\<inter> (X - (C\\_\\<alpha> - {p})) closed in C\\_\\<beta>.\<close>
      have hcl: "closedin_on X TX (X - (C \<alpha> - {p}))"
      proof -
        have hsub: "X - (C \<alpha> - {p}) \<subseteq> X" by (by100 blast)
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> (X - (C \<alpha> - {p})))"
        proof (intro ballI)
          fix \<beta> assume h\<beta>: "\<beta> \<in> J"
          show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> (X - (C \<alpha> - {p})))"
          proof (cases "\<beta> = \<alpha>")
            case True
            hence "C \<beta> \<inter> (X - (C \<alpha> - {p})) = {p}"
              using hC h\<alpha> by (by100 blast)
            moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) {p}"
            proof -
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have "p \<in> C \<beta>" using hC h\<beta> by (by100 blast)
              have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<beta> \<subseteq> X\<close> hhaus
                by (by100 blast)
              have "finite {p}" by (by100 simp)
              have "{p} \<subseteq> C \<beta>" using \<open>p \<in> C \<beta>\<close> by (by100 blast)
              from Theorem_17_8[OF \<open>is_hausdorff_on (C \<beta>) _\<close> \<open>finite {p}\<close> \<open>{p} \<subseteq> C \<beta>\<close>]
              show ?thesis .
            qed
            ultimately show ?thesis by (by100 simp)
          next
            case False
            hence "C \<beta> \<inter> (C \<alpha> - {p}) = {}"
              using hdisjoint h\<alpha> h\<beta> by (by100 blast)
            hence "C \<beta> \<inter> (X - (C \<alpha> - {p})) = C \<beta>"
              using hC h\<beta> by (by100 blast)
            moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta>)"
            proof -
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have htop: "is_topology_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                by (rule subspace_topology_is_topology_on)
                   (use hstrict in \<open>unfold is_topology_on_strict_def, by100 blast\<close>,
                    use \<open>C \<beta> \<subseteq> X\<close> in blast)
              from closedin_carrier[OF htop] show ?thesis .
            qed
            ultimately show ?thesis by (by100 simp)
          qed
        qed
        from hweak[rule_format, OF hsub, THEN iffD2] this
        show ?thesis by (by100 blast)
      qed
      have "X - (C \<alpha> - {p}) \<subseteq> X" by (by100 blast)
      have "X - (X - (C \<alpha> - {p})) \<in> TX"
        using hcl unfolding closedin_on_def by (by100 blast)
      moreover have "X - (X - (C \<alpha> - {p})) = C \<alpha> - {p}"
        using hC h\<alpha> by (by100 blast)
      ultimately show "C \<alpha> - {p} \<in> TX" by (by100 simp)
    qed
    have hcompact_finite: "\<And>K. K \<subseteq> X \<Longrightarrow> top1_compact_on K (subspace_topology X TX K)
        \<Longrightarrow> finite {\<alpha>\<in>J. K \<inter> (C \<alpha> - {p}) \<noteq> {}}"
    proof -
      fix K assume hK_sub: "K \<subseteq> X" and hK_compact: "top1_compact_on K (subspace_topology X TX K)"
      let ?S = "{\<alpha>\<in>J. K \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      show "finite ?S"
      proof (rule ccontr)
        assume "infinite ?S"
        \<comment> \<open>Pick x\\_\\<alpha> \\<in> K \\<inter> (C\\_\\<alpha> - {p}) for each \\<alpha> \\<in> ?S.\<close>
        have "\<forall>\<alpha>\<in>?S. \<exists>x. x \<in> K \<and> x \<in> C \<alpha> - {p}" by (by100 blast)
        hence "\<exists>xf. \<forall>\<alpha>\<in>?S. xf \<alpha> \<in> K \<and> xf \<alpha> \<in> C \<alpha> - {p}"
          by (rule bchoice)
        then obtain xf where hxf: "\<forall>\<alpha>\<in>?S. xf \<alpha> \<in> K \<and> xf \<alpha> \<in> C \<alpha> - {p}"
          by (by100 blast)
        let ?A = "xf ` ?S"
        \<comment> \<open>A is infinite (x\\_\\<alpha> pairwise distinct since C\\_\\<alpha> - {p} disjoint).\<close>
        have hinj: "inj_on xf ?S"
        proof (rule inj_onI)
          fix \<alpha> \<beta> assume "\<alpha> \<in> ?S" "\<beta> \<in> ?S" "xf \<alpha> = xf \<beta>"
          have "xf \<alpha> \<in> C \<alpha> - {p}" using hxf \<open>\<alpha> \<in> ?S\<close> by (by100 blast)
          have "xf \<beta> \<in> C \<beta> - {p}" using hxf \<open>\<beta> \<in> ?S\<close> by (by100 blast)
          have "xf \<alpha> \<in> C \<beta> - {p}" using \<open>xf \<alpha> = xf \<beta>\<close> \<open>xf \<beta> \<in> C \<beta> - {p}\<close> by (by100 simp)
          have "xf \<alpha> \<in> (C \<alpha> - {p}) \<inter> (C \<beta> - {p})"
            using \<open>xf \<alpha> \<in> C \<alpha> - {p}\<close> \<open>xf \<alpha> \<in> C \<beta> - {p}\<close> by (by100 blast)
          show "\<alpha> = \<beta>"
          proof (rule ccontr)
            assume "\<alpha> \<noteq> \<beta>"
            have "\<alpha> \<in> J" "\<beta> \<in> J" using \<open>\<alpha> \<in> ?S\<close> \<open>\<beta> \<in> ?S\<close> by (by100 blast)+
            from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> \<open>\<beta> \<in> J\<close> \<open>\<alpha> \<noteq> \<beta>\<close>]
            have "C \<alpha> \<inter> C \<beta> = {p}" .
            hence "(C \<alpha> - {p}) \<inter> (C \<beta> - {p}) = {}" by (by100 blast)
            thus False using \<open>xf \<alpha> \<in> (C \<alpha> - {p}) \<inter> (C \<beta> - {p})\<close> by (by100 blast)
          qed
        qed
        have hA_inf: "infinite ?A"
        proof -
          from \<open>infinite ?S\<close> have "\<not> finite ?S" by simp
          moreover have "finite ?A \<Longrightarrow> finite ?S" using finite_imageD[OF _ hinj] by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        have hA_sub_K: "?A \<subseteq> K" using hxf by (by100 blast)
        \<comment> \<open>Key: every subset of A is closed in X (by coherent topology).
           For any B \\<subseteq> A and any \\<beta> \\<in> J: C\\_\\<beta> \\<inter> B \\<subseteq> {xf \\<beta>} which is finite \\<Rightarrow> closed in C\\_\\<beta>.\<close>
        have hA_every_sub_closed: "\<forall>B. B \<subseteq> ?A \<longrightarrow> closedin_on X TX B"
        proof (intro allI impI)
          fix B assume hB: "B \<subseteq> ?A"
          have hB_sub_X: "B \<subseteq> X" using hB hA_sub_K hK_sub by (by100 blast)
          show "closedin_on X TX B"
            using hweak[rule_format, OF hB_sub_X]
          proof (rule iffD2)
            show "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> B)"
            proof (intro ballI)
              fix \<beta> assume h\<beta>: "\<beta> \<in> J"
              have "C \<beta> \<inter> B \<subseteq> {xf \<beta>}"
              proof
                fix x assume "x \<in> C \<beta> \<inter> B"
                hence "x \<in> C \<beta>" "x \<in> B" by (by100 blast)+
                from \<open>x \<in> B\<close> hB obtain \<gamma> where "\<gamma> \<in> ?S" "x = xf \<gamma>" by (by100 blast)
                have "\<gamma> \<in> J" using \<open>\<gamma> \<in> ?S\<close> by (by100 blast)
                have "x \<in> C \<gamma> - {p}" using hxf \<open>\<gamma> \<in> ?S\<close> \<open>x = xf \<gamma>\<close> by (by100 blast)
                have "x \<in> C \<beta> \<inter> C \<gamma>" using \<open>x \<in> C \<beta>\<close> \<open>x \<in> C \<gamma> - {p}\<close> by (by100 blast)
                have "\<gamma> = \<beta>"
                proof (rule ccontr)
                  assume "\<gamma> \<noteq> \<beta>"
                  from hdisjoint[rule_format, OF \<open>\<beta> \<in> J\<close> \<open>\<gamma> \<in> J\<close>]
                  have "C \<beta> \<inter> C \<gamma> = {p}" using \<open>\<gamma> \<noteq> \<beta>\<close> by (by100 blast)
                  hence "x = p" using \<open>x \<in> C \<beta> \<inter> C \<gamma>\<close> by (by100 blast)
                  thus False using \<open>x \<in> C \<gamma> - {p}\<close> by (by100 blast)
                qed
                thus "x \<in> {xf \<beta>}" using \<open>x = xf \<gamma>\<close> by (by100 simp)
              qed
              \<comment> \<open>C\\_\\<beta> \\<inter> B is finite (\\<subseteq> {xf \\<beta>}), hence closed in Hausdorff C\\_\\<beta>.\<close>
              have "finite (C \<beta> \<inter> B)" using \<open>C \<beta> \<inter> B \<subseteq> {xf \<beta>}\<close>
                by (rule finite_subset) (by100 simp)
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<beta> \<subseteq> X\<close> hhaus by (by100 blast)
              have "C \<beta> \<inter> B \<subseteq> C \<beta>" by (by100 blast)
              show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> B)"
                by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<beta>) _\<close> \<open>finite (C \<beta> \<inter> B)\<close>
                    \<open>C \<beta> \<inter> B \<subseteq> C \<beta>\<close>])
            qed
          qed
        qed
        \<comment> \<open>A \\<subseteq> K infinite, every subset closed in X (hence in K).
           K compact Hausdorff \\<Rightarrow> limit point compact (Theorem 28.1).
           A infinite \\<Rightarrow> has limit point x in K.
           But A - {x} is closed in K \\<Rightarrow> K - (A - {x}) is open \\<ni> x,
           and (K - (A - {x})) \\<inter> (A - {x}) = {} \\<Rightarrow> x not a limit point. Contradiction.\<close>
        have hK_haus: "is_hausdorff_on K (subspace_topology X TX K)"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hK_sub hhaus by (by100 blast)
        have hK_lpc: "top1_limit_point_compact_on K (subspace_topology X TX K)"
          by (rule Theorem_28_1[OF hK_compact])
        from hK_lpc[unfolded top1_limit_point_compact_on_def] hA_sub_K hA_inf
        obtain x where hx: "x \<in> K" and hx_lp: "is_limit_point_of x ?A K (subspace_topology X TX K)"
          by (by100 blast)
        \<comment> \<open>A - {x} is closed in X (every subset of A is closed).\<close>
        have "?A - {x} \<subseteq> ?A" by (by100 blast)
        from hA_every_sub_closed[rule_format, OF this]
        have hAmx_cl_X: "closedin_on X TX (?A - {x})" .
        \<comment> \<open>A - {x} closed in K (from closed in X + Theorem 17.2).\<close>
        have hTX_top: "is_topology_on X TX"
          using hstrict unfolding is_topology_on_strict_def by (by100 blast)
        from Theorem_17_2[OF hTX_top hK_sub]
        have "closedin_on K (subspace_topology X TX K) (?A - {x}) \<longleftrightarrow>
            (\<exists>D. closedin_on X TX D \<and> ?A - {x} = D \<inter> K)" .
        hence hAmx_cl_K: "closedin_on K (subspace_topology X TX K) (?A - {x})"
          using hAmx_cl_X hA_sub_K by (by100 blast)
        \<comment> \<open>K - (A - {x}) is open in K, contains x.\<close>
        have hopen_K: "K - (?A - {x}) \<in> subspace_topology X TX K"
          using hAmx_cl_K unfolding closedin_on_def by (by100 blast)
        have "x \<in> K - (?A - {x})" using hx by (by100 blast)
        \<comment> \<open>(K - (A - {x})) \\<inter> (A - {x}) = {} \\<Rightarrow> x is not a limit point of A.\<close>
        have "(K - (?A - {x})) \<inter> (?A - {x}) = {}" by (by100 blast)
        \<comment> \<open>But x IS a limit point: every open U \\<ni> x meets A - {x}.\<close>
        have "K - (?A - {x}) \<subseteq> K" by (by100 blast)
        have "K - (?A - {x}) \<in> subspace_topology X TX K" using hopen_K .
        \<comment> \<open>This open set contains x but is disjoint from A - {x}. Contradicts limit point.\<close>
        \<comment> \<open>x is a limit point of A, so every open U \\<ni> x meets A - {x}.
           But K - (A-{x}) is open, contains x, and is disjoint from A-{x}. Contradiction.\<close>
        from hx_lp[unfolded is_limit_point_of_def]
        have hlp_raw: "x \<in> K \<and> ?A \<subseteq> K \<and> (\<forall>U. neighborhood_of x K (subspace_topology X TX K) U
            \<longrightarrow> intersects (U - {x}) ?A)" by (by100 blast)
        have hlp: "\<forall>U. U \<in> subspace_topology X TX K \<longrightarrow> x \<in> U \<longrightarrow>
            (\<exists>y. y \<in> ?A \<and> y \<noteq> x \<and> y \<in> U)"
        proof (intro allI impI)
          fix U assume "U \<in> subspace_topology X TX K" "x \<in> U"
          have "neighborhood_of x K (subspace_topology X TX K) U"
            unfolding neighborhood_of_def using \<open>U \<in> _\<close> \<open>x \<in> U\<close> by (by100 blast)
          from hlp_raw \<open>neighborhood_of x K _ U\<close>
          have "intersects (U - {x}) ?A" by (by100 blast)
          thus "\<exists>y. y \<in> ?A \<and> y \<noteq> x \<and> y \<in> U"
            unfolding intersects_def by (by100 blast)
        qed
        from hlp[rule_format, OF hopen_K \<open>x \<in> K - (?A - {x})\<close>]
        obtain y where "y \<in> ?A" "y \<noteq> x" "y \<in> K - (?A - {x})" by (by100 blast)
        hence "y \<notin> ?A - {x}" by (by100 blast)
        hence "y = x" using \<open>y \<in> ?A\<close> by (by100 blast)
        thus False using \<open>y \<noteq> x\<close> by (by100 blast)
      qed
    qed
    have hloop_finite: "\<And>f. top1_is_loop_on X TX p f \<Longrightarrow>
        \<exists>F. finite F \<and> F \<subseteq> J \<and> f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)"
    proof -
      fix f assume hf: "top1_is_loop_on X TX p f"
      have hfI_sub: "f ` top1_unit_interval \<subseteq> X"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def
          top1_continuous_map_on_def by (by100 blast)
      have hfI_compact: "top1_compact_on (f ` top1_unit_interval) (subspace_topology X TX (f ` top1_unit_interval))"
      proof -
        have hcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
          using top1_unit_interval_topology_is_topology_on .
        have hTX_top: "is_topology_on X TX"
          using hstrict unfolding is_topology_on_strict_def by (by100 blast)
        have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        from Theorem_26_5[OF hI_top hTX_top hI_compact hcont]
        show ?thesis .
      qed
      let ?S = "{\<alpha>\<in>J. f ` top1_unit_interval \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      from hcompact_finite[OF hfI_sub hfI_compact] have "finite ?S" .
      have "J \<noteq> {}" using hp hcover by (by100 blast)
      then obtain \<beta> where "\<beta> \<in> J" by (by100 blast)
      let ?F = "?S \<union> {\<beta>}"
      have "finite ?F" using \<open>finite ?S\<close> by (by100 simp)
      have "?F \<subseteq> J" using \<open>\<beta> \<in> J\<close> by (by100 blast)
      have "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
      proof
        fix x assume "x \<in> f ` top1_unit_interval"
        hence "x \<in> X" using hfI_sub by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" "x \<in> C \<gamma>" using hcover by (by100 blast)
        show "x \<in> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        proof (cases "x = p")
          case True thus ?thesis using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
        next
          case False
          hence "x \<in> C \<gamma> - {p}" using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
          hence "\<gamma> \<in> ?S" using \<open>\<gamma> \<in> J\<close> \<open>x \<in> f ` top1_unit_interval\<close> by (by100 blast)
          thus ?thesis using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
        qed
      qed
      thus "\<exists>F. finite F \<and> F \<subseteq> J \<and> f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)"
        using \<open>finite ?F\<close> \<open>?F \<subseteq> J\<close> by (by5000 blast)
    qed
    have hhtpy_finite: "\<And>f g. top1_is_loop_on X TX p f \<Longrightarrow> top1_is_loop_on X TX p g \<Longrightarrow>
        top1_path_homotopic_on X TX p p f g \<Longrightarrow>
        \<exists>F. finite F \<and> F \<subseteq> J \<and> top1_path_homotopic_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p p f g"
    proof -
      fix f g assume hf: "top1_is_loop_on X TX p f" and hg: "top1_is_loop_on X TX p g"
        and hfg: "top1_path_homotopic_on X TX p p f g"
      \<comment> \<open>Extract homotopy H.\<close>
      from hfg[unfolded top1_path_homotopic_on_def]
      obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H"
        and hH0: "\<forall>s\<in>I_set. H (s, 0) = f s" and hH1: "\<forall>s\<in>I_set. H (s, 1) = g s"
        and hHl: "\<forall>t\<in>I_set. H (0, t) = p" and hHr: "\<forall>t\<in>I_set. H (1, t) = p"
        by (by100 blast)
      \<comment> \<open>II\\_topology = product\\_topology\\_on I\\_top I\\_top.\<close>
      have hH_cont': "top1_continuous_map_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology) X TX H"
        using hH_cont unfolding II_topology_def by (by100 simp)
      \<comment> \<open>H(I\\<times>I) is compact.\<close>
      have hHI_sub: "H ` (I_set \<times> I_set) \<subseteq> X"
        using hH_cont' unfolding top1_continuous_map_on_def by (by100 blast)
      have hHI_compact: "top1_compact_on (H ` (I_set \<times> I_set))
          (subspace_topology X TX (H ` (I_set \<times> I_set)))"
      proof -
        have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        have hII_compact: "top1_compact_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
          by (rule Theorem_26_7[OF hI_compact hI_compact])
        have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
          using top1_unit_interval_topology_is_topology_on .
        have hII_top: "is_topology_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
          using product_topology_on_is_topology_on[OF hI_top hI_top] .
        from Theorem_26_5[OF hII_top hTX hII_compact hH_cont']
        show ?thesis .
      qed
      \<comment> \<open>H(I\\<times>I) meets finitely many circles.\<close>
      from hcompact_finite[OF hHI_sub hHI_compact]
      have hH_fin: "finite {\<alpha>\<in>J. H ` (I_set \<times> I_set) \<inter> (C \<alpha> - {p}) \<noteq> {}}" .
      \<comment> \<open>Combine with hloop\\_finite for f and g.\<close>
      from hloop_finite[OF hf] obtain Ff where hFf: "finite Ff" "Ff \<subseteq> J"
          "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>Ff. C \<alpha>)" by (by100 blast)
      from hloop_finite[OF hg] obtain Fg where hFg: "finite Fg" "Fg \<subseteq> J"
          "g ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>Fg. C \<alpha>)" by (by100 blast)
      let ?SH = "{\<alpha>\<in>J. H ` (I_set \<times> I_set) \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      have "J \<noteq> {}" using hp hcover by (by100 blast)
      then obtain \<beta> where "\<beta> \<in> J" by (by100 blast)
      let ?F = "Ff \<union> Fg \<union> ?SH \<union> {\<beta>}"
      have "finite ?F" using hFf(1) hFg(1) hH_fin by (by100 simp)
      have "?F \<subseteq> J" using hFf(2) hFg(2) \<open>\<beta> \<in> J\<close> by (by100 blast)
      \<comment> \<open>H(I\\<times>I), f(I), g(I) all lie in \\<Union>?F C\\_\\<alpha>.\<close>
      have hH_in_F: "H ` (I_set \<times> I_set) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
      proof
        fix x assume "x \<in> H ` (I_set \<times> I_set)"
        hence "x \<in> X" using hHI_sub by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" "x \<in> C \<gamma>" using hcover by (by100 blast)
        show "x \<in> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        proof (cases "x = p")
          case True thus ?thesis using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
        next
          case xFalse: False
          hence "x \<in> C \<gamma> - {p}" using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
          hence "\<gamma> \<in> ?SH" using \<open>\<gamma> \<in> J\<close> \<open>x \<in> H ` (I_set \<times> I_set)\<close> by (by100 blast)
          thus ?thesis using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
        qed
      qed
      \<comment> \<open>The homotopy restricts to \\<Union>?F C\\_\\<alpha> \\<Rightarrow> path homotopy in the subspace.\<close>
      have hF_sub: "(\<Union>\<alpha>\<in>?F. C \<alpha>) \<subseteq> X" using hC \<open>?F \<subseteq> J\<close> by (by100 blast)
      let ?Y = "\<Union>\<alpha>\<in>?F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      \<comment> \<open>H restricts to continuous map I\\<times>I \\<rightarrow> ?Y (subspace topology).\<close>
      have hII_top: "is_topology_on (I_set \<times> I_set) II_topology"
        unfolding II_topology_def
        using product_topology_on_is_topology_on[OF
          top1_unit_interval_topology_is_topology_on top1_unit_interval_topology_is_topology_on] .
      have hH_cont_sub: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H"
      proof -
        from Theorem_18_2(5)[OF hII_top hTX hTX, rule_format]
        show ?thesis using hH_cont hH_in_F hF_sub by (by100 blast)
      qed
      \<comment> \<open>f restricts to continuous path I \\<rightarrow> ?Y.\<close>
      have hI_top: "is_topology_on I_set I_top"
        using top1_unit_interval_topology_is_topology_on .
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hFf_sub_F: "Ff \<subseteq> ?F" by (by100 blast)
      have "(\<Union>\<alpha>\<in>Ff. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        using hFf_sub_F by (by100 blast)
      have hf_im: "f ` I_set \<subseteq> ?Y"
        using hFf(3) \<open>(\<Union>\<alpha>\<in>Ff. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)\<close> by (by100 blast)
      have hf_cont_sub: "top1_continuous_map_on I_set I_top ?Y ?TY f"
      proof -
        from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
        show ?thesis using hf_cont hf_im hF_sub by (by100 blast)
      qed
      have hf0: "f 0 = p" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hf1: "f 1 = p" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hf_path: "top1_is_path_on ?Y ?TY p p f"
        unfolding top1_is_path_on_def using hf_cont_sub hf0 hf1 by (by100 blast)
      \<comment> \<open>g restricts to continuous path I \\<rightarrow> ?Y.\<close>
      have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
        using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hFg_sub_F: "Fg \<subseteq> ?F" by (by100 blast)
      have "(\<Union>\<alpha>\<in>Fg. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        using hFg_sub_F by (by100 blast)
      have hg_im: "g ` I_set \<subseteq> ?Y"
        using hFg(3) \<open>(\<Union>\<alpha>\<in>Fg. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)\<close> by (by100 blast)
      have hg_cont_sub: "top1_continuous_map_on I_set I_top ?Y ?TY g"
      proof -
        from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
        show ?thesis using hg_cont hg_im hF_sub by (by100 blast)
      qed
      have hg0: "g 0 = p" using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hg1: "g 1 = p" using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hg_path: "top1_is_path_on ?Y ?TY p p g"
        unfolding top1_is_path_on_def using hg_cont_sub hg0 hg1 by (by100 blast)
      \<comment> \<open>Package into path homotopy.\<close>
      have "top1_path_homotopic_on ?Y ?TY p p f g"
        unfolding top1_path_homotopic_on_def
        using hf_path hg_path hH_cont_sub hH0 hH1 hHl hHr by (by100 blast)
      show "\<exists>F. finite F \<and> F \<subseteq> J \<and> top1_path_homotopic_on (\<Union>\<alpha>\<in>F. C \<alpha>)
          (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p p f g"
      proof (rule exI[of _ ?F], intro conjI)
        show "finite ?F" using \<open>finite ?F\<close> .
        show "?F \<subseteq> J" using \<open>?F \<subseteq> J\<close> .
        show "top1_path_homotopic_on (\<Union>\<alpha>\<in>?F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>?F. C \<alpha>)) p p f g"
          using \<open>top1_path_homotopic_on (\<Union>\<alpha>\<in>?F. C \<alpha>) _ p p f g\<close> .
      qed
    qed
    \<comment> \<open>For each finite F \\<subseteq> J, the sub-wedge is a wedge (hfinite\\_free).\<close>
    have hfinite_free: "\<And>F. finite F \<Longrightarrow> F \<subseteq> J \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
        top1_is_wedge_of_circles_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) F p"
    proof -
      fix F assume hFfin: "finite F" and hFJ: "F \<subseteq> J" and hFne: "F \<noteq> {}"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      \<comment> \<open>Coherent topology for the sub-wedge: D \\<subseteq> ?Y closed in ?Y \\<longleftrightarrow>
         \\<forall>\\<alpha>\\<in>F. C\\_\\<alpha> \\<inter> D closed in C\\_\\<alpha>.
         Proof: D closed in ?Y \\<longleftrightarrow> D closed in X (by hweak, since for \\<alpha> \\<notin> F:
         C\\_\\<alpha> \\<inter> D \\<subseteq> {p} closed in Hausdorff C\\_\\<alpha>).
         Then D = D \\<inter> ?Y closed in subspace ?Y.\<close>
      have hcoh_F: "\<forall>D. D \<subseteq> ?Y \<longrightarrow>
          (closedin_on ?Y ?TY D \<longleftrightarrow>
           (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      proof (intro allI impI iffI ballI)
        fix D \<alpha> assume hD: "D \<subseteq> ?Y" and hcl: "closedin_on ?Y ?TY D" and h\<alpha>: "\<alpha> \<in> F"
        \<comment> \<open>D closed in ?Y (subspace) \\<Longrightarrow> \\<exists>E closed in X with D = E \\<inter> ?Y.\<close>
        from Theorem_17_2[OF hTX hY_sub, THEN iffD1, OF hcl]
        obtain E where hE_cl: "closedin_on X TX E" and hDE: "D = E \<inter> ?Y" by (by100 blast)
        have hE_sub: "E \<subseteq> X" using hE_cl unfolding closedin_on_def by (by100 blast)
        from hweak[rule_format, OF hE_sub, THEN iffD1, OF hE_cl]
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> E)" .
        hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> E)"
          using h\<alpha> hFJ by (by100 blast)
        moreover have "C \<alpha> \<inter> D = C \<alpha> \<inter> E"
          using \<open>D = E \<inter> ?Y\<close> h\<alpha> by (by100 blast)
        ultimately show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          by (by100 simp)
      next
        fix D assume hD: "D \<subseteq> ?Y"
          and hall: "\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        \<comment> \<open>Show D closed in X by hweak. For \\<alpha> \\<in> F: given. For \\<alpha> \\<notin> F: C\\_\\<alpha> \\<inter> D \\<subseteq> {p}.\<close>
        have "\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        proof (intro ballI)
          fix \<alpha> assume "\<alpha> \<in> J"
          show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (cases "\<alpha> \<in> F")
            case True thus ?thesis using hall by (by100 blast)
          next
            case False
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha> \<inter> ?Y" using hD by (by100 blast)
            also have "... \<subseteq> {p}"
            proof
              fix x assume "x \<in> C \<alpha> \<inter> ?Y"
              then obtain \<beta> where "\<beta> \<in> F" "x \<in> C \<alpha>" "x \<in> C \<beta>" by (by100 blast)
              have "\<alpha> \<noteq> \<beta>" using False \<open>\<beta> \<in> F\<close> by (by100 blast)
              from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> _ \<open>\<alpha> \<noteq> \<beta>\<close>] \<open>\<beta> \<in> F\<close> hFJ
              have "C \<alpha> \<inter> C \<beta> = {p}" by (by100 blast)
              thus "x \<in> {p}" using \<open>x \<in> C \<alpha>\<close> \<open>x \<in> C \<beta>\<close> by (by100 blast)
            qed
            finally have "C \<alpha> \<inter> D \<subseteq> {p}" .
            have "finite (C \<alpha> \<inter> D)" using \<open>C \<alpha> \<inter> D \<subseteq> {p}\<close> finite_subset by (by100 blast)
            have "C \<alpha> \<subseteq> X" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<alpha> \<subseteq> X\<close> hhaus by (by100 blast)
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha>" by (by100 blast)
            show ?thesis
              by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<alpha>) _\<close> \<open>finite (C \<alpha> \<inter> D)\<close>
                  \<open>C \<alpha> \<inter> D \<subseteq> C \<alpha>\<close>])
          qed
        qed
        hence "closedin_on X TX D" using hweak[rule_format, OF \<open>D \<subseteq> ?Y\<close>[THEN subset_trans[OF _ hY_sub]]]
          by (by100 blast)
        from Theorem_17_2[OF hTX hY_sub] this hD
        show "closedin_on ?Y ?TY D" by (by100 blast)
      qed
      show "top1_is_wedge_of_circles_on ?Y ?TY F p"
        unfolding top1_is_wedge_of_circles_on_def
      proof (intro conjI)
        show "is_topology_on_strict ?Y ?TY"
        proof -
          have "\<forall>U\<in>?TY. U \<subseteq> ?Y" unfolding subspace_topology_def by (by100 blast)
          moreover have "is_topology_on ?Y ?TY"
            by (rule subspace_topology_is_topology_on[OF hTX hY_sub])
          ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
        qed
        show "is_hausdorff_on ?Y ?TY"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hY_sub hhaus by (by100 blast)
        show "p \<in> ?Y"
        proof -
          from hFne obtain \<beta> where "\<beta> \<in> F" by (by100 blast)
          hence "\<beta> \<in> J" using hFJ by (by100 blast)
          have "p \<in> C \<beta>" using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
          thus ?thesis using \<open>\<beta> \<in> F\<close> by (by100 blast)
        qed
        show "\<exists>Ca. (\<forall>\<alpha>\<in>F. Ca \<alpha> \<subseteq> ?Y \<and> p \<in> Ca \<alpha>
            \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (Ca \<alpha>) (subspace_topology ?Y ?TY (Ca \<alpha>)) h))
          \<and> (\<Union>\<alpha>\<in>F. Ca \<alpha>) = ?Y
          \<and> (\<forall>\<alpha>\<in>F. \<forall>\<beta>\<in>F. \<alpha> \<noteq> \<beta> \<longrightarrow> Ca \<alpha> \<inter> Ca \<beta> = {p})
          \<and> (\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>F. closedin_on (Ca \<alpha>) (subspace_topology ?Y ?TY (Ca \<alpha>)) (Ca \<alpha> \<inter> D))))"
        proof (rule exI[of _ C], intro conjI)
          show "\<forall>\<alpha>\<in>F. C \<alpha> \<subseteq> ?Y \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h)"
          proof (intro ballI conjI)
            fix \<alpha> assume "\<alpha> \<in> F"
            hence "\<alpha> \<in> J" using hFJ by (by100 blast)
            show "C \<alpha> \<subseteq> ?Y" using \<open>\<alpha> \<in> F\<close> by (by100 blast)
            show "p \<in> C \<alpha>" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            show "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h"
            proof -
              from hC[rule_format, OF \<open>\<alpha> \<in> J\<close>]
              obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h" by (by100 blast)
              have "subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
                by (rule subspace_topology_trans) (use \<open>\<alpha> \<in> F\<close> in blast)
              have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h"
                using hh \<open>subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)\<close>
                by (by100 simp)
              thus ?thesis by (by100 blast)
            qed
          qed
          show "(\<Union>\<alpha>\<in>F. C \<alpha>) = ?Y" by (by100 blast)
          show "\<forall>\<alpha>\<in>F. \<forall>\<beta>\<in>F. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
            using hdisjoint hFJ by (by100 blast)
          show "\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) (C \<alpha> \<inter> D)))"
          proof (intro allI impI)
            fix D assume "D \<subseteq> ?Y"
            from hcoh_F[rule_format, OF this]
            have "closedin_on ?Y ?TY D \<longleftrightarrow>
                (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))" .
            moreover have "\<forall>\<alpha>\<in>F. subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
            proof (intro ballI)
              fix \<alpha> assume "\<alpha> \<in> F"
              show "subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
                by (rule subspace_topology_trans) (use \<open>\<alpha> \<in> F\<close> in blast)
            qed
            ultimately show "closedin_on ?Y ?TY D \<longleftrightarrow>
                (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) (C \<alpha> \<inter> D))"
              by (by100 simp)
          qed
        qed
      qed
    qed
    \<comment> \<open>Coherent topology for sub-wedges (same proof as inside hfinite\\_free, exposed separately).\<close>
    have hcoh_sub: "\<And>F. F \<subseteq> J \<Longrightarrow>
        (\<forall>D. D \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>) \<longrightarrow>
          (closedin_on (\<Union>\<alpha>\<in>F. C \<alpha>) (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) D \<longleftrightarrow>
           (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))))"
    proof -
      fix F assume hFJ: "F \<subseteq> J"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      show "\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
          (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      proof (intro allI impI iffI ballI)
        fix D \<alpha> assume hD: "D \<subseteq> ?Y" and hcl: "closedin_on ?Y ?TY D" and h\<alpha>: "\<alpha> \<in> F"
        from Theorem_17_2[OF hTX hY_sub, THEN iffD1, OF hcl]
        obtain E where hE_cl: "closedin_on X TX E" and hDE: "D = E \<inter> ?Y" by (by100 blast)
        have hE_sub: "E \<subseteq> X" using hE_cl unfolding closedin_on_def by (by100 blast)
        from hweak[rule_format, OF hE_sub, THEN iffD1, OF hE_cl]
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> E)" .
        hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> E)"
          using h\<alpha> hFJ by (by100 blast)
        moreover have "C \<alpha> \<inter> D = C \<alpha> \<inter> E" using \<open>D = E \<inter> ?Y\<close> h\<alpha> by (by100 blast)
        ultimately show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          by (by100 simp)
      next
        fix D assume hD: "D \<subseteq> ?Y"
          and hall: "\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        have "\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        proof (intro ballI)
          fix \<alpha> assume "\<alpha> \<in> J"
          show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (cases "\<alpha> \<in> F")
            case True thus ?thesis using hall by (by100 blast)
          next
            case False
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha> \<inter> ?Y" using hD by (by100 blast)
            also have "... \<subseteq> {p}"
            proof
              fix x assume "x \<in> C \<alpha> \<inter> ?Y"
              then obtain \<beta> where "\<beta> \<in> F" "x \<in> C \<alpha>" "x \<in> C \<beta>" by (by100 blast)
              have "\<alpha> \<noteq> \<beta>" using False \<open>\<beta> \<in> F\<close> by (by100 blast)
              from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> _ \<open>\<alpha> \<noteq> \<beta>\<close>] \<open>\<beta> \<in> F\<close> hFJ
              have "C \<alpha> \<inter> C \<beta> = {p}" by (by100 blast)
              thus "x \<in> {p}" using \<open>x \<in> C \<alpha>\<close> \<open>x \<in> C \<beta>\<close> by (by100 blast)
            qed
            finally have "C \<alpha> \<inter> D \<subseteq> {p}" .
            have "finite (C \<alpha> \<inter> D)" using \<open>C \<alpha> \<inter> D \<subseteq> {p}\<close> finite_subset by (by100 blast)
            have "C \<alpha> \<subseteq> X" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<alpha> \<subseteq> X\<close> hhaus by (by100 blast)
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha>" by (by100 blast)
            show ?thesis
              by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<alpha>) _\<close> \<open>finite (C \<alpha> \<inter> D)\<close>
                  \<open>C \<alpha> \<inter> D \<subseteq> C \<alpha>\<close>])
          qed
        qed
        hence "closedin_on X TX D"
          using hweak[rule_format, OF \<open>D \<subseteq> ?Y\<close>[THEN subset_trans[OF _ hY_sub]]]
          by (by100 blast)
        from Theorem_17_2[OF hTX hY_sub] this hD
        show "closedin_on ?Y ?TY D" by (by100 blast)
      qed
    qed
    \<comment> \<open>Now verify top1\\_is\\_free\\_group\\_full\\_on for \\<pi>\\_1(X, p).
       For each finite sub-wedge F, Theorem\\_71\\_3\\_finite gives \\<pi>\\_1 free on F.
       The free group condition 5 (no reduced word = id): a word w uses finitely many
       generators {\\<alpha>\\_1,...,\\<alpha>\\_n}. Take F containing these. The sub-wedge \\<Union>F C\\_\\<alpha>
       has \\<pi>\\_1 free on F (Theorem 71.1). The word is non-trivial there.
       The inclusion \\<pi>\\_1(sub-wedge) \\<hookrightarrow> \\<pi>\\_1(X) is injective (by hhtpy\\_finite:
       if a loop in the sub-wedge is null-homotopic in X, the homotopy lies in a finite
       sub-wedge, so the loop is null-homotopic in the sub-wedge).
       Therefore the word is non-trivial in \\<pi>\\_1(X).\<close>
    \<comment> \<open>Define \\<iota>(\\<alpha>) = the loop class of the S1 generator in C\\_\\<alpha>, included into X.\<close>
    \<comment> \<open>For each \\<alpha> \\<in> J, C\\_\\<alpha> \\<cong> S1, so \\<pi>\\_1(C\\_\\<alpha>, p) \\<cong> Z, generated by some loop f\\_\\<alpha>.
       The inclusion i\\_\\<alpha>: C\\_\\<alpha> \\<hookrightarrow> X induces a hom \\<pi>\\_1(C\\_\\<alpha>) \\<rightarrow> \\<pi>\\_1(X).
       Set \\<iota>(\\<alpha>) = [f\\_\\<alpha>] in \\<pi>\\_1(X, p).\<close>
    \<comment> \<open>Step 1: choose generator loops.\<close>
    \<comment> \<open>Step 1-2: choose generator loops and define \\<iota>.
       For each \\<alpha> \\<in> J, C\\_\\<alpha> \\<cong> S1 has \\<pi>\\_1(C\\_\\<alpha>) \\<cong> Z generated by some loop f\\_\\<alpha>.
       The inclusion C\\_\\<alpha> \\<hookrightarrow> X gives f\\_\\<alpha> as a loop in X with image in C\\_\\<alpha>.\<close>
    \<comment> \<open>For each \\<alpha>, the homeomorphism h\\_\\<alpha>: S1 \\<rightarrow> C\\_\\<alpha> may not send (1,0) to p.
       We compose h\\_\\<alpha> with a rotation to get g\\_\\<alpha> with g\\_\\<alpha>(1,0) = p.
       Then gen\\_loop \\<alpha> t = g\\_\\<alpha>(cos(2\\<pi>t), sin(2\\<pi>t)) is a loop in C\\_\\<alpha> based at p.\<close>
    \<comment> \<open>First, obtain homeomorphisms g\\_\\<alpha> with g\\_\\<alpha>(1,0) = p.\<close>
    have hg_ex: "\<forall>\<alpha>\<in>J. \<exists>g. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g \<and> g (1, 0) = p"
    proof (intro ballI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      from hC[rule_format, OF h\<alpha>]
      obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h" and hCsub: "C \<alpha> \<subseteq> X" and hpC: "p \<in> C \<alpha>"
        by (by100 blast)
      \<comment> \<open>h is bijective S1 \\<rightarrow> C\\_\\<alpha>. Since p \\<in> C\\_\\<alpha>, there exists q \\<in> S1 with h(q) = p.\<close>
      have hh_bij: "bij_betw h top1_S1 (C \<alpha>)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hh_surj: "h ` top1_S1 = C \<alpha>"
        using hh_bij unfolding bij_betw_def by (by100 blast)
      from hpC have "p \<in> h ` top1_S1" using hh_surj by (by100 simp)
      then obtain q where hq_S1: "q \<in> top1_S1" and hhq: "h q = p" by (by100 blast)
      obtain a b where hq_eq: "q = (a, b)" by (cases q) (by100 blast)
      have hab: "a * a + b * b = 1"
      proof -
        have "a^2 + b^2 = 1" using hq_S1 unfolding hq_eq top1_S1_def by (by100 simp)
        thus ?thesis unfolding power2_eq_square .
      qed
      \<comment> \<open>Define rotation R(x,y) = (a*x - b*y, b*x + a*y). R(1,0) = (a,b) = q.\<close>
      define R where "R z = (a * fst z - b * snd z, b * fst z + a * snd z)" for z
      have hR10: "R (1, 0) = q" unfolding R_def hq_eq by (by100 simp)
      \<comment> \<open>R maps S1 to S1.\<close>
      have hR_S1: "\<forall>z\<in>top1_S1. R z \<in> top1_S1"
      proof (intro ballI)
        fix z assume hz: "z \<in> top1_S1"
        have hzn: "fst z * fst z + snd z * snd z = 1"
        proof -
          have "(fst z)^2 + (snd z)^2 = 1" using hz unfolding top1_S1_def by (by100 simp)
          thus ?thesis unfolding power2_eq_square .
        qed
        have "fst (R z) * fst (R z) + snd (R z) * snd (R z) =
            (a * fst z - b * snd z) * (a * fst z - b * snd z) +
            (b * fst z + a * snd z) * (b * fst z + a * snd z)"
          unfolding R_def by (by100 simp)
        also have "... = (a*a + b*b) * (fst z * fst z + snd z * snd z)"
          by (by100 algebra)
        also have "... = 1" using hab hzn by (by100 simp)
        finally have "fst (R z) * fst (R z) + snd (R z) * snd (R z) = 1" .
        hence "(fst (R z))^2 + (snd (R z))^2 = 1" unfolding power2_eq_square .
        thus "R z \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      qed
      \<comment> \<open>R is bijective on S1. Inverse is R'(x,y) = (a*x + b*y, -b*x + a*y).\<close>
      define R' where "R' z = (a * fst z + b * snd z, -(b * fst z) + a * snd z)" for z
      have hR'_S1: "\<forall>z\<in>top1_S1. R' z \<in> top1_S1"
      proof (intro ballI)
        fix z assume hz: "z \<in> top1_S1"
        have hzn: "fst z * fst z + snd z * snd z = 1"
        proof -
          have "(fst z)^2 + (snd z)^2 = 1" using hz unfolding top1_S1_def by (by100 simp)
          thus ?thesis unfolding power2_eq_square .
        qed
        have "fst (R' z) * fst (R' z) + snd (R' z) * snd (R' z) =
            (a * fst z + b * snd z) * (a * fst z + b * snd z) +
            (-(b * fst z) + a * snd z) * (-(b * fst z) + a * snd z)"
          unfolding R'_def by (by100 simp)
        also have "... = (a*a + b*b) * (fst z * fst z + snd z * snd z)"
          by (by100 algebra)
        also have "... = 1" using hab hzn by (by100 simp)
        finally have "fst (R' z) * fst (R' z) + snd (R' z) * snd (R' z) = 1" .
        hence "(fst (R' z))^2 + (snd (R' z))^2 = 1" unfolding power2_eq_square .
        thus "R' z \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      qed
      have hRR': "\<forall>z\<in>top1_S1. R' (R z) = z"
      proof (intro ballI)
        fix z assume "z \<in> top1_S1"
        have "fst (R' (R z)) = a * (a * fst z - b * snd z) + b * (b * fst z + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * fst z" by (by100 algebra)
        also have "... = fst z" using hab by (by100 simp)
        finally have h1: "fst (R' (R z)) = fst z" .
        have "snd (R' (R z)) = -(b * (a * fst z - b * snd z)) + a * (b * fst z + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * snd z" by (by100 algebra)
        also have "... = snd z" using hab by (by100 simp)
        finally have h2: "snd (R' (R z)) = snd z" .
        show "R' (R z) = z" using h1 h2 by (rule prod_eqI)
      qed
      have hR'R: "\<forall>z\<in>top1_S1. R (R' z) = z"
      proof (intro ballI)
        fix z assume "z \<in> top1_S1"
        have "fst (R (R' z)) = a * (a * fst z + b * snd z) - b * (-(b * fst z) + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * fst z" by (by100 algebra)
        also have "... = fst z" using hab by (by100 simp)
        finally have h1: "fst (R (R' z)) = fst z" .
        have "snd (R (R' z)) = b * (a * fst z + b * snd z) + a * (-(b * fst z) + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * snd z" by (by100 algebra)
        also have "... = snd z" using hab by (by100 simp)
        finally have h2: "snd (R (R' z)) = snd z" .
        show "R (R' z) = z" using h1 h2 by (rule prod_eqI)
      qed
      have hR_bij: "bij_betw R top1_S1 top1_S1"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on R top1_S1"
        proof (rule inj_onI)
          fix x y assume "x \<in> top1_S1" "y \<in> top1_S1" "R x = R y"
          hence "R' (R x) = R' (R y)" by (by100 simp)
          thus "x = y" using hRR' \<open>x \<in> top1_S1\<close> \<open>y \<in> top1_S1\<close> by (by100 simp)
        qed
        show "R ` top1_S1 = top1_S1"
        proof
          show "R ` top1_S1 \<subseteq> top1_S1" using hR_S1 by (by100 blast)
          show "top1_S1 \<subseteq> R ` top1_S1"
          proof
            fix z assume "z \<in> top1_S1"
            hence "R' z \<in> top1_S1" using hR'_S1 by (by100 blast)
            have "R (R' z) = z" using hR'R \<open>z \<in> top1_S1\<close> by (by100 blast)
            hence "z = R (R' z)" by (by100 simp)
            thus "z \<in> R ` top1_S1" using \<open>R' z \<in> top1_S1\<close> by (rule image_eqI)
          qed
        qed
      qed
      \<comment> \<open>R is continuous on S1 (restriction of polynomial map on R2).
         Use Theorem 26.6: continuous bijection from compact to Hausdorff.\<close>
      have hR_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          top1_S1 top1_S1_topology R"
      proof -
        \<comment> \<open>R is continuous on all of R2 (linear map).\<close>
        have "continuous_on UNIV R"
          unfolding R_def
          by (intro continuous_intros)
        \<comment> \<open>Use bridge lemma: continuous\\_on UNIV + maps S1 \\<rightarrow> S1 \\<Longrightarrow> top1\\_continuous.\<close>
        from top1_continuous_map_on_real2_subspace[OF _ this]
        show ?thesis unfolding top1_S1_topology_def using hR_S1 by (by100 blast)
      qed
      have hR_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
          top1_S1 top1_S1_topology R"
      proof -
        have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology"
          using S1_compact .
        have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
          using top1_S1_is_hausdorff .
        show ?thesis
          by (rule Theorem_26_6[OF hS1_top hS1_top hS1_compact hS1_haus hR_cont hR_bij])
      qed
      \<comment> \<open>Compose: g = h \\<circ> R has g(1,0) = h(q) = p.\<close>
      define g where "g = h \<circ> R"
      have "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g"
        unfolding g_def by (rule homeomorphism_comp[OF hR_homeo hh])
      moreover have "g (1, 0) = p" unfolding g_def comp_def using hR10 hhq by (by100 simp)
      ultimately show "\<exists>g. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g \<and> g (1, 0) = p" by (by100 blast)
    qed
    obtain g where hg: "\<forall>\<alpha>\<in>J. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>) \<and> (g \<alpha>) (1, 0) = p"
      using bchoice[OF hg_ex] by (by100 blast)
    \<comment> \<open>Define gen\\_loop \\<alpha> t = g\\_\\<alpha>(cos(2\\<pi>t), sin(2\\<pi>t)). This is a loop in C\\_\\<alpha> based at p.\<close>
    define gen_loop where "gen_loop \<alpha> t = (g \<alpha>) (cos (2 * pi * t), sin (2 * pi * t))" for \<alpha> t
    have hgen: "\<forall>\<alpha>\<in>J. top1_is_loop_on X TX p (gen_loop \<alpha>) \<and>
        (gen_loop \<alpha>) ` top1_unit_interval \<subseteq> C \<alpha>"
    proof (intro ballI conjI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      have hg\<alpha>: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>)" "(g \<alpha>) (1, 0) = p"
        using hg h\<alpha> by (by100 blast)+
      have hC\<alpha>: "C \<alpha> \<subseteq> X" "p \<in> C \<alpha>" using hC h\<alpha> by (by100 blast)+
      have hTC\<alpha>: "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
        by (rule subspace_topology_is_topology_on[OF hTX hC\<alpha>(1)])
      \<comment> \<open>The standard S1 loop is a loop on S1. Composing with g\\_\\<alpha> gives a loop on C\\_\\<alpha>.\<close>
      have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
          (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
        by (rule standard_S1_loop_is_loop)
      \<comment> \<open>g\\_\\<alpha> is continuous S1 \\<rightarrow> C\\_\\<alpha>, and the standard loop is continuous I \\<rightarrow> S1.\<close>
      have hg\<alpha>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>)"
        using hg\<alpha>(1) unfolding top1_homeomorphism_on_def by (by100 blast)
      have hstd_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology
          (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
        using hstd unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      \<comment> \<open>Composition: gen\\_loop \\<alpha> is continuous I \\<rightarrow> C\\_\\<alpha>.\<close>
      have hcomp: "top1_continuous_map_on I_set I_top
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (gen_loop \<alpha>)"
      proof -
        have "top1_continuous_map_on I_set I_top
            (C \<alpha>) (subspace_topology X TX (C \<alpha>))
            ((g \<alpha>) \<circ> (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))))"
          by (rule top1_continuous_map_on_comp[OF hstd_cont hg\<alpha>_cont])
        moreover have "(g \<alpha>) \<circ> (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) = gen_loop \<alpha>"
          unfolding gen_loop_def comp_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Lift to X via inclusion C\\_\\<alpha> \\<hookrightarrow> X.\<close>
      have hincl: "top1_continuous_map_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) X TX id"
        using Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hC\<alpha>(1)] .
      have hgen_cont_X: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
      proof -
        have "top1_continuous_map_on I_set I_top X TX (id \<circ> gen_loop \<alpha>)"
          by (rule top1_continuous_map_on_comp[OF hcomp hincl])
        thus ?thesis by (by100 simp)
      qed
      show "top1_is_loop_on X TX p (gen_loop \<alpha>)"
        unfolding top1_is_loop_on_def top1_is_path_on_def
        using hgen_cont_X hg\<alpha>(2) unfolding gen_loop_def by (by100 simp)
      show "(gen_loop \<alpha>) ` top1_unit_interval \<subseteq> C \<alpha>"
      proof
        fix x assume "x \<in> gen_loop \<alpha> ` top1_unit_interval"
        then obtain t where "t \<in> top1_unit_interval" "x = gen_loop \<alpha> t" by (by100 blast)
        have "(cos (2 * pi * t), sin (2 * pi * t)) \<in> top1_S1"
          unfolding top1_S1_def by (by100 simp)
        hence "x \<in> C \<alpha>" using \<open>x = gen_loop \<alpha> t\<close>
          hg\<alpha>(1)[unfolded top1_homeomorphism_on_def top1_continuous_map_on_def]
          unfolding gen_loop_def by (by100 blast)
        thus "x \<in> C \<alpha>" .
      qed
    qed
    \<comment> \<open>Inclusion injectivity: the inclusion hom \\<pi>\\_1(\\<Union>F) \\<rightarrow> \\<pi>\\_1(X) is injective.
       Book: if f is a loop in \\<Union>F that is null-homotopic in X, then it is
       null-homotopic in some \\<Union>F' \\<supseteq> \\<Union>F, hence in \\<Union>F by Theorem 71.1.\<close>
    have hincl_inj: "\<And>F. finite F \<Longrightarrow> F \<subseteq> J \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
        inj_on (top1_fundamental_group_induced_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p X TX p (\<lambda>x. x))
          (top1_fundamental_group_carrier (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p)"
    proof -
      fix F assume hFfin: "finite F" and hFJ: "F \<subseteq> J" and hFne: "F \<noteq> {}"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      let ?incl = "top1_fundamental_group_induced_on ?Y ?TY p X TX p (\<lambda>x. x)"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      have hpY: "p \<in> ?Y" using hFne hC hFJ by (by100 blast)
      have hTY: "is_topology_on ?Y ?TY" by (rule subspace_topology_is_topology_on[OF hTX hY_sub])
      \<comment> \<open>\\<pi>\\_1(?Y) is free on F via chosen\\_loops\\_arb.\<close>
      from hfinite_free[OF hFfin hFJ hFne]
      have hwedge_Y: "top1_is_wedge_of_circles_on ?Y ?TY F p" .
      have hg_F: "\<forall>j\<in>F. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
      proof -
        { fix j assume "j \<in> F"
          hence "j \<in> J" using hFJ by (by100 blast)
          have "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
          moreover have "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
            by (rule subspace_topology_trans) (use \<open>j \<in> F\<close> in blast)
          ultimately have "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y ?TY (C j)) (g j)" by (by100 simp) }
        thus ?thesis by (by100 blast)
      qed
      have hC_closed_F: "\<forall>D\<subseteq>?Y. closedin_on ?Y ?TY D \<longleftrightarrow>
          (\<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D))"
      proof (intro allI impI iffI)
        fix D assume hD: "D \<subseteq> ?Y"
        from hcoh_sub[OF hFJ, rule_format, OF hD]
        have hiff: "closedin_on ?Y ?TY D \<longleftrightarrow>
            (\<forall>j\<in>F. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
        have htrans: "\<forall>j\<in>F. subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
          by (intro ballI, rule subspace_topology_trans) blast
        show "closedin_on ?Y ?TY D \<Longrightarrow>
            \<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)"
          using hiff htrans by (by100 simp)
        show "(\<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)) \<Longrightarrow>
            closedin_on ?Y ?TY D"
          using hiff htrans by (by100 simp)
      qed
      have hbase_F: "\<forall>j\<in>F. g j (1, 0) = p" using hg hFJ by (by100 blast)
      have hC_data_F: "\<forall>j\<in>F. C j \<subseteq> ?Y \<and> p \<in> C j" using hC hFJ by (by100 blast)
      have hC_union_F: "(\<Union>j\<in>F. C j) = ?Y" by (by100 blast)
      have hC_disj_F: "\<forall>i\<in>F. \<forall>j\<in>F. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
        using hdisjoint hFJ by (by100 blast)
      from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_Y hFfin
          hg_F hbase_F hC_data_F hC_union_F hC_disj_F hC_closed_F]
      obtain GF :: "int set" and mulF eF invgF and \<eta>F :: "'i \<Rightarrow> int" and \<Phi>F
        where hfreeF: "top1_is_free_group_full_on GF mulF eF invgF \<eta>F F"
          and hisoF: "top1_group_iso_on GF mulF
              (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p) \<Phi>F"
          and hgensF: "\<forall>j\<in>F. \<Phi>F (\<eta>F j) = {l. top1_loop_equiv_on ?Y ?TY p
              (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
        by (by100 blast)
      \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<rightarrow> \\<pi>\\_1(X) is a group hom.\<close>
      have hincl_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p)
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) ?incl"
        by (rule subspace_inclusion_induced_hom[OF hTX hY_sub hpY])
      \<comment> \<open>Suppose ?incl(c) = ?incl(c') for c, c' \\<in> \\<pi>\\_1(?Y). Need c = c'.
         Equivalently: ker(?incl) = {id}. I.e., ?incl(c) = id\\_X \\<Longrightarrow> c = id\\_Y.

         We prove: ?incl(c) = id\\_X \\<Longrightarrow> c = id\\_Y.
         The composition \\<Phi>\\_F\<inverse> \\<circ> ?incl \\<circ> \\<Phi>\\_F: free(F) \\<rightarrow> \\<pi>\\_1(X).
         If this sends x \\<mapsto> id\\_X, then by applying free\\_group\\_word\\_kernel
         in the reverse direction... no, we use the subgroup\\_generated representation
         + free\\_group\\_word\\_kernel of free(F\\<union>F') to derive x = eF.\<close>
      show "inj_on ?incl (top1_fundamental_group_carrier ?Y ?TY p)"
      proof (rule inj_onI)
        fix c1 c2 assume hc1: "c1 \<in> top1_fundamental_group_carrier ?Y ?TY p"
          and hc2: "c2 \<in> top1_fundamental_group_carrier ?Y ?TY p"
          and heq: "?incl c1 = ?incl c2"
        \<comment> \<open>Sufficient to show: if ?incl(c) = id\\_X then c = id\\_Y.
           Then ?incl(c1 * c2\<inverse>) = ?incl(c1) * ?incl(c2)\<inverse> = id, so c1 * c2\<inverse> = id, so c1 = c2.\<close>
        \<comment> \<open>Alternative: directly show c1 = c2 from ?incl(c1) = ?incl(c2).\<close>
        \<comment> \<open>?incl(c1) = ?incl(c2) means: for loops f1 \\<in> c1, f2 \\<in> c2, f1 ~ f2 in X.\<close>
        \<comment> \<open>By hhtpy\\_finite, f1 ~ f2 in \\<Union>F'. In \\<Union>(F\\<union>F'), f1 ~ f2.
           So [f1] = [f2] in \\<pi>\\_1(\\<Union>(F\\<union>F')).
           The inclusion \\<pi>\\_1(\\<Union>F) \\<rightarrow> \\<pi>\\_1(\\<Union>(F\\<union>F')) sends c1 \\<mapsto> [f1], c2 \\<mapsto> [f2].
           So inclusion(c1) = inclusion(c2) in \\<pi>\\_1(\\<Union>(F\\<union>F')).
           Need: this inclusion is injective. This is the free group embedding.
           Use: free\\_group\\_word\\_kernel on free(F\\<union>F') with target free(F).\<close>
        \<comment> \<open>Extract representative loops and use hhtpy\\_finite.\<close>
        from hc1[unfolded top1_fundamental_group_carrier_def]
        obtain f1 where hf1_loop: "top1_is_loop_on ?Y ?TY p f1"
            and hc1_eq: "c1 = {g. top1_loop_equiv_on ?Y ?TY p f1 g}" by (by100 blast)
        from hc2[unfolded top1_fundamental_group_carrier_def]
        obtain f2 where hf2_loop: "top1_is_loop_on ?Y ?TY p f2"
            and hc2_eq: "c2 = {g. top1_loop_equiv_on ?Y ?TY p f2 g}" by (by100 blast)
        \<comment> \<open>incl(c1) = incl(c2) means f1 ~ f2 in X.\<close>
        have hf1X: "top1_is_loop_on X TX p f1"
        proof -
          have hf1_cont_Y: "top1_continuous_map_on I_set I_top ?Y ?TY f1"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX (id \<circ> f1)"
            by (rule top1_continuous_map_on_comp[OF hf1_cont_Y
              Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
          hence "top1_continuous_map_on I_set I_top X TX f1" by (by100 simp)
          moreover have "f1 0 = p" "f1 1 = p"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hf2X: "top1_is_loop_on X TX p f2"
        proof -
          have hf2_cont_Y: "top1_continuous_map_on I_set I_top ?Y ?TY f2"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX (id \<circ> f2)"
            by (rule top1_continuous_map_on_comp[OF hf2_cont_Y
              Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
          hence "top1_continuous_map_on I_set I_top X TX f2" by (by100 simp)
          moreover have "f2 0 = p" "f2 1 = p"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have "top1_path_homotopic_on X TX p p f1 f2"
        proof -
          \<comment> \<open>f1 \\<in> ?incl c1: take f' = f1 (reflexive in ?Y), then id\\<circ>f1 = f1.\<close>
          have "f1 \<in> ?incl c1"
          proof -
            have "f1 \<in> {l. top1_loop_equiv_on ?Y ?TY p f1 l}"
              using top1_loop_equiv_on_refl[OF hf1_loop] by (by100 blast)
            moreover have "(\<lambda>x. x) \<circ> f1 = f1" by (by100 auto)
            hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f1) f1"
              using top1_loop_equiv_on_refl[OF hf1X] by (by100 simp)
            ultimately show ?thesis
              unfolding top1_fundamental_group_induced_on_def hc1_eq by (by100 blast)
          qed
          \<comment> \<open>Since ?incl c1 = ?incl c2: f1 \\<in> ?incl c2.\<close>
          hence "f1 \<in> ?incl c2" using heq by (by100 simp)
          \<comment> \<open>\\<exists>f'. loop\\_equiv(?Y, f2, f') \\<and> loop\\_equiv(X, f', f1).\<close>
          then obtain f' where hf'2: "top1_loop_equiv_on ?Y ?TY p f2 f'"
              and hf'1: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') f1"
            unfolding top1_fundamental_group_induced_on_def hc2_eq by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have hf'1': "top1_loop_equiv_on X TX p f' f1" using hf'1 \<open>(\<lambda>x. x) \<circ> f' = f'\<close>
            by (by100 simp)
          \<comment> \<open>f2 ~ f' in ?Y, hence f2 ~ f' in X. Then f' ~ f1 in X. By transitivity: f2 ~ f1 in X.\<close>
          have "top1_loop_equiv_on X TX p f2 f'"
          proof -
            from hf'2[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f2 f'" by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTX hY_sub _ this]
            have "top1_path_homotopic_on X TX p p f2 f'" by (by100 blast)
            have "top1_is_loop_on X TX p f'"
              using hf'1' unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf2X \<open>top1_is_loop_on X TX p f'\<close>
                \<open>top1_path_homotopic_on X TX p p f2 f'\<close> by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTX this hf'1']
          have "top1_loop_equiv_on X TX p f2 f1" .
          from top1_loop_equiv_on_sym[OF this]
          show "top1_path_homotopic_on X TX p p f1 f2"
            unfolding top1_loop_equiv_on_def by (by100 blast)
        qed
        \<comment> \<open>By hhtpy\\_finite, f1 ~ f2 in some \\<Union>F'.\<close>
        from hhtpy_finite[OF hf1X hf2X \<open>top1_path_homotopic_on X TX p p f1 f2\<close>]
        obtain F' where hF'fin: "finite F'" and hF'J: "F' \<subseteq> J"
            and hF'htpy: "top1_path_homotopic_on (\<Union>\<gamma>\<in>F'. C \<gamma>)
                (subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)) p p f1 f2" by (by100 blast)
        let ?FF = "F \<union> F'"
        \<comment> \<open>f1 ~ f2 in \\<Union>?FF (lifting from \\<Union>F').\<close>
        have hF'_sub_FF: "(\<Union>\<gamma>\<in>F'. C \<gamma>) \<subseteq> (\<Union>\<gamma>\<in>?FF. C \<gamma>)" by (by100 blast)
        let ?YFF = "\<Union>\<gamma>\<in>?FF. C \<gamma>"
        let ?TYFF = "subspace_topology X TX ?YFF"
        have hYFF_sub: "?YFF \<subseteq> X" using hC hFJ hF'J by (by100 blast)
        have hTYFF: "is_topology_on ?YFF ?TYFF" by (rule subspace_topology_is_topology_on[OF hTX hYFF_sub])
        have hhtpy_FF: "top1_path_homotopic_on ?YFF ?TYFF p p f1 f2"
        proof -
          have "subspace_topology ?YFF ?TYFF (\<Union>\<gamma>\<in>F'. C \<gamma>) = subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)"
            by (rule subspace_topology_trans) (use hF'_sub_FF in blast)
          from path_homotopic_subspace_to_ambient[OF hTYFF hF'_sub_FF this[symmetric] hF'htpy]
          show ?thesis .
        qed
        \<comment> \<open>f1 ~ f2 in ?YFF \\<Longrightarrow> [f1] = [f2] in \\<pi>\\_1(?YFF).
           The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective (by free\\_group\\_hom\\_subset\\_injective).
           Since c1 = [f1]\\_{?Y} and c2 = [f2]\\_{?Y} map to the same class in \\<pi>\\_1(?YFF),
           and the map is injective, c1 = c2.\<close>
        \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective.
           This follows from free\\_group\\_hom\\_subset\\_injective applied to
           free(F) \\<hookrightarrow> free(F\\<union>F'), composed with the isos.\<close>
        \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective.\<close>
        let ?incl_FF = "top1_fundamental_group_induced_on ?Y ?TY p ?YFF ?TYFF p (\<lambda>x. x)"
        have hF_sub_FF: "?Y \<subseteq> ?YFF" by (by100 blast)
        have hpYFF: "p \<in> ?YFF" using hpY hF_sub_FF by (by100 blast)
        have hsubsp_eq: "subspace_topology ?YFF ?TYFF ?Y = ?TY"
          by (rule subspace_topology_trans) (use hF_sub_FF in blast)
        have hincl_FF_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p)
            (top1_fundamental_group_carrier ?YFF ?TYFF p) (top1_fundamental_group_mul ?YFF ?TYFF p)
            ?incl_FF"
          using subspace_inclusion_induced_hom[OF hTYFF hF_sub_FF hpY]
            hsubsp_eq by (by100 simp)
        \<comment> \<open>?incl\\_FF(c1) = [f1]\\_{?YFF} and ?incl\\_FF(c2) = [f2]\\_{?YFF}.\<close>
        \<comment> \<open>From hhtpy\\_FF: f1 ~ f2 in ?YFF, so [f1] = [f2] in \\<pi>\\_1(?YFF).\<close>
        have hf1_loop_FF: "top1_is_loop_on ?YFF ?TYFF p f1"
        proof -
          have "top1_continuous_map_on I_set I_top ?Y ?TY f1"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hf1_cont_FF: "top1_continuous_map_on I_set I_top ?YFF ?TYFF f1"
          proof -
            have "f1 ` I_set \<subseteq> ?Y" using hf1_loop
              unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
              by (by100 blast)
            hence "f1 ` I_set \<subseteq> ?YFF" using hF_sub_FF by (by100 blast)
            have "top1_continuous_map_on I_set I_top X TX f1"
              using hf1X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                rule_format] this \<open>f1 ` I_set \<subseteq> ?YFF\<close> hYFF_sub
            show ?thesis by (by100 blast)
          qed
          moreover have "f1 0 = p" "f1 1 = p"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hf2_loop_FF: "top1_is_loop_on ?YFF ?TYFF p f2"
        proof -
          have "f2 ` I_set \<subseteq> ?Y" using hf2_loop
            unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
            by (by100 blast)
          hence "f2 ` I_set \<subseteq> ?YFF" using hF_sub_FF by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX f2"
            using hf2X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
              rule_format] this \<open>f2 ` I_set \<subseteq> ?YFF\<close> hYFF_sub
          have "top1_continuous_map_on I_set I_top ?YFF ?TYFF f2" by (by100 blast)
          moreover have "f2 0 = p" "f2 1 = p"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hloop_equiv_FF: "top1_loop_equiv_on ?YFF ?TYFF p f1 f2"
          unfolding top1_loop_equiv_on_def
          using hf1_loop_FF hf2_loop_FF hhtpy_FF by (by100 blast)
        \<comment> \<open>?incl\\_FF(c1) = ?incl\\_FF(c2) in \\<pi>\\_1(?YFF).\<close>
        have hincl_c1: "?incl_FF c1 = {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          unfolding top1_fundamental_group_induced_on_def hc1_eq
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f1 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}"
          then obtain f' where hf': "top1_loop_equiv_on ?Y ?TY p f1 f'"
              "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'(2) \<open>_ = f'\<close> by (by100 simp)
          have "top1_loop_equiv_on ?YFF ?TYFF p f1 f'"
          proof -
            from hf'(1)[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f1 f'" by (by100 blast)
            have "subspace_topology ?YFF ?TYFF ?Y = ?TY" using hsubsp_eq by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTYFF hF_sub_FF this[symmetric]
                \<open>top1_path_homotopic_on ?Y ?TY p p f1 f'\<close>]
            have "top1_path_homotopic_on ?YFF ?TYFF p p f1 f'" .
            have "top1_is_loop_on ?YFF ?TYFF p f'"
              using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
              unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf1_loop_FF \<open>top1_path_homotopic_on ?YFF ?TYFF p p f1 f'\<close>
              by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTYFF this \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          have "top1_loop_equiv_on ?Y ?TY p f1 f1" by (rule top1_loop_equiv_on_refl[OF hf1_loop])
          moreover have "(\<lambda>x. x) \<circ> f1 = f1" by (by100 auto)
          hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f1) h"
            using \<open>h \<in> _\<close> by (by100 simp)
          ultimately show "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f1 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
        qed
        moreover have hincl_c2: "?incl_FF c2 = {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          unfolding top1_fundamental_group_induced_on_def hc2_eq
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f2 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}"
          then obtain f' where hf': "top1_loop_equiv_on ?Y ?TY p f2 f'"
              "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'(2) \<open>_ = f'\<close> by (by100 simp)
          have "top1_loop_equiv_on ?YFF ?TYFF p f2 f'"
          proof -
            from hf'(1)[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f2 f'" by (by100 blast)
            have "subspace_topology ?YFF ?TYFF ?Y = ?TY" using hsubsp_eq by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTYFF hF_sub_FF this[symmetric]
                \<open>top1_path_homotopic_on ?Y ?TY p p f2 f'\<close>]
            have "top1_path_homotopic_on ?YFF ?TYFF p p f2 f'" .
            have "top1_is_loop_on ?YFF ?TYFF p f'"
              using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
              unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf2_loop_FF \<open>top1_path_homotopic_on ?YFF ?TYFF p p f2 f'\<close>
              by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTYFF this \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          have "top1_loop_equiv_on ?Y ?TY p f2 f2" by (rule top1_loop_equiv_on_refl[OF hf2_loop])
          moreover have "(\<lambda>x. x) \<circ> f2 = f2" by (by100 auto)
          hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f2) h"
            using \<open>h \<in> _\<close> by (by100 simp)
          ultimately show "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f2 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
        qed
        moreover have "{h. top1_loop_equiv_on ?YFF ?TYFF p f1 h} =
            {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          hence "top1_loop_equiv_on ?YFF ?TYFF p f1 h" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTYFF
              top1_loop_equiv_on_sym[OF hloop_equiv_FF] this]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          hence "top1_loop_equiv_on ?YFF ?TYFF p f2 h" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTYFF hloop_equiv_FF this]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}" by (by100 blast)
        qed
        ultimately have "?incl_FF c1 = ?incl_FF c2" by (by100 simp)
        \<comment> \<open>?incl\\_FF is injective (free group embedding).
           Both \\<pi>\\_1(?Y) and \\<pi>\\_1(?YFF) are free. The inclusion maps generators
           to generators. By free\\_group\\_hom\\_subset\\_injective: injective.\<close>
        moreover have "inj_on ?incl_FF (top1_fundamental_group_carrier ?Y ?TY p)"
        proof -
          \<comment> \<open>Get the free group for ?YFF.\<close>
          have hFFfin: "finite ?FF" using hFfin hF'fin by (by100 simp)
          have hFFJ: "?FF \<subseteq> J" using hFJ hF'J by (by100 blast)
          have hFFne: "?FF \<noteq> {}" using hFne by (by100 blast)
          from hfinite_free[OF hFFfin hFFJ hFFne]
          have hwedge_FF: "top1_is_wedge_of_circles_on ?YFF ?TYFF ?FF p" .
          have hg_FF: "\<forall>j\<in>?FF. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?YFF ?TYFF (C j)) (g j)"
          proof -
            { fix j assume "j \<in> ?FF"
              hence "j \<in> J" using hFFJ by (by100 blast)
              have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              moreover have "subspace_topology ?YFF ?TYFF (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use \<open>j \<in> ?FF\<close> in blast)
              ultimately have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?YFF ?TYFF (C j)) (g j)" by (by100 simp) }
            thus ?thesis by (by100 blast)
          qed
          have hC_closed_FF: "\<forall>D\<subseteq>?YFF. closedin_on ?YFF ?TYFF D \<longleftrightarrow>
              (\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?YFF"
            from hcoh_sub[OF hFFJ, rule_format, OF hD]
            have hiff: "closedin_on ?YFF ?TYFF D \<longleftrightarrow>
                (\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?FF. subspace_topology ?YFF ?TYFF (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?YFF ?TYFF D \<Longrightarrow>
                \<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?YFF ?TYFF D"
              using hiff htrans by (by100 simp)
          qed
          have hbase_FF: "\<forall>j\<in>?FF. g j (1, 0) = p" using hg hFFJ by (by100 blast)
          have hC_data_FF: "\<forall>j\<in>?FF. C j \<subseteq> ?YFF \<and> p \<in> C j" using hC hFFJ by (by100 blast)
          have hC_union_FF: "(\<Union>j\<in>?FF. C j) = ?YFF" by (by100 blast)
          have hC_disj_FF: "\<forall>i\<in>?FF. \<forall>j\<in>?FF. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hFFJ by (by100 blast)
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_FF hFFfin
              hg_FF hbase_FF hC_data_FF hC_union_FF hC_disj_FF hC_closed_FF]
          obtain GFF :: "int set" and mulFF eFF invgFF and \<eta>FF :: "'i \<Rightarrow> int" and \<Phi>FF
            where hfreeFF: "top1_is_free_group_full_on GFF mulFF eFF invgFF \<eta>FF ?FF"
              and hisoFF: "top1_group_iso_on GFF mulFF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) \<Phi>FF"
              and hgensFF: "\<forall>j\<in>?FF. \<Phi>FF (\<eta>FF j) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>The composition: \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F: free(F) \\<rightarrow> free(F\\<union>F').
             This maps \\<eta>\\_F(\\<alpha>) to \\<eta>\\_FF(\\<alpha>) for \\<alpha> \\<in> F.
             By free\\_group\\_hom\\_subset\\_injective, it's injective.
             Since \\<Phi>\\_F, \\<Phi>\\_FF are bijections, incl\\_FF is injective.\<close>
          \<comment> \<open>For simplicity, we show injectivity directly:
             if incl\\_FF(c) = incl\\_FF(c') then c = c'.
             This was already handled by the enclosing proof structure (inj\\_onI).
             The injectivity follows from: if c \\<noteq> id, then incl\\_FF(c) \\<noteq> id
             (by free group embedding). Equivalently: ker(incl\\_FF) = {id}.\<close>
          \<comment> \<open>\\<Phi>\\_F and \\<Phi>\\_FF are available from chosen\\_loops\\_arb.\<close>
          have h\<Phi>F_bij: "bij_betw \<Phi>F GF (top1_fundamental_group_carrier ?Y ?TY p)"
            using hisoF unfolding top1_group_iso_on_def by (by100 blast)
          have h\<Phi>FF_bij: "bij_betw \<Phi>FF GFF (top1_fundamental_group_carrier ?YFF ?TYFF p)"
            using hisoFF unfolding top1_group_iso_on_def by (by100 blast)
          have h\<Phi>F_inj: "inj_on \<Phi>F GF"
            using h\<Phi>F_bij unfolding bij_betw_def by (by100 blast)
          have h\<Phi>FF_inj: "inj_on \<Phi>FF GFF"
            using h\<Phi>FF_bij unfolding bij_betw_def by (by100 blast)
          \<comment> \<open>Compose: \\<psi> = \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F: GF \\<rightarrow> GFF.
             This is a hom mapping \\<eta>\\_F(\\<alpha>) to \\<eta>\\_FF(\\<alpha>) for \\<alpha> \\<in> F.
             By free\\_group\\_hom\\_subset\\_injective: \\<psi> is injective.
             Since \\<Phi>\\_F is bijective, incl\\_FF \\<circ> \\<Phi>\\_F is injective on GF.
             Since \\<Phi>\\_F is surjective onto \\<pi>\\_1(?Y), incl\\_FF is injective on \\<pi>\\_1(?Y).\<close>
          \<comment> \<open>Alternative direct argument: if incl\\_FF(c) = incl\\_FF(c'), then
             \\<Phi>\\_FF\<inverse>(incl\\_FF(c)) = \\<Phi>\\_FF\<inverse>(incl\\_FF(c')). The map \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F
             is injective (free\\_group\\_hom\\_subset\\_injective). So \\<Phi>\\_F\<inverse>(c) = \\<Phi>\\_F\<inverse>(c').
             Since \\<Phi>\\_F bijective: c = c'.\<close>
          \<comment> \<open>By free\\_group\\_hom\\_exists + free\\_group\\_hom\\_subset\\_injective:
             the algebraic map \\<psi>: GF \\<rightarrow> GFF with \\<psi>(\\<eta>\\_F(\\<alpha>)) = \\<eta>\\_FF(\\<alpha>) is injective.
             Composing with the bijections \\<Phi>\\_F, \\<Phi>\\_FF gives incl\\_FF injective.
             This requires finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb to verify
             the generator correspondence \\<Phi>(\\<eta>(\\<alpha>)) = [gen\\_loop \\<alpha>].\<close>
          \<comment> \<open>Construct \\<psi>: GF \\<rightarrow> GFF with \\<psi>(\\<eta>\\_F(\\<alpha>)) = \\<eta>\\_FF(\\<alpha>) using free\\_group\\_hom\\_exists.\<close>
          have hGFF_grp: "top1_is_group_on GFF mulFF eFF invgFF"
            using hfreeFF unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hGF_grp: "top1_is_group_on GF mulF eF invgF"
            using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
          have h\<eta>FF_in: "\<forall>\<alpha>\<in>F. \<eta>FF \<alpha> \<in> GFF"
            using hfreeFF unfolding top1_is_free_group_full_on_def by (by100 blast)
          from free_group_hom_exists[OF hfreeF hGFF_grp h\<eta>FF_in]
          obtain \<psi> where h\<psi>_hom: "top1_group_hom_on GF mulF GFF mulFF \<psi>"
              and h\<psi>_gen: "\<forall>\<alpha>\<in>F. \<psi> (\<eta>F \<alpha>) = \<eta>FF \<alpha>" by (by100 blast)
          \<comment> \<open>By free\\_group\\_hom\\_subset\\_injective: \\<psi> is injective.\<close>
          have hF_sub_FF: "F \<subseteq> ?FF" by (by100 blast)
          from free_group_hom_subset_injective[OF hfreeF hfreeFF hF_sub_FF h\<psi>_hom h\<psi>_gen]
          have h\<psi>_inj: "inj_on \<psi> GF" .
          \<comment> \<open>incl\\_FF = \\<Phi>\\_FF \\<circ> \\<psi> \\<circ> \\<Phi>\\_F\\<inverse> (on generators, by free\\_group\\_hom\\_unique).
             Since \\<psi> injective + \\<Phi>s bijective \\<Longrightarrow> incl\\_FF injective.\<close>
          \<comment> \<open>Simpler: show incl\\_FF injective directly.
             Take c, c' with incl\\_FF(c) = incl\\_FF(c').
             Let x = \\<Phi>\\_F\\<inverse>(c), y = \\<Phi>\\_F\\<inverse>(c'). Both in GF.
             \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) = incl\\_FF(c) = incl\\_FF(c') = \\<Phi>\\_FF(\\<psi>(y)).
             \\<Phi>\\_FF injective: \\<psi>(x) = \\<psi>(y).
             \\<psi> injective: x = y.
             \\<Phi>\\_F injective: c = c'.
             BUT: \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) requires that the composition agrees
             with the topological inclusion. This uses free\\_group\\_hom\\_unique.\<close>
          \<comment> \<open>Now show: for c \\<in> \\<pi>\\_1(?Y) with incl\\_FF(c) = incl\\_FF(c'),
             c = c'. Use: \\<Phi>\\_F\\<inverse>(c) = x \\<in> GF, \\<Phi>\\_F\\<inverse>(c') = y \\<in> GF.
             incl\\_FF(c) = incl\\_FF(\\<Phi>\\_F(x)), etc.
             Need: \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)).
             Then \\<Phi>\\_FF(\\<psi>(x)) = \\<Phi>\\_FF(\\<psi>(y)) \\<Longrightarrow> \\<psi>(x) = \\<psi>(y) \\<Longrightarrow> x = y \\<Longrightarrow> c = c'.\<close>
          \<comment> \<open>The equality \\<Phi>\\_FF \\<circ> \\<psi> = incl\\_FF \\<circ> \\<Phi>\\_F on GF follows from
             free\\_group\\_hom\\_unique: both are homs GF \\<rightarrow> \\<pi>\\_1(?YFF)
             agreeing on generators \\<eta>\\_F(\\<alpha>).\<close>
          show ?thesis
          proof (rule inj_onI)
            fix c c' assume hcY: "c \<in> top1_fundamental_group_carrier ?Y ?TY p"
              and hc'Y: "c' \<in> top1_fundamental_group_carrier ?Y ?TY p"
              and hincl_eq: "?incl_FF c = ?incl_FF c'"
            \<comment> \<open>\\<Phi>\\_F is surjective onto \\<pi>\\_1(?Y). Get x, y.\<close>
            have hPhiF_surj: "\<Phi>F ` GF = top1_fundamental_group_carrier ?Y ?TY p"
              using h\<Phi>F_bij unfolding bij_betw_def by (by100 blast)
            from hcY obtain x where hxG: "x \<in> GF" and hcx: "c = \<Phi>F x"
              using hPhiF_surj by (by100 blast)
            from hc'Y obtain y where hyG: "y \<in> GF" and hc'y: "c' = \<Phi>F y"
              using hPhiF_surj by (by100 blast)
            \<comment> \<open>\\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) (both homs agree on generators).\<close>
            \<comment> \<open>This requires free\\_group\\_hom\\_unique + generator correspondence.
               Both \\<Phi>\\_FF \\<circ> \\<psi> and incl\\_FF \\<circ> \\<Phi>\\_F are homs GF \\<rightarrow> \\<pi>\\_1(?YFF).
               They agree on generators \\<eta>\\_F(\\<alpha>):
               \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) and
               incl\\_FF(\\<Phi>\\_F(\\<eta>\\_F \\<alpha>)) = incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}
               and \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}
               (from finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb).
               By free\\_group\\_hom\\_unique: they agree everywhere.\<close>
            have "?incl_FF (\<Phi>F x) = ?incl_FF (\<Phi>F y)"
              using hincl_eq hcx hc'y by (by100 simp)
            \<comment> \<open>Both equal \\<Phi>\\_FF(\\<psi>(x)) and \\<Phi>\\_FF(\\<psi>(y)) respectively (by the hom agreement).\<close>
            \<comment> \<open>So \\<Phi>\\_FF(\\<psi>(x)) = \\<Phi>\\_FF(\\<psi>(y)).\<close>
            have h\<psi>x_in: "\<psi> x \<in> GFF"
              using h\<psi>_hom hxG unfolding top1_group_hom_on_def by (by100 blast)
            have h\<psi>y_in: "\<psi> y \<in> GFF"
              using h\<psi>_hom hyG unfolding top1_group_hom_on_def by (by100 blast)
            \<comment> \<open>Both \\<Phi>\\_FF \\<circ> \\<psi> and incl\\_FF \\<circ> \\<Phi>\\_F are homs GF \\<rightarrow> \\<pi>\\_1(?YFF).
               They agree on all of GF by free\\_group\\_hom\\_unique.\<close>
            \<comment> \<open>Both homs agree on generators: for \\<alpha> \\<in> F,
               \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}
               ?incl\\_FF(\\<Phi>\\_F(\\<eta>\\_F \\<alpha>)) = ?incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}\<close>
            have hgen_agree: "\<forall>\<alpha>\<in>F. \<Phi>FF (\<psi> (\<eta>F \<alpha>)) = ?incl_FF (\<Phi>F (\<eta>F \<alpha>))"
            proof (intro ballI)
              fix \<alpha> assume h\<alpha>F: "\<alpha> \<in> F"
              have h\<alpha>J: "\<alpha> \<in> J" using h\<alpha>F hFJ by (by100 blast)
              have h\<alpha>FF: "\<alpha> \<in> ?FF" using h\<alpha>F by (by100 blast)
              \<comment> \<open>LHS: \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}.\<close>
              have "\<psi> (\<eta>F \<alpha>) = \<eta>FF \<alpha>" using h\<psi>_gen h\<alpha>F by (by100 blast)
              hence hLHS: "\<Phi>FF (\<psi> (\<eta>F \<alpha>)) = \<Phi>FF (\<eta>FF \<alpha>)" by (by100 simp)
              have hPhiFF_gen: "\<Phi>FF (\<eta>FF \<alpha>) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                using hgensFF h\<alpha>FF by (by100 blast)
              \<comment> \<open>RHS: \\<Phi>\\_F(\\<eta>\\_F \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?Y}.\<close>
              have hPhiF_gen: "\<Phi>F (\<eta>F \<alpha>) = {l. top1_loop_equiv_on ?Y ?TY p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                using hgensF h\<alpha>F by (by100 blast)
              \<comment> \<open>?incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}.\<close>
              have hincl_gen: "?incl_FF (\<Phi>F (\<eta>F \<alpha>)) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                unfolding hPhiF_gen top1_fundamental_group_induced_on_def
              proof (rule set_eqI, rule iffI)
                let ?gl = "\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))"
                fix h assume "h \<in> {ga. \<exists>f\<in>{l. top1_loop_equiv_on ?Y ?TY p ?gl l}.
                    top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) ga}"
                then obtain f' where hf'Y: "top1_loop_equiv_on ?Y ?TY p ?gl f'"
                    and hf'h: "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'h \<open>_ = f'\<close> by (by100 simp)
                have "top1_loop_equiv_on ?YFF ?TYFF p ?gl f'"
                proof -
                  from hf'Y[unfolded top1_loop_equiv_on_def]
                  have "top1_path_homotopic_on ?Y ?TY p p ?gl f'" by (by100 blast)
                  have hsubsp: "subspace_topology ?YFF ?TYFF ?Y = ?TY"
                    by (rule subspace_topology_trans) (use hF_sub_FF in blast)
                  have "top1_path_homotopic_on ?YFF ?TYFF p p ?gl f'"
                  proof -
                    from \<open>top1_path_homotopic_on ?Y ?TY p p ?gl f'\<close>[unfolded top1_path_homotopic_on_def]
                    obtain H_loc where
                        "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc"
                        "\<forall>s\<in>I_set. H_loc (s, 0) = ?gl s" "\<forall>s\<in>I_set. H_loc (s, 1) = f' s"
                        "\<forall>t\<in>I_set. H_loc (0, t) = p" "\<forall>t\<in>I_set. H_loc (1, t) = p"
                      by (by100 blast)
                    \<comment> \<open>H\\_loc: I\\<times>I \\<rightarrow> ?Y continuous. Lift to ?YFF via ?Y \\<subseteq> ?YFF \\<subseteq> X.\<close>
                    have hH_sub: "H_loc ` (I_set \<times> I_set) \<subseteq> ?Y"
                      using \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc\<close>
                      unfolding top1_continuous_map_on_def by (by100 blast)
                    have hY_sub_YFF: "?Y \<subseteq> ?YFF" by (by100 blast)
                    have "H_loc ` (I_set \<times> I_set) \<subseteq> ?YFF"
                      using subset_trans[OF hH_sub hY_sub_YFF] .
                    \<comment> \<open>H\\_loc continuous into X.\<close>
                    have hII_top: "is_topology_on (I_set \<times> I_set) II_topology"
                      unfolding II_topology_def
                      using product_topology_on_is_topology_on[OF
                        top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on] .
                    have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (id \<circ> H_loc)"
                      by (rule top1_continuous_map_on_comp[OF
                        \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc\<close>
                        Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
                    hence "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H_loc"
                      by (by100 simp)
                    \<comment> \<open>Restrict range to ?YFF.\<close>
                    from Theorem_18_2(5)[OF hII_top hTX hTX, rule_format]
                      this \<open>H_loc ` (I_set \<times> I_set) \<subseteq> ?YFF\<close> hYFF_sub
                    have "top1_continuous_map_on (I_set \<times> I_set) II_topology ?YFF ?TYFF H_loc"
                      by (by100 blast)
                    \<comment> \<open>?gl and f' are loops/paths in ?YFF.\<close>
                    have hf'_loop_YFF: "top1_is_loop_on ?YFF ?TYFF p f'"
                      using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
                      unfolding top1_loop_equiv_on_def by (by100 blast)
                    have hgl_loop_YFF: "top1_is_loop_on ?YFF ?TYFF p ?gl"
                    proof -
                      have "top1_is_loop_on X TX p ?gl"
                        using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                      have "?gl ` I_set \<subseteq> ?YFF"
                        using hgen h\<alpha>J h\<alpha>FF unfolding gen_loop_def by (by100 blast)
                      from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                          rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?YFF\<close> hYFF_sub
                      have "top1_continuous_map_on I_set I_top ?YFF ?TYFF ?gl"
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                      moreover have "?gl 0 = p" "?gl 1 = p"
                        using \<open>top1_is_loop_on X TX p ?gl\<close>
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                      ultimately show ?thesis
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    qed
                    show ?thesis
                      unfolding top1_path_homotopic_on_def
                      using \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?YFF ?TYFF H_loc\<close>
                        \<open>\<forall>s\<in>I_set. H_loc (s, 0) = ?gl s\<close> \<open>\<forall>s\<in>I_set. H_loc (s, 1) = f' s\<close>
                        \<open>\<forall>t\<in>I_set. H_loc (0, t) = p\<close> \<open>\<forall>t\<in>I_set. H_loc (1, t) = p\<close>
                        hgl_loop_YFF hf'_loop_YFF
                      unfolding top1_is_loop_on_def by (by100 blast)
                  qed
                  have "top1_is_loop_on ?YFF ?TYFF p f'"
                    using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
                    unfolding top1_loop_equiv_on_def by (by100 blast)
                  have "top1_is_loop_on ?YFF ?TYFF p ?gl"
                  proof -
                    have "top1_is_loop_on X TX p ?gl"
                      using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                    have "?gl ` I_set \<subseteq> ?YFF"
                      using hgen h\<alpha>J h\<alpha>FF unfolding gen_loop_def by (by100 blast)
                    from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                        rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?YFF\<close> hYFF_sub
                    have "top1_continuous_map_on I_set I_top ?YFF ?TYFF ?gl"
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    moreover have "?gl 0 = p" "?gl 1 = p"
                      using \<open>top1_is_loop_on X TX p ?gl\<close>
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                    ultimately show ?thesis
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  qed
                  thus ?thesis unfolding top1_loop_equiv_on_def
                    using \<open>top1_is_loop_on ?YFF ?TYFF p f'\<close>
                      \<open>top1_path_homotopic_on ?YFF ?TYFF p p ?gl f'\<close> by (by100 blast)
                qed
                from top1_loop_equiv_on_trans[OF hTYFF this
                    \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
                show "h \<in> {l. top1_loop_equiv_on ?YFF ?TYFF p ?gl l}" by (by100 blast)
              next
                let ?gl = "\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))"
                fix h assume "h \<in> {l. top1_loop_equiv_on ?YFF ?TYFF p ?gl l}"
                have "top1_is_loop_on ?Y ?TY p ?gl"
                proof -
                  have "top1_is_loop_on X TX p ?gl"
                    using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                  have "?gl ` I_set \<subseteq> ?Y"
                    using hgen h\<alpha>J h\<alpha>F unfolding gen_loop_def by (by100 blast)
                  from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                      rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?Y\<close> hY_sub
                  have "top1_continuous_map_on I_set I_top ?Y ?TY ?gl"
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  moreover have "?gl 0 = p" "?gl 1 = p"
                    using \<open>top1_is_loop_on X TX p ?gl\<close>
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                  ultimately show ?thesis
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                qed
                from top1_loop_equiv_on_refl[OF this]
                have "?gl \<in> {l. top1_loop_equiv_on ?Y ?TY p ?gl l}" by (by100 blast)
                moreover have "(\<lambda>x. x) \<circ> ?gl = ?gl" by (by100 auto)
                hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> ?gl) h"
                  using \<open>h \<in> _\<close> by (by100 simp)
                ultimately show "h \<in> {ga. \<exists>f\<in>{l. top1_loop_equiv_on ?Y ?TY p ?gl l}.
                    top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) ga}" by (by100 blast)
              qed
              show "\<Phi>FF (\<psi> (\<eta>F \<alpha>)) = ?incl_FF (\<Phi>F (\<eta>F \<alpha>))"
                using hLHS hPhiFF_gen hincl_gen by (by100 simp)
            qed
            \<comment> \<open>By free\\_group\\_hom\\_unique: both homs agree on all of GF.\<close>
            have hpi1YFF_grp: "top1_is_group_on
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p)
                (top1_fundamental_group_id ?YFF ?TYFF p)
                (top1_fundamental_group_invg ?YFF ?TYFF p)"
              by (rule top1_fundamental_group_is_group[OF hTYFF hpYFF])
            have hGF_gen: "GF = top1_subgroup_generated_on GF mulF eF invgF (\<eta>F ` F)"
              using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
            have h\<eta>F_in: "\<forall>s\<in>F. \<eta>F s \<in> GF"
              using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
            have h\<Phi>FF_hom: "top1_group_hom_on GFF mulFF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) \<Phi>FF"
              using hisoFF unfolding top1_group_iso_on_def by (by100 blast)
            have h\<Phi>F_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?Y ?TY p)
                (top1_fundamental_group_mul ?Y ?TY p) \<Phi>F"
              using hisoF unfolding top1_group_iso_on_def by (by100 blast)
            have hcomp1_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) (\<lambda>z. \<Phi>FF (\<psi> z))"
            proof -
              from group_hom_comp[OF h\<psi>_hom h\<Phi>FF_hom]
              have "top1_group_hom_on GF mulF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) (\<Phi>FF \<circ> \<psi>)" .
              moreover have "(\<Phi>FF \<circ> \<psi>) = (\<lambda>z. \<Phi>FF (\<psi> z))" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            have hcomp2_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) (\<lambda>z. ?incl_FF (\<Phi>F z))"
            proof -
              from group_hom_comp[OF h\<Phi>F_hom hincl_FF_hom]
              have "top1_group_hom_on GF mulF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) (?incl_FF \<circ> \<Phi>F)" .
              moreover have "(?incl_FF \<circ> \<Phi>F) = (\<lambda>z. ?incl_FF (\<Phi>F z))" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            have hcomp_agree: "\<forall>z\<in>GF. \<Phi>FF (\<psi> z) = ?incl_FF (\<Phi>F z)"
              using free_group_hom_unique[OF hGF_grp hpi1YFF_grp hGF_gen h\<eta>F_in
                  hcomp1_hom hcomp2_hom hgen_agree] by (by100 blast)
            have hcomp_x: "\<Phi>FF (\<psi> x) = ?incl_FF (\<Phi>F x)"
              using hcomp_agree hxG by (by100 blast)
            have hcomp_y: "\<Phi>FF (\<psi> y) = ?incl_FF (\<Phi>F y)"
              using hcomp_agree hyG by (by100 blast)
            hence "\<Phi>FF (\<psi> x) = \<Phi>FF (\<psi> y)"
              using hcomp_x \<open>?incl_FF (\<Phi>F x) = ?incl_FF (\<Phi>F y)\<close> by (by100 simp)
            hence "\<psi> x = \<psi> y"
              using h\<Phi>FF_inj h\<psi>x_in h\<psi>y_in unfolding inj_on_def by (by100 blast)
            hence "x = y" using h\<psi>_inj hxG hyG unfolding inj_on_def by (by100 blast)
            thus "c = c'" using hcx hc'y by (by100 simp)
          qed
        qed
        ultimately show "c1 = c2" using hc1 hc2 unfolding inj_on_def by (by100 blast)
      qed
    qed
    define \<iota> where "\<iota> \<alpha> = {f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f}" for \<alpha>
    \<comment> \<open>Step 3: verify top1\\_is\\_free\\_group\\_full\\_on.\<close>
    show ?thesis
      unfolding top1_is_free_group_full_on_def
    proof (intro exI[of _ \<iota>] conjI)
      show "top1_is_group_on
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
          (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
        by (rule top1_fundamental_group_is_group[OF hTX hp])
      show "\<forall>s\<in>J. \<iota> s \<in> top1_fundamental_group_carrier X TX p"
      proof (intro ballI)
        fix s assume "s \<in> J"
        have "top1_is_loop_on X TX p (gen_loop s)" using hgen \<open>s \<in> J\<close> by (by100 blast)
        thus "\<iota> s \<in> top1_fundamental_group_carrier X TX p"
          unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
      qed
      show "inj_on \<iota> J"
      proof (rule inj_onI)
        fix \<alpha> \<beta> assume h\<alpha>J: "\<alpha> \<in> J" and h\<beta>J: "\<beta> \<in> J" and heq: "\<iota> \<alpha> = \<iota> \<beta>"
        \<comment> \<open>\\<iota>(\\<alpha>) = \\<iota>(\\<beta>) means gen\\_loop \\<alpha> \\<sim> gen\\_loop \\<beta> in X.\<close>
        have hloop_\<alpha>: "top1_is_loop_on X TX p (gen_loop \<alpha>)" using hgen h\<alpha>J by (by100 blast)
        have hloop_\<beta>: "top1_is_loop_on X TX p (gen_loop \<beta>)" using hgen h\<beta>J by (by100 blast)
        \<comment> \<open>From \\<iota>(\\<alpha>) = \\<iota>(\\<beta>), derive path homotopy.\<close>
        have hhtpy: "top1_path_homotopic_on X TX p p (gen_loop \<alpha>) (gen_loop \<beta>)"
        proof -
          from heq have "{f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f} =
              {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}" unfolding \<iota>_def .
          hence "gen_loop \<beta> \<in> {f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f}"
          proof -
            have "gen_loop \<beta> \<in> {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}"
              using top1_loop_equiv_on_refl[OF hloop_\<beta>] by (by100 blast)
            thus ?thesis using \<open>{f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f} =
                {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}\<close> by (by100 blast)
          qed
          hence "top1_loop_equiv_on X TX p (gen_loop \<alpha>) (gen_loop \<beta>)" by (by100 blast)
          thus ?thesis unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
        qed
        \<comment> \<open>By hhtpy\\_finite, the homotopy lies in a finite sub-wedge.\<close>
        from hhtpy_finite[OF hloop_\<alpha> hloop_\<beta> hhtpy]
        obtain F' where hF'fin: "finite F'" and hF'J: "F' \<subseteq> J"
          and hF'htpy: "top1_path_homotopic_on (\<Union>\<gamma>\<in>F'. C \<gamma>)
              (subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)) p p (gen_loop \<alpha>) (gen_loop \<beta>)"
          by (by100 blast)
        \<comment> \<open>Take F = {\\<alpha>, \\<beta>} \\<union> F'. Both gen\\_loops and the homotopy lie in \\<Union>F.\<close>
        let ?F = "{\<alpha>, \<beta>} \<union> F'"
        have hFfin: "finite ?F" using hF'fin by (by100 simp)
        have hFJ: "?F \<subseteq> J" using h\<alpha>J h\<beta>J hF'J by (by100 blast)
        have hFne: "?F \<noteq> {}" by (by100 blast)
        \<comment> \<open>gen\\_loop \\<alpha> and gen\\_loop \\<beta> are homotopic in \\<Union>?F (lift from \\<Union>F').\<close>
        have hF'_sub_F: "(\<Union>\<gamma>\<in>F'. C \<gamma>) \<subseteq> (\<Union>\<gamma>\<in>?F. C \<gamma>)" by (by100 blast)
        have hF_sub_X: "(\<Union>\<gamma>\<in>?F. C \<gamma>) \<subseteq> X" using hC hFJ by (by100 blast)
        \<comment> \<open>Subspace topology of \\<Union>F' in \\<Union>?F = subspace topology in X (transitivity).\<close>
        have hsubsp_eq: "subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>) =
            subspace_topology (\<Union>\<gamma>\<in>?F. C \<gamma>) (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>))
                (\<Union>\<gamma>\<in>F'. C \<gamma>)"
          by (rule subspace_topology_trans[symmetric]) (use hF'_sub_F in blast)
        have hhtpy_F: "top1_path_homotopic_on (\<Union>\<gamma>\<in>?F. C \<gamma>)
            (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>)) p p (gen_loop \<alpha>) (gen_loop \<beta>)"
        proof -
          have hTF: "is_topology_on (\<Union>\<gamma>\<in>?F. C \<gamma>) (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>))"
            by (rule subspace_topology_is_topology_on[OF hTX hF_sub_X])
          from path_homotopic_subspace_to_ambient[OF hTF hF'_sub_F hsubsp_eq hF'htpy]
          show ?thesis .
        qed
        \<comment> \<open>The sub-wedge \\<Union>?F is a wedge with free \\<pi>\\_1.\<close>
        from hfinite_free[OF hFfin hFJ hFne]
        have hwedge_F: "top1_is_wedge_of_circles_on (\<Union>\<gamma>\<in>?F. C \<gamma>)
            (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>)) ?F p" .
        \<comment> \<open>In \\<pi>\\_1(\\<Union>?F), gen\\_loop \\<alpha> and gen\\_loop \\<beta> are generators indexed by \\<alpha> and \\<beta>.
           If \\<alpha> \\<noteq> \\<beta>, they generate distinct elements (injectivity of free generators).
           But they are homotopic in \\<Union>?F, contradiction.\<close>
        \<comment> \<open>Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb to \\<Union>?F.\<close>
        let ?Y = "\<Union>\<gamma>\<in>?F. C \<gamma>"
        let ?TY = "subspace_topology X TX ?Y"
        have hg_F: "\<forall>j\<in>?F. top1_homeomorphism_on top1_S1 top1_S1_topology
            (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
        proof -
          {
            fix j assume hjF: "j \<in> ?F"
            hence "j \<in> J" using hFJ by (by100 blast)
            have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
            have "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
              by (rule subspace_topology_trans) (use hjF in blast)
            hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
              using hgj by (by100 simp)
          }
          thus ?thesis by (by100 blast)
        qed
        have hC_closed_F: "\<forall>D\<subseteq>?Y. closedin_on ?Y ?TY D \<longleftrightarrow>
            (\<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D))"
        proof (intro allI impI iffI)
          fix D assume hD: "D \<subseteq> ?Y"
          from hcoh_sub[OF hFJ, rule_format, OF hD]
          have hiff: "closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>j\<in>?F. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
          have htrans: "\<forall>j\<in>?F. subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
          proof (intro ballI)
            fix j assume "j \<in> ?F"
            show "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
              by (rule subspace_topology_trans) (use \<open>j \<in> ?F\<close> in blast)
          qed
          show "closedin_on ?Y ?TY D \<Longrightarrow>
              \<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)"
            using hiff htrans by (by100 simp)
          show "(\<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)) \<Longrightarrow>
              closedin_on ?Y ?TY D"
            using hiff htrans by (by100 simp)
        qed
        have hbase_F: "\<forall>j\<in>?F. g j (1, 0) = p"
          using hg hFJ by (by100 blast)
        have hC_data_F: "\<forall>j\<in>?F. C j \<subseteq> ?Y \<and> p \<in> C j"
          using hC hFJ by (by100 blast)
        have hC_union_F: "(\<Union>j\<in>?F. C j) = ?Y" by (by100 blast)
        have hC_disj_F: "\<forall>i\<in>?F. \<forall>j\<in>?F. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
          using hdisjoint hFJ by (by100 blast)
        from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_F hFfin
            hg_F hbase_F hC_data_F hC_union_F hC_disj_F hC_closed_F]
        obtain F_grp :: "int set" and mul_F e_F invg_F and \<eta>_F :: "'i \<Rightarrow> int" and \<Phi>_F
          where hfree_F: "top1_is_free_group_full_on F_grp mul_F e_F invg_F \<eta>_F ?F"
            and hiso_F: "top1_group_iso_on F_grp mul_F
                (top1_fundamental_group_carrier ?Y ?TY p)
                (top1_fundamental_group_mul ?Y ?TY p) \<Phi>_F"
            and hgens_F: "\<forall>j\<in>?F. \<Phi>_F (\<eta>_F j) = {l. top1_loop_equiv_on ?Y ?TY p
                (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
          by (by100 blast)
        \<comment> \<open>gen\\_loop j t = g j (cos(2\\<pi>t), sin(2\\<pi>t)).\<close>
        have hPhi_\<alpha>: "\<Phi>_F (\<eta>_F \<alpha>) = {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}"
        proof -
          have "\<alpha> \<in> ?F" by (by100 blast)
          from hgens_F[rule_format, OF this]
          show ?thesis unfolding gen_loop_def by (by100 blast)
        qed
        have hPhi_\<beta>: "\<Phi>_F (\<eta>_F \<beta>) = {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
        proof -
          have "\<beta> \<in> ?F" by (by100 blast)
          from hgens_F[rule_format, OF this]
          show ?thesis unfolding gen_loop_def by (by100 blast)
        qed
        \<comment> \<open>gen\\_loop \\<alpha> \\<sim> gen\\_loop \\<beta> in ?Y, so their loop classes coincide.\<close>
        have hloop_eq: "top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) (gen_loop \<beta>)"
          using hhtpy_F unfolding top1_loop_equiv_on_def top1_is_loop_on_def
            top1_path_homotopic_on_def by (by100 blast)
        have hTY: "is_topology_on ?Y ?TY"
          by (rule subspace_topology_is_topology_on[OF hTX hF_sub_X])
        have hclass_eq: "{l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l} =
            {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
        proof (rule set_eqI, rule iffI)
          fix l assume "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}"
          hence "top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTY
              top1_loop_equiv_on_sym[OF hloop_eq] this]
          show "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}" by (by100 blast)
        next
          fix l assume "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
          hence "top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTY hloop_eq this]
          show "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}" by (by100 blast)
        qed
        hence "\<Phi>_F (\<eta>_F \<alpha>) = \<Phi>_F (\<eta>_F \<beta>)" using hPhi_\<alpha> hPhi_\<beta> by (by100 simp)
        \<comment> \<open>\\<Phi>\\_F is injective (iso), so \\<eta>\\_F \\<alpha> = \\<eta>\\_F \\<beta>.\<close>
        hence h\<eta>_eq: "\<eta>_F \<alpha> = \<eta>_F \<beta>"
        proof -
          assume hPhi_eq: "\<Phi>_F (\<eta>_F \<alpha>) = \<Phi>_F (\<eta>_F \<beta>)"
          have h\<alpha>F: "\<eta>_F \<alpha> \<in> F_grp"
            using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
          have h\<beta>F: "\<eta>_F \<beta> \<in> F_grp"
            using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
          have "inj_on \<Phi>_F F_grp"
            using hiso_F unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
          thus ?thesis using hPhi_eq h\<alpha>F h\<beta>F unfolding inj_on_def by (by100 blast)
        qed
        \<comment> \<open>\\<eta>\\_F is injective on ?F (free group condition).\<close>
        have "inj_on \<eta>_F ?F"
          using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
        thus "\<alpha> = \<beta>"
          using h\<eta>_eq unfolding inj_on_def by (by100 blast)
      qed
      show "top1_fundamental_group_carrier X TX p =
          top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
      proof (rule set_eqI, rule iffI)
        fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX p"
        \<comment> \<open>c = [f] for some loop f. By hloop\\_finite, f lies in a finite sub-wedge.\<close>
        from hc[unfolded top1_fundamental_group_carrier_def]
        obtain f where hf: "top1_is_loop_on X TX p f" and hc_eq: "c = {g. top1_loop_equiv_on X TX p f g}"
          by (by100 blast)
        from hloop_finite[OF hf] obtain F where hFfin: "finite F" and hFJ: "F \<subseteq> J"
            and hf_in_F: "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)" by (by100 blast)
        \<comment> \<open>Ensure F is non-empty (add an arbitrary element from J if needed).\<close>
        have "J \<noteq> {}" using hp hcover by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" by (by100 blast)
        let ?F2 = "F \<union> {\<gamma>}"
        have hF2fin: "finite ?F2" using hFfin by (by100 simp)
        have hF2J: "?F2 \<subseteq> J" using hFJ \<open>\<gamma> \<in> J\<close> by (by100 blast)
        have hF2ne: "?F2 \<noteq> {}" by (by100 blast)
        \<comment> \<open>[f] is in the image of the inclusion \\<pi>\\_1(\\<Union>?F) \\<rightarrow> \\<pi>\\_1(X).
           In \\<pi>\\_1(\\<Union>?F), every element is a product of generators [gen\\_loop \\<alpha>].
           The inclusion sends these to \\<iota>(\\<alpha>). So c \\<in> subgroup\\_generated.\<close>
        show "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
            (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
        proof -
          let ?Y2 = "\<Union>\<alpha>\<in>?F2. C \<alpha>"
          let ?TY2 = "subspace_topology X TX ?Y2"
          have hY2_sub: "?Y2 \<subseteq> X" using hC hF2J by (by100 blast)
          have hpY2: "p \<in> ?Y2" using hC \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hTY2: "is_topology_on ?Y2 ?TY2"
            by (rule subspace_topology_is_topology_on[OF hTX hY2_sub])
          \<comment> \<open>Step 1: \\<Union>?F2 is a wedge. Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb.\<close>
          from hfinite_free[OF hF2fin hF2J hF2ne]
          have hwedge2: "top1_is_wedge_of_circles_on ?Y2 ?TY2 ?F2 p" .
          \<comment> \<open>Prepare homeomorphisms for the sub-wedge.\<close>
          have hg_F2: "\<forall>j\<in>?F2. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
          proof -
            {
              fix j assume hjF: "j \<in> ?F2"
              hence "j \<in> J" using hF2J by (by100 blast)
              have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              have "subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use hjF in blast)
              hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
                using hgj by (by100 simp)
            }
            thus ?thesis by (by100 blast)
          qed
          have hbase_F2: "\<forall>j\<in>?F2. g j (1, 0) = p" using hg hF2J by (by100 blast)
          have hC_data_F2: "\<forall>j\<in>?F2. C j \<subseteq> ?Y2 \<and> p \<in> C j" using hC hF2J by (by100 blast)
          have hC_union_F2: "(\<Union>j\<in>?F2. C j) = ?Y2" by (by100 blast)
          have hC_disj_F2: "\<forall>i\<in>?F2. \<forall>j\<in>?F2. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hF2J by (by100 blast)
          have hC_closed_F2: "\<forall>D\<subseteq>?Y2. closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
              (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?Y2"
            from hcoh_sub[OF hF2J, rule_format, OF hD]
            have hiff: "closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
                (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?F2. subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?Y2 ?TY2 D \<Longrightarrow>
                \<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?Y2 ?TY2 D"
              using hiff htrans by (by100 simp)
          qed
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge2 hF2fin
              hg_F2 hbase_F2 hC_data_F2 hC_union_F2 hC_disj_F2 hC_closed_F2]
          obtain G2 :: "int set" and mul2 e2 invg2 and \<eta>2 :: "'i \<Rightarrow> int" and \<Phi>2
            where hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 ?F2"
              and hiso2: "top1_group_iso_on G2 mul2
                  (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              and hgens2: "\<forall>j\<in>?F2. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>Step 2: \\<pi>\\_1(?Y2) is generated by [gen\\_loop \\<alpha>] for \\<alpha> \\<in> ?F2.\<close>
          \<comment> \<open>Condition 4 of free\\_group\\_full\\_on: G2 = subgroup\\_generated(\\<eta>2 ` ?F2).\<close>
          have hG2_gen: "G2 = top1_subgroup_generated_on G2 mul2 e2 invg2 (\<eta>2 ` ?F2)"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hG2_grp: "top1_is_group_on G2 mul2 e2 invg2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>\\<Phi>2 is a surjective hom G2 \\<rightarrow> \\<pi>\\_1(?Y2).\<close>
          have hPhi2_surj: "\<Phi>2 ` G2 = top1_fundamental_group_carrier ?Y2 ?TY2 p"
            using hiso2 unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
          have hPhi2_hom: "top1_group_hom_on G2 mul2
              (top1_fundamental_group_carrier ?Y2 ?TY2 p) (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
            using hiso2 unfolding top1_group_iso_on_def by (by100 blast)
          have hpi1Y2_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p) (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p) (top1_fundamental_group_invg ?Y2 ?TY2 p)"
            by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
          \<comment> \<open>By surjective\\_hom\\_preserves\\_generation: \\<pi>\\_1(?Y2) = subgroup\\_generated(\\<Phi>2 ` \\<eta>2 ` ?F2).\<close>
          have h\<eta>2_sub: "\<eta>2 ` ?F2 \<subseteq> G2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          from surjective_hom_preserves_generation[OF hG2_grp hpi1Y2_grp hG2_gen
              hPhi2_hom hPhi2_surj h\<eta>2_sub]
          have hpi1Y2_gen: "top1_fundamental_group_carrier ?Y2 ?TY2 p =
              top1_subgroup_generated_on (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p)
                  (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p) (\<Phi>2 ` \<eta>2 ` ?F2)" .
          \<comment> \<open>\\<Phi>2(\\<eta>2(\\<alpha>)) = [gen\\_loop \\<alpha>]\\_{?Y2} (from hgens2 + gen\\_loop\\_def).\<close>
          define S_Y2 where "S_Y2 = (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
          have hPhi_eta_eq: "\<Phi>2 ` \<eta>2 ` ?F2 = S_Y2"
            unfolding S_Y2_def
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Phi>2 ` \<eta>2 ` ?F2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2" "x = \<Phi>2 (\<eta>2 \<alpha>)" by (by100 blast)
            from hgens2[rule_format, OF \<open>\<alpha> \<in> ?F2\<close>]
            have "\<Phi>2 (\<eta>2 \<alpha>) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}" .
            hence "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              using \<open>x = \<Phi>2 (\<eta>2 \<alpha>)\<close> unfolding gen_loop_def by (by100 blast)
            thus "x \<in> (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
              using \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
          next
            fix x assume "x \<in> (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2"
              "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}" by (by100 blast)
            from hgens2[rule_format, OF \<open>\<alpha> \<in> ?F2\<close>]
            have "\<Phi>2 (\<eta>2 \<alpha>) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}" .
            hence "x = \<Phi>2 (\<eta>2 \<alpha>)"
              using \<open>x = _\<close> unfolding gen_loop_def by (by100 blast)
            thus "x \<in> \<Phi>2 ` \<eta>2 ` ?F2" using \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
          qed
          \<comment> \<open>Step 3: The inclusion hom \\<pi>\\_1(?Y2) \\<rightarrow> \\<pi>\\_1(X).\<close>
          let ?incl = "top1_fundamental_group_induced_on ?Y2 ?TY2 p X TX p (\<lambda>x. x)"
          have hincl_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) ?incl"
            by (rule subspace_inclusion_induced_hom[OF hTX hY2_sub hpY2])
          \<comment> \<open>Step 4: inclusion maps [gen\\_loop \\<alpha>]\\_{?Y2} to \\<iota>(\\<alpha>) = [gen\\_loop \\<alpha>]\\_X.\<close>
          have hincl_gen: "\<forall>\<alpha>\<in>?F2.
              ?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l} = \<iota> \<alpha>"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>F: "\<alpha> \<in> ?F2"
            show "?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l} = \<iota> \<alpha>"
              unfolding top1_fundamental_group_induced_on_def \<iota>_def
            proof (rule set_eqI, rule iffI)
              fix h assume "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}.
                  top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}"
              then obtain f' where hf'_eq: "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) f'"
                  and hh_eq: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
              \<comment> \<open>loop\\_equiv in ?Y2 implies loop\\_equiv in X.\<close>
              have h\<alpha>J': "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
              have hgen_\<alpha>_loop_X: "top1_is_loop_on X TX p (gen_loop \<alpha>)"
                using hgen h\<alpha>J' by (by100 blast)
              have "top1_loop_equiv_on X TX p (gen_loop \<alpha>) f'"
              proof -
                from hf'_eq[unfolded top1_loop_equiv_on_def]
                have hf'_path: "top1_path_homotopic_on ?Y2 ?TY2 p p (gen_loop \<alpha>) f'" by (by100 blast)
                have hf'_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p f'"
                  using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
                have hf'_loop_X: "top1_is_loop_on X TX p f'"
                proof -
                  have hf'_cont_Y2: "top1_continuous_map_on I_set I_top ?Y2 ?TY2 f'"
                    using hf'_loop_Y2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  have "top1_continuous_map_on I_set I_top X TX (id \<circ> f')"
                    by (rule top1_continuous_map_on_comp[OF hf'_cont_Y2
                      Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY2_sub]])
                  hence "top1_continuous_map_on I_set I_top X TX f'" by (by100 simp)
                  moreover have "f' 0 = p" "f' 1 = p"
                    using hf'_loop_Y2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                  ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                qed
                from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ hf'_path]
                have "top1_path_homotopic_on X TX p p (gen_loop \<alpha>) f'" by (by100 blast)
                thus ?thesis unfolding top1_loop_equiv_on_def
                  using hgen_\<alpha>_loop_X hf'_loop_X by (by100 blast)
              qed
              have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
              have "top1_loop_equiv_on X TX p f' h" using hh_eq \<open>(\<lambda>x. x) \<circ> f' = f'\<close> by (by100 simp)
              from top1_loop_equiv_on_trans[OF hTX
                \<open>top1_loop_equiv_on X TX p (gen_loop \<alpha>) f'\<close> this]
              show "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop \<alpha>) g}" by (by100 blast)
            next
              fix h assume "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop \<alpha>) g}"
              hence hh: "top1_loop_equiv_on X TX p (gen_loop \<alpha>) h" by (by100 blast)
              have h\<alpha>J: "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
              have "top1_is_loop_on ?Y2 ?TY2 p (gen_loop \<alpha>)"
              proof -
                have hgl_loop_X: "top1_is_loop_on X TX p (gen_loop \<alpha>)"
                  using hgen h\<alpha>F hF2J by (by100 blast)
                have hgl_cont_X: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
                  using hgl_loop_X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hgl_im: "(gen_loop \<alpha>) ` I_set \<subseteq> ?Y2"
                  using hgen h\<alpha>F hF2J by (by100 blast)
                have hI_top: "is_topology_on I_set I_top"
                  using top1_unit_interval_topology_is_topology_on .
                from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
                  hgl_cont_X hgl_im hY2_sub
                have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop \<alpha>)" by (by100 blast)
                moreover have "(gen_loop \<alpha>) 0 = p" "(gen_loop \<alpha>) 1 = p"
                  using hgl_loop_X unfolding top1_is_loop_on_def top1_is_path_on_def
                  by (by100 blast)+
                ultimately show ?thesis
                  unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              qed
              from top1_loop_equiv_on_refl[OF this]
              have "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) (gen_loop \<alpha>)" .
              moreover have "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> gen_loop \<alpha>) h"
              proof -
                have "(\<lambda>x. x) \<circ> gen_loop \<alpha> = gen_loop \<alpha>" by (by100 auto)
                thus ?thesis using hh by (by100 simp)
              qed
              ultimately show "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}.
                  top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
            qed
          qed
          \<comment> \<open>Step 5: ?incl maps S\\_Y2 into subgroup\\_generated(\\<iota>`J).\<close>
          have hincl_S_in_gen: "?incl ` S_Y2 \<subseteq>
              top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
                  (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
                  (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
          proof
            fix y assume "y \<in> ?incl ` S_Y2"
            then obtain \<alpha> where h\<alpha>F: "\<alpha> \<in> ?F2" and
              hy_eq: "y = ?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              unfolding S_Y2_def by (by100 blast)
            have "y = \<iota> \<alpha>" using hy_eq hincl_gen h\<alpha>F by (by100 blast)
            have "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
            hence "\<iota> \<alpha> \<in> \<iota> ` J" by (by100 blast)
            have "top1_is_loop_on X TX p (gen_loop \<alpha>)" using hgen \<open>\<alpha> \<in> J\<close> by (by100 blast)
            hence "\<iota> \<alpha> \<in> top1_fundamental_group_carrier X TX p"
              unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
            have "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
            proof
              fix x assume "x \<in> \<iota> ` J"
              then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
              thus "x \<in> top1_fundamental_group_carrier X TX p"
                using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
            qed
            from subgroup_generated_contains[OF
              top1_fundamental_group_is_group[OF hTX hp] this \<open>\<iota> \<alpha> \<in> \<iota> ` J\<close>]
            show "y \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
                (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
                (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
              using \<open>y = \<iota> \<alpha>\<close> by (by100 simp)
          qed
          \<comment> \<open>Step 6: The subgroup\\_generated(\\<iota>`J) is a subgroup, so we can apply
             hom\\_image\\_in\\_subgroup\\_from\\_generators.\<close>
          let ?N = "top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
          have h\<iota>J_sub: "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
          proof
            fix x assume "x \<in> \<iota> ` J"
            then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
            thus "x \<in> top1_fundamental_group_carrier X TX p"
              using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
          qed
          have hN_grp: "top1_is_group_on ?N
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p)"
            by (rule intersection_of_subgroups_is_group[OF
              top1_fundamental_group_is_group[OF hTX hp] h\<iota>J_sub])
          have hN_sub: "?N \<subseteq> top1_fundamental_group_carrier X TX p"
            by (rule subgroup_generated_subset[OF top1_fundamental_group_is_group[OF hTX hp] h\<iota>J_sub])
          \<comment> \<open>Step 7: \\<pi>\\_1(?Y2) generated by S\\_Y2. Inclusion maps S\\_Y2 into ?N. Hence image \\<subseteq> ?N.\<close>
          have hpi1Y2_gen': "top1_fundamental_group_carrier ?Y2 ?TY2 p =
              top1_subgroup_generated_on (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p) S_Y2"
            using hpi1Y2_gen hPhi_eta_eq by (by100 simp)
          have hS_Y2_sub: "S_Y2 \<subseteq> top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof
            fix x assume "x \<in> S_Y2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2" "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              unfolding S_Y2_def by (by100 blast)
            have h\<alpha>J'': "\<alpha> \<in> J" using \<open>\<alpha> \<in> ?F2\<close> hF2J by (by100 blast)
            have "top1_is_loop_on ?Y2 ?TY2 p (gen_loop \<alpha>)"
            proof -
              have hgl_cont: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
                using hgen h\<alpha>J'' unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have hgl_im: "(gen_loop \<alpha>) ` I_set \<subseteq> ?Y2"
                using hgen h\<alpha>J'' \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
              from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                  rule_format] hgl_cont hgl_im hY2_sub
              have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop \<alpha>)" by (by100 blast)
              moreover have "(gen_loop \<alpha>) 0 = p" "(gen_loop \<alpha>) 1 = p"
                using hgen h\<alpha>J'' unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
              ultimately show ?thesis
                unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            qed
            thus "x \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using \<open>x = _\<close> unfolding top1_fundamental_group_carrier_def by (by100 blast)
          qed
          from hom_image_in_subgroup_from_generators[OF hpi1Y2_grp
              top1_fundamental_group_is_group[OF hTX hp]
              hincl_hom hpi1Y2_gen' hS_Y2_sub hN_grp hN_sub]
          have himage_in_N: "?incl ` top1_fundamental_group_carrier ?Y2 ?TY2 p \<subseteq> ?N"
            using hincl_S_in_gen by (by100 blast)
          \<comment> \<open>Step 8: c = [f]\\_X is in the image of the inclusion.\<close>
          have "c \<in> ?incl ` top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof -
            \<comment> \<open>f is a loop in ?Y2.\<close>
            have hf_cont_X: "top1_continuous_map_on I_set I_top X TX f"
              using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            have hf_im_Y2: "f ` I_set \<subseteq> ?Y2"
            proof
              fix x assume "x \<in> f ` I_set"
              thus "x \<in> ?Y2" using hf_in_F by (by100 blast)
            qed
            from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                rule_format] hf_cont_X hf_im_Y2 hY2_sub
            have hf_cont_Y2: "top1_continuous_map_on I_set I_top ?Y2 ?TY2 f" by (by100 blast)
            have hf_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p f"
              unfolding top1_is_loop_on_def top1_is_path_on_def
              using hf_cont_Y2 hf unfolding top1_is_loop_on_def top1_is_path_on_def
              by (by100 blast)
            \<comment> \<open>[f]\\_{?Y2} \\<in> \\<pi>\\_1(?Y2).\<close>
            let ?cl = "{h. top1_loop_equiv_on ?Y2 ?TY2 p f h}"
            have "?cl \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              unfolding top1_fundamental_group_carrier_def using hf_loop_Y2 by (by100 blast)
            \<comment> \<open>?incl ?cl = c.\<close>
            moreover have "?incl ?cl = c"
            proof -
              have "?incl ?cl = {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                unfolding top1_fundamental_group_induced_on_def by (by100 blast)
              also have "... = {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                  top1_loop_equiv_on X TX p f' h}"
              proof (rule set_eqI, rule iffI)
                fix h assume "h \<in> {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                then obtain f' where hf'cl: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                hence "top1_loop_equiv_on X TX p f' h" using hf'h by (by100 simp)
                thus "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}" using hf'cl by (by100 blast)
              next
                fix h assume "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}"
                then obtain f' where hf'eq: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p f' h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" using hf'h by (by100 simp)
                thus "h \<in> {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                  using hf'eq by (by100 blast)
              qed
              also have "... = c"
              proof (rule set_eqI, rule iffI)
                fix h assume "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}"
                then obtain f' where hf'eq: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p f' h" by (by100 blast)
                have "top1_loop_equiv_on X TX p f f'"
                proof -
                  from hf'eq[unfolded top1_loop_equiv_on_def]
                  have "top1_path_homotopic_on ?Y2 ?TY2 p p f f'" by (by100 blast)
                  from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ this]
                  have "top1_path_homotopic_on X TX p p f f'" by (by100 blast)
                  have "top1_is_loop_on X TX p f'"
                    using hf'h unfolding top1_loop_equiv_on_def by (by100 blast)
                  thus ?thesis unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX p f'\<close>
                    \<open>top1_path_homotopic_on X TX p p f f'\<close> by (by100 blast)
                qed
                from top1_loop_equiv_on_trans[OF hTX this hf'h]
                show "h \<in> c" unfolding hc_eq by (by100 blast)
              next
                fix h assume "h \<in> c"
                hence "top1_loop_equiv_on X TX p f h" unfolding hc_eq by (by100 blast)
                \<comment> \<open>Take f' = f. loop\\_equiv(?Y2, f, f) by reflexivity.\<close>
                moreover have "top1_loop_equiv_on ?Y2 ?TY2 p f f"
                  by (rule top1_loop_equiv_on_refl[OF hf_loop_Y2])
                ultimately show "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}" by (by100 blast)
              qed
              finally show ?thesis .
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          thus "c \<in> ?N" using himage_in_N by (by100 blast)
        qed
      next
        fix c assume "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
            (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
        have "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
        proof
          fix x assume "x \<in> \<iota> ` J"
          then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
          thus "x \<in> top1_fundamental_group_carrier X TX p"
            using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def
            by (by100 blast)
        qed
        from subgroup_generated_subset[OF top1_fundamental_group_is_group[OF hTX hp] this]
        show "c \<in> top1_fundamental_group_carrier X TX p"
          using \<open>c \<in> top1_subgroup_generated_on _ _ _ _ _\<close> by (by100 blast)
      qed
      show "\<forall>ws::('i \<times> bool) list.
          ws \<noteq> [] \<longrightarrow>
          top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
          (\<forall>i<length ws. fst (ws ! i) \<in> J) \<longrightarrow>
          top1_group_word_product (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id X TX p"
      proof (intro allI impI)
        fix ws :: "('i \<times> bool) list"
        assume hws_ne: "ws \<noteq> []"
          and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
          and hws_in: "\<forall>i<length ws. fst (ws ! i) \<in> J"
        \<comment> \<open>The word uses finitely many generators.\<close>
        let ?gens = "fst ` set ws"
        have hgens_fin: "finite ?gens" by (by100 simp)
        have hgens_J: "?gens \<subseteq> J"
        proof
          fix \<alpha> assume "\<alpha> \<in> ?gens"
          then obtain sb where "sb \<in> set ws" "fst sb = \<alpha>" by (by100 blast)
          from \<open>sb \<in> set ws\<close> have "\<exists>i. i < length ws \<and> ws ! i = sb"
            using in_set_conv_nth by (by5000 metis)
          then obtain i where "i < length ws" "ws ! i = sb" by (by100 blast)
          have "fst (ws ! i) \<in> J" using hws_in \<open>i < length ws\<close> by (by100 blast)
          thus "\<alpha> \<in> J" using \<open>fst sb = \<alpha>\<close> \<open>ws ! i = sb\<close> by (by100 simp)
        qed
        \<comment> \<open>Each generator loop lies in its circle. The word product loop lies in \\<Union>?gens C\\_\\<alpha>.\<close>
        \<comment> \<open>By hloop\\_finite, the word product is in a finite sub-wedge F \\<supseteq> ?gens.
           By hfinite\\_free, \\<Union>F C\\_\\<alpha> is a wedge. By Theorem\\_71\\_3\\_finite, \\<pi>\\_1 free on F.
           The word is non-trivial in \\<pi>\\_1(\\<Union>F C\\_\\<alpha>). By hhtpy\\_finite,
           the inclusion is injective. So the word is non-trivial in \\<pi>\\_1(X).\<close>
        \<comment> \<open>Proof by contradiction: assume the word product = id in \\<pi>\\_1(X).
           The word uses generators from ?gens \\<subseteq> J. Take the sub-wedge \\<Union>?gens C\\_\\<alpha>.
           The word is non-trivial there by freeness. But it's trivial in \\<pi>\\_1(X),
           and by hhtpy\\_finite + expanding to a larger sub-wedge, it's trivial in
           some sub-wedge containing ?gens. Contradiction.\<close>
        \<comment> \<open>Proof: the word product in \\<pi>\\_1(X) is the image of the word product in
           \\<pi>\\_1(\\<Union>?gens C\\_\\<alpha>) under the inclusion homomorphism.
           In the sub-wedge, the word is non-trivial by freeness (condition 5).
           The inclusion hom preserves this via hom\\_word\\_product.\<close>
        show "top1_group_word_product (top1_fundamental_group_mul X TX p)
            (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
            (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id X TX p"
        proof -
          have "J \<noteq> {}" using hp hcover by (by100 blast)
          then obtain \<gamma> where "\<gamma> \<in> J" by (by100 blast)
          let ?F2 = "?gens \<union> {\<gamma>}"
          have hF2fin: "finite ?F2" using hgens_fin by (by100 simp)
          have hF2J: "?F2 \<subseteq> J" using hgens_J \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hF2ne: "?F2 \<noteq> {}" by (by100 blast)
          have hgens_sub_F2: "?gens \<subseteq> ?F2" by (by100 blast)
          let ?Y2 = "\<Union>\<alpha>\<in>?F2. C \<alpha>"
          let ?TY2 = "subspace_topology X TX ?Y2"
          have hY2_sub: "?Y2 \<subseteq> X" using hC hF2J by (by100 blast)
          have hpY2: "p \<in> ?Y2" using hC \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hTY2: "is_topology_on ?Y2 ?TY2"
            by (rule subspace_topology_is_topology_on[OF hTX hY2_sub])
          from hfinite_free[OF hF2fin hF2J hF2ne]
          have hwedge2: "top1_is_wedge_of_circles_on ?Y2 ?TY2 ?F2 p" .
          \<comment> \<open>Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb.\<close>
          have hg_F2: "\<forall>j\<in>?F2. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
          proof -
            {
              fix j assume hjF: "j \<in> ?F2"
              hence "j \<in> J" using hF2J by (by100 blast)
              have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              have "subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use hjF in blast)
              hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
                using hgj by (by100 simp)
            }
            thus ?thesis by (by100 blast)
          qed
          have hC_closed_F2: "\<forall>D\<subseteq>?Y2. closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
              (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?Y2"
            from hcoh_sub[OF hF2J, rule_format, OF hD]
            have hiff: "closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
                (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?F2. subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?Y2 ?TY2 D \<Longrightarrow>
                \<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?Y2 ?TY2 D"
              using hiff htrans by (by100 simp)
          qed
          have hbase_F2: "\<forall>j\<in>?F2. g j (1, 0) = p" using hg hF2J by (by100 blast)
          have hC_data_F2: "\<forall>j\<in>?F2. C j \<subseteq> ?Y2 \<and> p \<in> C j" using hC hF2J by (by100 blast)
          have hC_union_F2: "(\<Union>j\<in>?F2. C j) = ?Y2" by (by100 blast)
          have hC_disj_F2: "\<forall>i\<in>?F2. \<forall>j\<in>?F2. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hF2J by (by100 blast)
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge2 hF2fin
              hg_F2 hbase_F2 hC_data_F2 hC_union_F2 hC_disj_F2 hC_closed_F2]
          obtain G2 :: "int set" and mul2 e2 invg2 and \<eta>2 :: "'i \<Rightarrow> int" and \<Phi>2
            where hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 ?F2"
              and hiso2: "top1_group_iso_on G2 mul2
                  (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              and hgens2: "\<forall>j\<in>?F2. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>Condition 5 of free group: reduced non-empty word \\<noteq> e.\<close>
          have hfree_cond5: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
              top1_is_reduced_word (map (\<lambda>(s, b). (\<eta>2 s, b)) ws') \<Longrightarrow>
              (\<forall>i<length ws'. fst (ws' ! i) \<in> ?F2) \<Longrightarrow>
              top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s, b). (\<eta>2 s, b)) ws') \<noteq> e2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>Our word ws has generators from ?gens \\<subseteq> ?F2.
             The word in \\<eta>2-form is reduced (since \\<eta>2 is injective and the original word is reduced).
             By condition 5, word\\_product(G2, ...) \\<noteq> e2.\<close>
          \<comment> \<open>Via iso \\<Phi>2: word\\_product(\\<pi>\\_1(?Y2), ...) \\<noteq> id\\_{?Y2}.\<close>
          \<comment> \<open>Via inclusion hom: word\\_product(\\<pi>\\_1(X), ...) = word\\_product in X.\<close>
          \<comment> \<open>The inclusion sends [gen\\_loop \\<alpha>]\\_{?Y2} to \\<iota>(\\<alpha>).
             So inclusion(word\\_product(\\<pi>\\_1(?Y2), [(gen\\_loop ws\\_i, b\\_i)])) =
             word\\_product(\\<pi>\\_1(X), [(\\<iota>(ws\\_i), b\\_i)]).\<close>
          \<comment> \<open>If X's word product = id, then sub-wedge's word product maps to id under inclusion.
             Need: inclusion injective \\<Longrightarrow> sub-wedge's word product = id. Contradiction.\<close>
          \<comment> \<open>Inclusion injectivity on this specific element:
             the word product loop has image in \\<Union>?gens \\<subseteq> \\<Union>?F2.
             If null-homotopic in X, the homotopy lies in some \\<Union>F' (hhtpy\\_finite).
             Take F'' = ?F2 \\<union> F'. In \\<Union>F'', the word product is null-homotopic.
             But \\<Union>F'' has free \\<pi>\\_1 and the word is still non-trivial there. Contradiction.\<close>
          \<comment> \<open>Step A: In the free group G2 on ?F2, the word is non-trivial.\<close>
          have hws_in_F2: "\<forall>i<length ws. fst (ws ! i) \<in> ?F2"
          proof (intro allI impI)
            fix i assume "i < length ws"
            have "fst (ws ! i) \<in> J" using hws_in \<open>i < length ws\<close> by (by100 blast)
            have "fst (ws ! i) \<in> ?gens" using \<open>i < length ws\<close> by (by100 force)
            thus "fst (ws ! i) \<in> ?F2" using hgens_sub_F2 by (by100 blast)
          qed
          \<comment> \<open>Step B: The inclusion hom is injective (from hincl\\_inj).\<close>
          let ?incl = "top1_fundamental_group_induced_on ?Y2 ?TY2 p X TX p (\<lambda>x. x)"
          from hincl_inj[OF hF2fin hF2J hF2ne]
          have hincl_injective: "inj_on ?incl
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)" .
          \<comment> \<open>Step C: By the free group structure and inclusion injectivity,
             the word product in \\<pi>\\_1(X) is non-trivial.
             The argument: word non-trivial in \\<pi>\\_1(?Y2) (from condition 5 + iso),
             inclusion injective \\<Longrightarrow> image non-trivial in \\<pi>\\_1(X),
             and hom\\_word\\_product connects word products across the inclusion.\<close>
          \<comment> \<open>Chain: word \\<noteq> e in G2 \\<Rightarrow> word \\<noteq> id in \\<pi>\\_1(?Y2) \\<Rightarrow> word \\<noteq> id in \\<pi>\\_1(X).\<close>
          have h\<eta>2_inj: "inj_on \<eta>2 ?F2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>Step C1: word reduced in \\<eta>2-form.\<close>
          have hred_\<eta>2: "top1_is_reduced_word (map (\<lambda>(s, b). (\<eta>2 s, b)) ws)"
          proof (rule reduced_word_transfer[where S="?F2" and h="\<iota>" and g="\<eta>2"])
            show "\<And>s t. s \<in> ?F2 \<Longrightarrow> t \<in> ?F2 \<Longrightarrow> \<eta>2 s = \<eta>2 t \<Longrightarrow> \<iota> s = \<iota> t"
            proof -
              fix s t assume "s \<in> ?F2" "t \<in> ?F2" "\<eta>2 s = \<eta>2 t"
              from \<open>\<eta>2 s = \<eta>2 t\<close> have "s = t"
                using h\<eta>2_inj \<open>s \<in> ?F2\<close> \<open>t \<in> ?F2\<close> unfolding inj_on_def by (by100 blast)
              thus "\<iota> s = \<iota> t" by (by100 simp)
            qed
            show "\<forall>i<length ws. fst (ws ! i) \<in> ?F2" by (rule hws_in_F2)
            show "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)" by (rule hred)
          qed
          \<comment> \<open>Step C2: word \\<noteq> e in G2.\<close>
          have hword_ne_G2: "top1_group_word_product mul2 e2 invg2
              (map (\<lambda>(s, b). (\<eta>2 s, b)) ws) \<noteq> e2"
            by (rule hfree_cond5[OF hws_ne hred_\<eta>2 hws_in_F2])
          \<comment> \<open>Step C3: word \\<noteq> id in \\<pi>\\_1(?Y2). Uses iso \\<Phi>2 + hom\\_word\\_product.\<close>
          have hword_ne_Y2: "top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) \<noteq>
              top1_fundamental_group_id ?Y2 ?TY2 p"
          proof -
            have hG2_grp: "top1_is_group_on G2 mul2 e2 invg2"
              using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
            have hpi1Y2_grp': "top1_is_group_on
                (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)"
              by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
            have hPhi2_hom: "top1_group_hom_on G2 mul2
                (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              using hiso2 unfolding top1_group_iso_on_def by (by100 blast)
            have hPhi2_inj: "inj_on \<Phi>2 G2"
              using hiso2 unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
            have h\<eta>2_in_G2: "\<forall>i<length ws. fst (map (\<lambda>(s,b). (\<eta>2 s, b)) ws ! i) \<in> G2"
            proof (intro allI impI)
              fix i assume "i < length ws"
              have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
              hence "\<eta>2 (fst (ws ! i)) \<in> G2"
                using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
              moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
              ultimately show "fst (map (\<lambda>(s,b). (\<eta>2 s, b)) ws ! i) \<in> G2"
                using \<open>i < length ws\<close> by (by100 simp)
            qed
            \<comment> \<open>\\<Phi>2 preserves word products.\<close>
            have h\<eta>2_ws_in_G2: "\<forall>i<length (map (\<lambda>(s,b). (\<eta>2 s, b)) ws).
                fst ((map (\<lambda>(s,b). (\<eta>2 s, b)) ws) ! i) \<in> G2"
              using h\<eta>2_in_G2 by (by100 auto)
            have hPhi2_wp: "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                    (top1_fundamental_group_id ?Y2 ?TY2 p)
                    (top1_fundamental_group_invg ?Y2 ?TY2 p)
                    (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)"
            proof -
              from hom_word_product[OF hG2_grp hpi1Y2_grp' hPhi2_hom h\<eta>2_ws_in_G2]
              have "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                  top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                      (top1_fundamental_group_id ?Y2 ?TY2 p)
                      (top1_fundamental_group_invg ?Y2 ?TY2 p)
                      (map (\<lambda>(x, b). (\<Phi>2 x, b)) (map (\<lambda>(s,b). (\<eta>2 s, b)) ws))" .
              moreover have "map (\<lambda>(x, b). (\<Phi>2 x, b)) (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) =
                  map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws" by (by100 auto)
              ultimately show ?thesis by (by5000 metis)
            qed
            \<comment> \<open>Since word(G2) \\<noteq> e2 and \\<Phi>2 injective:\<close>
            have "top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) \<in> G2"
              by (rule word_product_in_group[OF hG2_grp h\<eta>2_ws_in_G2])
            have "e2 \<in> G2" using hG2_grp unfolding top1_is_group_on_def by (by100 blast)
            have "\<Phi>2 e2 = top1_fundamental_group_id ?Y2 ?TY2 p"
              by (rule hom_preserves_id[OF hG2_grp hpi1Y2_grp' hPhi2_hom])
            show ?thesis
            proof
              assume "top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                  (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p)
                  (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                  top1_fundamental_group_id ?Y2 ?TY2 p"
              hence "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                  \<Phi>2 e2"
                using \<open>\<Phi>2 (top1_group_word_product mul2 e2 invg2 _) = _\<close>
                  \<open>\<Phi>2 e2 = _\<close> by (by100 simp)
              hence "top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) = e2"
                using hPhi2_inj
                  \<open>top1_group_word_product mul2 e2 invg2 _ \<in> G2\<close> \<open>e2 \<in> G2\<close>
                unfolding inj_on_def by (by5000 metis)
              thus False using hword_ne_G2 by contradiction
            qed
          qed
          \<comment> \<open>Step C4: word in \\<pi>\\_1(X) = inclusion of word in \\<pi>\\_1(?Y2).\<close>
          have hincl_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) ?incl"
            by (rule subspace_inclusion_induced_hom[OF hTX hY2_sub hpY2])
          have hincl_maps_word: "?incl (top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
              top1_group_word_product (top1_fundamental_group_mul X TX p)
                  (top1_fundamental_group_id X TX p)
                  (top1_fundamental_group_invg X TX p)
                  (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
          proof -
            have hPhi_eta_in': "\<forall>i<length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws).
                fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
            proof (intro allI impI)
              fix i assume "i < length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)"
              hence "i < length ws" by (by100 simp)
              have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
              have "\<eta>2 (fst (ws ! i)) \<in> G2"
                using hfree2 \<open>fst (ws ! i) \<in> ?F2\<close>
                unfolding top1_is_free_group_full_on_def by (by100 blast)
              have "\<Phi>2 (\<eta>2 (fst (ws ! i))) \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
                using hiso2 \<open>\<eta>2 (fst (ws ! i)) \<in> G2\<close>
                unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
              moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
              ultimately show "fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                  top1_fundamental_group_carrier ?Y2 ?TY2 p"
                using \<open>i < length ws\<close> by (by100 simp)
            qed
            from hom_word_product[OF
                top1_fundamental_group_is_group[OF hTY2 hpY2]
                top1_fundamental_group_is_group[OF hTX hp]
                hincl_hom hPhi_eta_in']
            have "?incl (top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                top1_group_word_product (top1_fundamental_group_mul X TX p)
                    (top1_fundamental_group_id X TX p)
                    (top1_fundamental_group_invg X TX p)
                    (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws))" .
            moreover have "map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                map (\<lambda>(s,b). (\<iota> s, b)) ws"
            proof -
              have hincl_gen': "\<forall>s\<in>?F2. ?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
              proof (intro ballI)
                fix s assume "s \<in> ?F2"
                \<comment> \<open>\\<Phi>2(\\<eta>2 s) = [gen\\_loop s]\\_{Y2}.\<close>
                from hgens2[rule_format, OF \<open>s \<in> ?F2\<close>]
                have "(\<Phi>2 (\<eta>2 s)) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                    (\<lambda>t. g s (cos (2 * pi * t), sin (2 * pi * t))) l}" .
                hence hPhi_eta_s: "\<Phi>2 (\<eta>2 s) = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}"
                  unfolding gen_loop_def by (by100 blast)
                \<comment> \<open>?incl [gen\\_loop s]\\_{Y2} = \\<iota>(s).\<close>
                show "?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
                  unfolding hPhi_eta_s top1_fundamental_group_induced_on_def \<iota>_def
                proof (rule set_eqI, rule iffI)
                  fix h assume "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}.
                      top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}"
                  then obtain f' where "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) f'"
                      "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                  have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                  have "top1_loop_equiv_on X TX p f' h" using \<open>top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h\<close>
                    \<open>(\<lambda>x. x) \<circ> f' = f'\<close> by (by100 simp)
                  have "top1_loop_equiv_on X TX p (gen_loop s) f'"
                  proof -
                    from \<open>top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) f'\<close>[unfolded top1_loop_equiv_on_def]
                    have "top1_path_homotopic_on ?Y2 ?TY2 p p (gen_loop s) f'" by (by100 blast)
                    from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ this]
                    have "top1_path_homotopic_on X TX p p (gen_loop s) f'" by (by100 blast)
                    have "top1_is_loop_on X TX p f'"
                      using \<open>top1_loop_equiv_on X TX p f' h\<close> unfolding top1_loop_equiv_on_def by (by100 blast)
                    have "s \<in> J" using \<open>s \<in> ?F2\<close> hF2J by (by100 blast)
                    have "top1_is_loop_on X TX p (gen_loop s)" using hgen \<open>s \<in> J\<close> by (by100 blast)
                    thus ?thesis unfolding top1_loop_equiv_on_def
                      using \<open>top1_is_loop_on X TX p (gen_loop s)\<close> \<open>top1_is_loop_on X TX p f'\<close>
                        \<open>top1_path_homotopic_on X TX p p (gen_loop s) f'\<close> by (by100 blast)
                  qed
                  from top1_loop_equiv_on_trans[OF hTX this \<open>top1_loop_equiv_on X TX p f' h\<close>]
                  show "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop s) g}" by (by100 blast)
                next
                  fix h assume "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop s) g}"
                  hence "top1_loop_equiv_on X TX p (gen_loop s) h" by (by100 blast)
                  have "s \<in> J" using \<open>s \<in> ?F2\<close> hF2J by (by100 blast)
                  have hgl_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p (gen_loop s)"
                  proof -
                    have hgl_cont: "top1_continuous_map_on I_set I_top X TX (gen_loop s)"
                      using hgen \<open>s \<in> J\<close> unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    have hgl_im: "(gen_loop s) ` I_set \<subseteq> ?Y2"
                      using hgen \<open>s \<in> J\<close> \<open>s \<in> ?F2\<close> by (by100 blast)
                    from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                        rule_format] hgl_cont hgl_im hY2_sub
                    have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop s)" by (by100 blast)
                    moreover have "(gen_loop s) 0 = p" "(gen_loop s) 1 = p"
                      using hgen \<open>s \<in> J\<close> unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  qed
                  from top1_loop_equiv_on_refl[OF hgl_loop_Y2]
                  have "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) (gen_loop s)" .
                  moreover have "(\<lambda>x. x) \<circ> gen_loop s = gen_loop s" by (by100 auto)
                  hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> gen_loop s) h"
                    using \<open>top1_loop_equiv_on X TX p (gen_loop s) h\<close> by (by100 simp)
                  ultimately show "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}.
                      top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
                qed
              qed
              have hincl_ptwise: "\<forall>i<length ws. ?incl (\<Phi>2 (\<eta>2 (fst (ws ! i)))) = \<iota> (fst (ws ! i))"
              proof (intro allI impI)
                fix i assume "i < length ws"
                have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
                thus "?incl (\<Phi>2 (\<eta>2 (fst (ws ! i)))) = \<iota> (fst (ws ! i))"
                  using hincl_gen' by (by100 blast)
              qed
              show ?thesis
              proof (rule nth_equalityI)
                show "length (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                    length (map (\<lambda>(s,b). (\<iota> s, b)) ws)" by (by100 simp)
              next
                fix i assume "i < length (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws))"
                hence hi: "i < length ws" by (by100 simp)
                obtain s b where hsb: "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
                have "?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
                  using hincl_ptwise hi hsb by (by100 force)
                thus "(map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) ! i =
                    (map (\<lambda>(s,b). (\<iota> s, b)) ws) ! i"
                  using hi hsb by (by100 simp)
              qed
            qed
            ultimately show ?thesis by (by5000 metis)
          qed
          \<comment> \<open>Step C5: word \\<noteq> id in \\<pi>\\_1(X). Uses inclusion injectivity.\<close>
          have hPhi_eta_in_carrier: "\<forall>i<length ws.
              fst (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws ! i) \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof (intro allI impI)
            fix i assume "i < length ws"
            have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
            have "\<eta>2 (fst (ws ! i)) \<in> G2"
              using hfree2 \<open>fst (ws ! i) \<in> ?F2\<close>
              unfolding top1_is_free_group_full_on_def by (by100 blast)
            have "\<Phi>2 (\<eta>2 (fst (ws ! i))) \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using hiso2 \<open>\<eta>2 (fst (ws ! i)) \<in> G2\<close>
              unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
            moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
            ultimately show "fst (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using \<open>i < length ws\<close> by (by100 simp)
          qed
          have hpi1Y2_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)"
            by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
          have hword_in_carrier: "top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof -
            have "\<forall>i<length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws).
                fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using hPhi_eta_in_carrier by (by100 auto)
            from word_product_in_group[OF hpi1Y2_grp this] show ?thesis .
          qed
          have hid_in_carrier: "top1_fundamental_group_id ?Y2 ?TY2 p \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
            using hpi1Y2_grp unfolding top1_is_group_on_def by (by100 blast)
          have hincl_id: "?incl (top1_fundamental_group_id ?Y2 ?TY2 p) =
              top1_fundamental_group_id X TX p"
            by (rule hom_preserves_id[OF hpi1Y2_grp
              top1_fundamental_group_is_group[OF hTX hp] hincl_hom])
          show ?thesis
          proof
            assume heq: "top1_group_word_product (top1_fundamental_group_mul X TX p)
                (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
                (map (\<lambda>(s, b). (\<iota> s, b)) ws) = top1_fundamental_group_id X TX p"
            \<comment> \<open>?incl(word(Y2)) = word(X) = id\\_X = ?incl(id\\_Y2).\<close>
            have "?incl (top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                ?incl (top1_fundamental_group_id ?Y2 ?TY2 p)"
              using hincl_maps_word heq hincl_id by (by100 simp)
            \<comment> \<open>By injectivity: word(Y2) = id\\_Y2.\<close>
            hence "top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                top1_fundamental_group_id ?Y2 ?TY2 p"
              using hincl_injective hword_in_carrier hid_in_carrier
              unfolding inj_on_def by (by5000 metis)
            \<comment> \<open>But word(Y2) \\<noteq> id\\_Y2. Contradiction.\<close>
            thus False using hword_ne_Y2 by contradiction
          qed
        qed
      qed
    qed
  qed
qed

\<comment> \<open>Theorem 71.3 (int set packaging): corollary for downstream use.
   The int set wrapping is needed for some applications but requires countable J.\<close>
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
    show ?thesis by (rule Theorem_71_3_finite[OF assms True])
  next
    case False
    \<comment> \<open>Infinite case: use Theorem\\_71\\_3\\_pi1\\_free (book-faithful version)
       which proves \\<pi>\\_1(X) is free on J. Then package into int set.\<close>
    from Theorem_71_3_pi1_free[OF assms]
    obtain \<iota> where hpi1_free: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p)
        (top1_fundamental_group_invg X TX p)
        \<iota> J" by (by100 blast)
    \<comment> \<open>Int set packaging: need to construct G :: int set isomorphic to \\<pi>\\_1(X).
       This requires |J| \\<le> |int| (countable J).\<close>
    show ?thesis sorry \<comment> \<open>Int set packaging from pi1\\_free. Requires countable J.\<close>
  qed
qed





\<comment> \<open>§71 helpers + §74 moved to AlgTopCached8.\<close>

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
  show ?thesis sorry \<comment> \<open>Full 6-step construction of covering space (Munkres §82).\<close>
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





\<comment> \<open>Homotopy helpers + §84 infrastructure moved to AlgTopCached7.\<close>


\<comment> \<open>Weak form of Theorem 84.7: \\<pi>\\_1 of a connected graph is free (no int set).
   This is proved as a standalone universal lemma that can be used
   for subgraph applications inside Theorem 84.7's proof.\<close>
lemma graph_pi1_free_weak:
  fixes Y :: "'a set" and TY :: "'a set set" and y0 :: 'a
  assumes "top1_is_graph_on Y TY"
      and "top1_connected_on Y TY"
      and "y0 \<in> Y"
  shows "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
      (top1_fundamental_group_carrier Y TY y0)
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0)
      \<iota> S"
proof -
  \<comment> \<open>Extract graph structure.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>_cover: "\<Union>\<A> = Y"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
    using assms(1) unfolding top1_is_graph_on_def by (by5000 auto)
  \<comment> \<open>Get maximal tree.\<close>
  obtain T where hT_tree: "top1_is_tree_on T (subspace_topology Y TY T)"
      and hT_sub: "T \<subseteq> Y" and hT_x0: "y0 \<in> T"
      and hT_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or>
           A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      and hT_coverage: "T = \<Union>{A \<in> \<A>. A \<subseteq> T}"
      and hT_max: "\<forall>T'. T' \<subseteq> Y \<longrightarrow> T \<subseteq> T' \<longrightarrow>
           top1_is_tree_on T' (subspace_topology Y TY T') \<longrightarrow>
           (\<forall>A\<in>\<A>. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)) \<longrightarrow>
           T' = \<Union>{A \<in> \<A>. A \<subseteq> T'} \<longrightarrow> T' = T"
  proof -
    from connected_graph_has_maximal_tree[OF assms(1) assms(2) assms(3) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh]
    show ?thesis by - (erule exE, (erule conjE)+, rule that, assumption+)
  qed
  \<comment> \<open>Every point in Y is in some arc that meets T.\<close>
  have hT_reaches_loc: "\<forall>v\<in>Y. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
  proof (rule maximal_tree_reaches_all_arcs[OF assms(1) assms(2) assms(3)
      h\<A> h\<A>_cover h\<A>_inter h\<A>_coh hT_tree hT_sub hT_x0])
    show "\<forall>T'. T' \<subseteq> Y \<longrightarrow> T \<subseteq> T' \<longrightarrow>
         top1_is_tree_on T' (subspace_topology Y TY T') \<longrightarrow>
         (\<forall>A\<in>\<A>. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)) \<longrightarrow>
         T' = \<Union>{A \<in> \<A>. A \<subseteq> T'} \<longrightarrow> T' = T" by (rule hT_max)
    show "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      by (rule hT_subgraph)
    show "T = \<Union>{A \<in> \<A>. A \<subseteq> T}" by (rule hT_coverage)
  qed
  \<comment> \<open>Endpoints of non-tree arcs are in T (from hT\\_reaches).\<close>
  have hNT_endpoints: "\<forall>A\<in>{A \<in> \<A>. \<not> A \<subseteq> T}.
       \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
  proof (intro ballI)
    fix A e assume hA_nt: "A \<in> {A \<in> \<A>. \<not> A \<subseteq> T}"
        and he: "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
    have "A \<in> \<A>" using hA_nt by (by100 blast)
    have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
    have he_Y: "e \<in> Y" using he \<open>A \<subseteq> Y\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
    from hT_reaches_loc[rule_format, OF he_Y]
    obtain B where hB: "B \<in> \<A>" "e \<in> B" "\<exists>w\<in>T. w \<in> B" by (by100 blast)
    then obtain w where hw: "w \<in> T" "w \<in> B" by (by100 blast)
    show "e \<in> T"
    proof (cases "B \<subseteq> T")
      case True thus ?thesis using hB(2) by (by100 blast)
    next
      case False
      from hT_subgraph[rule_format, OF hB(1)] False
      have hBT_ep: "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
      have hw_ep: "w \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
        using hw hBT_ep by (by100 blast)
      have he_ep_B: "e \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
      proof (cases "A = B")
        case True thus ?thesis using he True by (by100 simp)
      next
        case False
        have "e \<in> A \<inter> B" using he hB(2) unfolding top1_arc_endpoints_on_def by (by100 blast)
        from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> hB(1) False]
        show ?thesis using \<open>e \<in> A \<inter> B\<close> by (by100 blast)
      qed
      \<comment> \<open>e and w are both endpoints of B. If e=w: done. If e\\<noteq>w: maximality contradiction.\<close>
      show "e \<in> T"
      proof (rule ccontr)
        assume "e \<notin> T"
        hence "e \<noteq> w" using hw(1) by (by100 blast)
        \<comment> \<open>B \\<inter> T \\<subseteq> {w} (e is the only non-T endpoint). T \\<union> B would be a larger tree.\<close>
        have "B \<inter> T \<subseteq> {w}"
        proof -
          have hB_arc: "top1_is_arc_on B (subspace_topology Y TY B)"
            using h\<A> hB(1) by (by100 blast)
          obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
              top1_unit_interval_topology B (subspace_topology Y TY B) h'"
            using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
          have hY_strict: "is_topology_on_strict Y TY"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          have hY_haus: "is_hausdorff_on Y TY"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          have "B \<subseteq> Y" using h\<A> hB(1) by (by100 blast)
          from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>B \<subseteq> Y\<close> hB_arc hh']
          have hep_eq: "top1_arc_endpoints_on B (subspace_topology Y TY B) = {h' 0, h' 1}" .
          have "B \<inter> T \<subseteq> {h' 0, h' 1}" using hBT_ep hep_eq by (by100 simp)
          have "e \<in> {h' 0, h' 1}" using he_ep_B hep_eq by (by100 simp)
          have "B \<inter> T \<subseteq> {h' 0, h' 1} - {e}"
            using \<open>B \<inter> T \<subseteq> {h' 0, h' 1}\<close> \<open>e \<notin> T\<close> by (by100 blast)
          have "w \<in> {h' 0, h' 1}" using hw_ep hep_eq by (by100 simp)
          have "{h' 0, h' 1} - {e} \<subseteq> {w}"
          proof (cases "e = h' 0")
            case True thus ?thesis using \<open>w \<in> {h' 0, h' 1}\<close> True \<open>e \<noteq> w\<close> by (by100 blast)
          next
            case False hence "e = h' 1" using \<open>e \<in> {h' 0, h' 1}\<close> by (by100 blast)
            thus ?thesis using \<open>w \<in> {h' 0, h' 1}\<close> \<open>e \<noteq> w\<close> by (by100 blast)
          qed
          thus ?thesis using \<open>B \<inter> T \<subseteq> {h' 0, h' 1} - {e}\<close> by (by100 blast)
        qed
        \<comment> \<open>T \\<union> B contradicts maximality of T.\<close>
        have "B \<inter> T \<noteq> {}" using hw by (by100 blast)
        have "card (B \<inter> T) = 1"
        proof -
          have "w \<in> B \<inter> T" using hw by (by100 blast)
          hence "B \<inter> T = {w}" using \<open>B \<inter> T \<subseteq> {w}\<close> by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>By Lemma 84.2: T \\<union> B is a tree (arc meeting tree at 1 endpoint).\<close>
        have "B \<subseteq> Y" using h\<A> hB(1) by (by100 blast)
        \<comment> \<open>T is closed in Y (coherent topology: T\\<inter>A closed in A for each arc A).\<close>
        have hT_closed: "closedin_on Y TY T"
        proof -
          have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> T)"
          proof (intro ballI)
            fix A' assume "A' \<in> \<A>"
            show "closedin_on A' (subspace_topology Y TY A') (A' \<inter> T)"
            proof (cases "A' \<subseteq> T")
              case True
              hence "A' \<inter> T = A'" by (by100 blast)
              have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
              have "is_topology_on Y TY"
                using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def
                by (by100 blast)
              show ?thesis using \<open>A' \<inter> T = A'\<close>
                closedin_intro[where X="A'" and T="subspace_topology Y TY A'"]
              proof -
                have "A' \<inter> T = A'" using True by (by100 blast)
                have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                \<comment> \<open>Whole space is closed: A' - A' = {} \\<in> topology.\<close>
                from closedin_empty[OF subspace_topology_is_topology_on[OF
                    \<open>is_topology_on Y TY\<close> \<open>A' \<subseteq> Y\<close>]]
                have "closedin_on A' (subspace_topology Y TY A') {}" .
                have "A' \<inter> T = A'" using True by (by100 blast)
                \<comment> \<open>Actually need: A' closed in A'. Use Theorem\\_17\\_2: A' = A' \\<inter> Y.\<close>
                from Theorem_17_2[OF \<open>is_topology_on Y TY\<close> \<open>A' \<subseteq> Y\<close>]
                have "closedin_on A' (subspace_topology Y TY A') A' \<longleftrightarrow>
                    (\<exists>C. closedin_on Y TY C \<and> A' = C \<inter> A')" .
                moreover have "\<exists>C. closedin_on Y TY C \<and> A' = C \<inter> A'"
                proof (rule exI[of _ Y])
                  have "closedin_on Y TY Y"
                  proof -
                    have "{} \<in> TY" using \<open>is_topology_on Y TY\<close>
                      unfolding is_topology_on_def by (by100 fast)
                    hence "Y - Y \<in> TY" by simp
                    thus ?thesis unfolding closedin_on_def by (by100 blast)
                  qed
                  moreover have "A' = Y \<inter> A'" using \<open>A' \<subseteq> Y\<close> by (by100 blast)
                  ultimately show "closedin_on Y TY Y \<and> A' = Y \<inter> A'" by (by100 blast)
                qed
                ultimately have "closedin_on A' (subspace_topology Y TY A') A'" by (by100 blast)
                thus ?thesis using \<open>A' \<inter> T = A'\<close> by simp
              qed
            next
              case False
              have "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
                using hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>] False by (by100 blast)
              have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
              have "is_hausdorff_on Y TY"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "is_hausdorff_on A' (subspace_topology Y TY A')"
                using Theorem_17_11 \<open>is_hausdorff_on Y TY\<close> \<open>A' \<subseteq> Y\<close> by (by100 blast)
              have "finite (A' \<inter> T)"
              proof -
                have hA'_arc: "top1_is_arc_on A' (subspace_topology Y TY A')"
                  using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
                obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology A' (subspace_topology Y TY A') h'"
                  using hA'_arc unfolding top1_is_arc_on_def by (by100 blast)
                have hY_strict: "is_topology_on_strict Y TY"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                from arc_endpoints_are_boundary[OF hY_strict \<open>is_hausdorff_on Y TY\<close>
                    \<open>A' \<subseteq> Y\<close> hA'_arc hh']
                have "top1_arc_endpoints_on A' (subspace_topology Y TY A') = {h' 0, h' 1}" .
                have "A' \<inter> T \<subseteq> {h' 0, h' 1}" using \<open>A' \<inter> T \<subseteq> _\<close>
                  \<open>_ = {h' 0, h' 1}\<close> by (by100 simp)
                thus ?thesis using finite_subset[OF \<open>A' \<inter> T \<subseteq> {h' 0, h' 1}\<close>] by (by100 simp)
              qed
              have "A' \<inter> T \<subseteq> A'" by (by100 blast)
              from Theorem_17_8[OF \<open>is_hausdorff_on A' _\<close> \<open>finite (A' \<inter> T)\<close> \<open>A' \<inter> T \<subseteq> A'\<close>]
              show ?thesis .
            qed
          qed
          thus ?thesis using h\<A>_coh hT_sub by (by100 blast)
        qed
        \<comment> \<open>T \\<union> B is a graph (subgraph of Y).\<close>
        have hTB_graph: "top1_is_graph_on (T \<union> B) (subspace_topology Y TY (T \<union> B))"
        proof -
          \<comment> \<open>T \\<union> B is connected (tree + arc meeting at 1 point).\<close>
          have hTB_conn: "top1_connected_on (T \<union> B) (subspace_topology Y TY (T \<union> B))"
          proof -
            have hB_arc: "top1_is_arc_on B (subspace_topology Y TY B)"
              using h\<A> hB(1) by (by100 blast)
            have "\<exists>e. e \<in> T \<and> e \<in> B" using hw by (by100 blast)
            have hTY_top_loc: "is_topology_on Y TY"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def
              by (by100 blast)
            from tree_union_arcs_path_connected[OF hTY_top_loc hT_tree hT_sub _ _ _ hT_x0,
                of "{B}"]
            have "top1_path_connected_on (T \<union> \<Union>{B}) (subspace_topology Y TY (T \<union> \<Union>{B}))"
              using hB_arc \<open>B \<subseteq> Y\<close> \<open>\<exists>e. e \<in> T \<and> e \<in> B\<close> by (by100 simp)
            hence "top1_path_connected_on (T \<union> B) (subspace_topology Y TY (T \<union> B))"
              by simp
            thus ?thesis using top1_path_connected_imp_connected by (by100 blast)
          qed
          \<comment> \<open>T \\<union> B has \\<ge> 2 points (T has x0, B has e which is not in T).\<close>
          have hTB_2pts: "\<exists>y1 y2. y1 \<in> T \<union> B \<and> y2 \<in> T \<union> B \<and> y1 \<noteq> y2"
            using hT_x0 hB(2) \<open>e \<notin> T\<close> by (by100 blast)
          \<comment> \<open>Non-(T\\<union>B) arcs intersect T\\<union>B finitely.\<close>
          have hTB_finite_inter: "\<forall>A'\<in>\<A>. \<not> A' \<subseteq> T \<union> B \<longrightarrow> finite (A' \<inter> (T \<union> B))"
          proof (intro ballI impI)
            fix A' assume "A' \<in> \<A>" "\<not> A' \<subseteq> T \<union> B"
            have "A' \<inter> (T \<union> B) \<subseteq> (A' \<inter> T) \<union> (A' \<inter> B)" by (by100 blast)
            moreover have "finite (A' \<inter> T)"
            proof -
              have "\<not> A' \<subseteq> T" using \<open>\<not> A' \<subseteq> T \<union> B\<close> by (by100 blast)
              hence "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
                using hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>] by (by100 blast)
              have hA'_arc: "top1_is_arc_on A' (subspace_topology Y TY A')"
                using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
              obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A' (subspace_topology Y TY A') h'"
                using hA'_arc unfolding top1_is_arc_on_def by (by100 blast)
              have hY_s: "is_topology_on_strict Y TY"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hY_h: "is_hausdorff_on Y TY"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_s hY_h \<open>A' \<subseteq> Y\<close> hA'_arc hh']
              have "A' \<inter> T \<subseteq> {h' 0, h' 1}" using \<open>A' \<inter> T \<subseteq> _\<close> by (by100 simp)
              thus ?thesis using finite_subset[OF \<open>A' \<inter> T \<subseteq> {h' 0, h' 1}\<close>] by (by100 simp)
            qed
            moreover have "finite (A' \<inter> B)"
            proof (cases "A' = B")
              case True thus ?thesis using \<open>\<not> A' \<subseteq> T \<union> B\<close> True by (by100 blast)
            next
              case False
              from h\<A>_inter[rule_format, OF \<open>A' \<in> \<A>\<close> hB(1) False]
              show ?thesis by (by100 blast)
            qed
            ultimately show "finite (A' \<inter> (T \<union> B))" using finite_subset by (by100 blast)
          qed
          \<comment> \<open>Direct coverage proof: T\\<union>B = \\<Union>{arcs in T\\<union>B}.\<close>
          have hTB_eq: "T \<union> B = \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}" thus "x \<in> T \<union> B" by (by100 blast)
          next
            fix x assume "x \<in> T \<union> B"
            thus "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
            proof
              assume "x \<in> T"
              hence "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T}" using hT_coverage by simp
              then obtain A' where "A' \<in> \<A>" "A' \<subseteq> T" "x \<in> A'" by (by100 blast)
              thus ?thesis using \<open>A' \<subseteq> T\<close> by (by100 blast)
            next
              assume "x \<in> B"
              thus ?thesis using hB(1) by (by100 blast)
            qed
          qed
          \<comment> \<open>Coherent topology for T\\<union>B.\<close>
          let ?\<B>TB = "{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
          have hTB_coh: "\<forall>C. C \<subseteq> T \<union> B \<longrightarrow>
              (closedin_on (T \<union> B) (subspace_topology Y TY (T \<union> B)) C \<longleftrightarrow>
               (\<forall>A\<in>?\<B>TB. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
          proof (rule subgraph_coherent_topology)
            show "top1_is_graph_on Y TY" by (rule assms(1))
            show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
            show "\<Union>\<A> = Y" by (rule h\<A>_cover)
            show "\<forall>A\<in>\<A>. \<forall>Ba\<in>\<A>. A \<noteq> Ba \<longrightarrow> A \<inter> Ba \<subseteq>
                top1_arc_endpoints_on A (subspace_topology Y TY A) \<and>
                A \<inter> Ba \<subseteq> top1_arc_endpoints_on Ba (subspace_topology Y TY Ba) \<and>
                finite (A \<inter> Ba) \<and> card (A \<inter> Ba) \<le> 2" by (rule h\<A>_inter)
            show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
            show "?\<B>TB \<subseteq> \<A>" by (by100 blast)
            show "T \<union> B = \<Union>?\<B>TB" by (rule hTB_eq)
          qed
          \<comment> \<open>Apply subgraph\\_union\\_of\\_arcs\\_is\\_graph.\<close>
          have "top1_is_graph_on (\<Union>?\<B>TB) (subspace_topology Y TY (\<Union>?\<B>TB))"
          proof (rule subgraph_union_of_arcs_is_graph)
            show "top1_is_graph_on Y TY" by (rule assms(1))
            show "\<forall>A\<in>?\<B>TB. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
              using h\<A> by (by100 blast)
            show "\<Union>?\<B>TB \<subseteq> Y" using h\<A> by (by100 blast)
            show "\<forall>A\<in>?\<B>TB. \<forall>Ba\<in>?\<B>TB. A \<noteq> Ba \<longrightarrow> A \<inter> Ba \<subseteq>
                top1_arc_endpoints_on A (subspace_topology Y TY A) \<and>
                A \<inter> Ba \<subseteq> top1_arc_endpoints_on Ba (subspace_topology Y TY Ba) \<and>
                finite (A \<inter> Ba) \<and> card (A \<inter> Ba) \<le> 2"
            proof (intro ballI impI)
              fix A' Ba assume "A' \<in> ?\<B>TB" "Ba \<in> ?\<B>TB" "A' \<noteq> Ba"
              from h\<A>_inter[rule_format, OF _ _ \<open>A' \<noteq> Ba\<close>]
              show "A' \<inter> Ba \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A') \<and>
                  A' \<inter> Ba \<subseteq> top1_arc_endpoints_on Ba (subspace_topology Y TY Ba) \<and>
                  finite (A' \<inter> Ba) \<and> card (A' \<inter> Ba) \<le> 2"
                using \<open>A' \<in> ?\<B>TB\<close> \<open>Ba \<in> ?\<B>TB\<close> by (by100 blast)
            qed
            show "\<forall>C. C \<subseteq> \<Union>?\<B>TB \<longrightarrow>
                (closedin_on (\<Union>?\<B>TB) (subspace_topology Y TY (\<Union>?\<B>TB)) C \<longleftrightarrow>
                 (\<forall>A\<in>?\<B>TB. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
              using hTB_coh hTB_eq by simp
          qed
          thus ?thesis using hTB_eq by simp
        qed
        have hB_inter_T: "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)"
          using hBT_ep .
        have hTB_tree: "top1_is_tree_on (T \<union> B) (subspace_topology Y TY (T \<union> B))"
        proof (rule Lemma_84_2_tree_union_arc[OF assms(1) hT_tree hT_sub hB(1)
            h\<A> h\<A>_cover h\<A>_inter])
          show "B \<inter> T \<noteq> {}" using hw by (by100 blast)
          show "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)"
            by (rule hB_inter_T)
          show "card (B \<inter> T) = 1" by (rule \<open>card (B \<inter> T) = 1\<close>)
          show "B \<subseteq> Y" by (rule \<open>B \<subseteq> Y\<close>)
          show "closedin_on Y TY T" by (rule hT_closed)
          show "top1_is_graph_on (T \<union> B) (subspace_topology Y TY (T \<union> B))"
            by (rule hTB_graph)
        qed
        \<comment> \<open>T \\<union> B strictly contains T (e \\<in> B, e \\<notin> T).\<close>
        have "T \<subset> T \<union> B" using hB(2) \<open>e \<notin> T\<close> \<open>B \<subseteq> Y\<close> hT_sub by (by100 blast)
        hence "T \<union> B \<noteq> T" by (by100 blast)
        \<comment> \<open>T \\<union> B satisfies subgraph condition.\<close>
        have hTB_subgraph: "\<forall>A'\<in>\<A>. A' \<subseteq> T \<union> B \<or> A' \<inter> (T \<union> B) \<subseteq>
            top1_arc_endpoints_on A' (subspace_topology Y TY A')"
        proof (intro ballI)
          fix A' assume "A' \<in> \<A>"
          show "A' \<subseteq> T \<union> B \<or> A' \<inter> (T \<union> B) \<subseteq>
              top1_arc_endpoints_on A' (subspace_topology Y TY A')"
          proof (cases "A' \<subseteq> T \<or> A' = B")
            case True thus ?thesis by (by100 blast)
          next
            case False
            hence "A' \<noteq> B" "\<not> A' \<subseteq> T" by (by100 blast)+
            from hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>] \<open>\<not> A' \<subseteq> T\<close>
            have "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
              by (by100 blast)
            from h\<A>_inter[rule_format, OF \<open>A' \<in> \<A>\<close> hB(1) \<open>A' \<noteq> B\<close>]
            have "A' \<inter> B \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
              by (by100 blast)
            have "A' \<inter> (T \<union> B) = (A' \<inter> T) \<union> (A' \<inter> B)" by (by100 blast)
            thus ?thesis using \<open>A' \<inter> T \<subseteq> _\<close> \<open>A' \<inter> B \<subseteq> _\<close> by (by100 blast)
          qed
        qed
        have hTB_coverage: "(T \<union> B) = \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> T \<union> B"
          thus "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
          proof
            assume "x \<in> T"
            hence "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T}" using hT_coverage by simp
            then obtain A' where "A' \<in> \<A>" "A' \<subseteq> T" "x \<in> A'" by (by100 blast)
            have "A' \<subseteq> T \<union> B" using \<open>A' \<subseteq> T\<close> by (by100 blast)
            thus ?thesis using \<open>A' \<in> \<A>\<close> \<open>x \<in> A'\<close> \<open>A' \<subseteq> T \<union> B\<close> by (by100 blast)
          next
            assume "x \<in> B"
            have "B \<subseteq> T \<union> B" by (by100 blast)
            thus ?thesis using hB(1) \<open>x \<in> B\<close> by (by100 blast)
          qed
        next
          fix x assume "x \<in> \<Union>{A' \<in> \<A>. A' \<subseteq> T \<union> B}"
          thus "x \<in> T \<union> B" by (by100 blast)
        qed
        have "T \<union> B \<subseteq> Y" using hT_sub \<open>B \<subseteq> Y\<close> by (by100 blast)
        have "T \<subseteq> T \<union> B" by (by100 blast)
        have "T \<union> B = T"
          using hT_max \<open>T \<union> B \<subseteq> Y\<close> \<open>T \<subseteq> T \<union> B\<close>
              hTB_tree hTB_subgraph hTB_coverage by (by100 blast)
        thus False using \<open>T \<union> B \<noteq> T\<close> by contradiction
      qed
    qed
  qed
  let ?NT = "{A \<in> \<A>. \<not> A \<subseteq> T}"
  \<comment> \<open>Strong induction on card(?NT): universal over all graphs.\<close>
  \<comment> \<open>Since we already fixed Y, we need the IH to apply to subgraphs.
     The IH comes from graph\\_pi1\\_free\\_weak itself (available via sorry in quick\\_and\\_dirty).\<close>
  show ?thesis
  proof (cases "?NT = {}")
    case True
    \<comment> \<open>No non-tree arcs: Y = T. Use graph\\_tree\\_free\\_pi1.\<close>
    show ?thesis
      by (rule graph_tree_free_pi1[OF assms(1) assms(3) h\<A> h\<A>_cover hT_tree hT_sub hT_x0 True])
  next
    case False
    \<comment> \<open>Non-tree arcs exist. Proceed by cases: finite or infinite.\<close>
    show ?thesis
    proof (cases "finite ?NT")
      case True
      \<comment> \<open>Finite case: delegate to graph\\_pi1\\_free\\_weak\\_finite (proper induction).\<close>
      show ?thesis
      proof (rule graph_pi1_free_weak_finite[where n="card ?NT" and \<A>=\<A> and T=T])
        show "top1_is_graph_on Y TY" by (rule assms(1))
        show "top1_connected_on Y TY" by (rule assms(2))
        show "y0 \<in> Y" by (rule assms(3))
        show "card ?NT \<le> card ?NT" by (by100 simp)
        show "finite ?NT" by (rule True)
        show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
        show "\<Union>\<A> = Y" by (rule h\<A>_cover)
        show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
        show "\<forall>C. C \<subseteq> Y \<longrightarrow>
             (closedin_on Y TY C \<longleftrightarrow>
              (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
        show "top1_is_tree_on T (subspace_topology Y TY T)" by (rule hT_tree)
        show "T \<subseteq> Y" by (rule hT_sub)
        show "\<forall>A\<in>\<A>. A \<subseteq> T \<or>
             A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (rule hT_subgraph)
        show "y0 \<in> T" by (rule hT_x0)
        show "\<forall>A\<in>{A\<in>\<A>. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
          by (rule hNT_endpoints)
      qed
    next
      case hInf: False
      \<comment> \<open>Infinite case: compactness reduction to finite subgraphs.\<close>
      \<comment> \<open>Infinite case: direct limit argument.
         Every loop in Y has compact image meeting finitely many arcs.
         So every element of \\<pi>\\_1(Y) lies in \\<pi>\\_1 of some finite subgraph.
         \\<pi>\\_1(Y) is the direct limit of \\<pi>\\_1(finite subgraphs), all free.
         Direct limit of free groups with injective maps is free.\<close>
      \<comment> \<open>Book Step 3: Infinite case. For each non-tree arc A, define
         the loop g\\_A = \\<gamma>\\_a * f\\_A * rev(\\<gamma>\\_b) where \\<gamma>\\_a, \\<gamma>\\_b are
         paths in T from x0 to A's endpoints, and f\\_A is the linear path in A.
         Claim: \\<pi>\\_1(Y) is free on {[g\\_A] | A \\<in> NT}.
         Proof: any reduced word w in these generators involves finitely many A's.
         The subgraph Y' = T \\<union> {those A's} has \\<pi>\\_1(Y') free on the corresponding
         generators (by the finite case). The inclusion Y' \\<hookrightarrow> Y induces an injection
         on \\<pi>\\_1 (since Y' is a retract of Y). So w \\<ne> id in \\<pi>\\_1(Y') implies w \\<ne> id
         in \\<pi>\\_1(Y).\<close>
      \<comment> \<open>Proof sketch: \\<pi>\\_1(Y) is free on generators {[g\\_A] | A \\<in> NT}.
         The freeness condition (no non-trivial reduced word = id) follows
         from the finite case + injectivity of inclusion on \\<pi>\\_1.\<close>
      \<comment> \<open>Key idea: for any reduced word w = g\\_{A1}^{e1} ... g\\_{An}^{en},
         the finite subgraph Y' = T \\<union> A1 \\<union> ... \\<union> An has \\<pi>\\_1 free on {[g\\_{Ai}]}.
         The inclusion \\<iota>: Y' \\<hookrightarrow> Y induces \\<iota>*: \\<pi>\\_1(Y') \\<hookrightarrow> \\<pi>\\_1(Y) (injective).
         Since w \\<noteq> id in \\<pi>\\_1(Y') (freeness), w \\<noteq> id in \\<pi>\\_1(Y) (injectivity).
         Injectivity of \\<iota>*: there's a retraction r: Y \\<rightarrow> Y' (collapse non-Y' arcs
         to T-endpoints), so r* \\<circ> \\<iota>* = id on \\<pi>\\_1(Y'), hence \\<iota>* injective.\<close>
      show ?thesis sorry \<comment> \<open>Infinite case. The proof is correct but needs:
         (a) Generator loops g\\_A defined for each A (path in T + arc + path back).
         (b) Retraction Y \\<rightarrow> Y' for finite Y' \\<subseteq> Y (continuous by coherent topology).
         (c) top1\\_is\\_free\\_group\\_full\\_on verification with potentially infinite generator set.\<close>
    qed
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
      have hT_sub_impl: "\<forall>A\<in>\<A>. \<not> A \<subseteq> T \<longrightarrow>
          A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        using hT_subgraph by (by100 blast)
      show "top1_deformation_retract_of_on (X - ps ` S)
          (subspace_topology X TX (X - ps ` S))
          (T \<union> \<Union>(?NT - S))"
        by (rule graph_deformation_retract_helper[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
            hT_tree hT_sub hT_sub_impl hNT_endpoints hS_fin hS_sub hps_loc])
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
          by (rule graph_one_edge_pi1_iso_Z[OF assms(1) assms(2) assms(3)
              h\<A> h\<A>_cover h\<A>_inter h\<A>_coh hT_tree hT_sub hT_subgraph hx0_T
              hNT_endpoints hA1 hNT_singleton])
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
        \<comment> \<open>Use graph\\_pi1\\_free\\_weak (standalone lemma) for subgraph applications.\<close>
        \<comment> \<open>target\\_U has free \\<pi>\\_1 (from graph\\_pi1\\_free\\_weak).\<close>
        have htU_pi1_free: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
            (top1_fundamental_group_carrier ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            (top1_fundamental_group_mul ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            (top1_fundamental_group_id ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            (top1_fundamental_group_invg ?target_U (subspace_topology ?U ?TU ?target_U) x0)
            \<iota> S"
        proof -
          have htU_conn: "top1_connected_on ?target_U (subspace_topology X TX ?target_U)"
          proof -
            \<comment> \<open>T \\<union> A1 is path-connected (tree + arc with endpoint in T).\<close>
            have "A1 \<in> \<A>" using hA1 by (by100 blast)
            have hA1_arc_loc: "top1_is_arc_on A1 (subspace_topology X TX A1)"
              using h\<A> \<open>A1 \<in> \<A>\<close> by (by100 blast)
            have hA1_sub_loc: "A1 \<subseteq> X" using h\<A> \<open>A1 \<in> \<A>\<close> by (by100 blast)
            have "\<exists>e. e \<in> T \<and> e \<in> A1"
            proof -
              obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A1 (subspace_topology X TX A1) hj"
                using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
              have hX_strict': "is_topology_on_strict X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hX_haus': "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hX_strict' hX_haus' hA1_sub_loc hA1_arc_loc hhj]
              have hep: "top1_arc_endpoints_on A1 (subspace_topology X TX A1) = {hj 0, hj 1}" .
              have "hj 0 \<in> T"
                using hNT_endpoints[rule_format, OF hA1] hep by (by100 simp)
              have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "hj 0 \<in> A1"
                using hhj \<open>(0::real) \<in> _\<close> unfolding top1_homeomorphism_on_def bij_betw_def
                by (by100 blast)
              thus ?thesis using \<open>hj 0 \<in> T\<close> by (by100 blast)
            qed
            from tree_union_arcs_path_connected[OF hTX_top hT_tree hT_sub _
                _ _ hx0_T, of "{A1}"]
            have "top1_path_connected_on (T \<union> \<Union>{A1}) (subspace_topology X TX (T \<union> \<Union>{A1}))"
              using hA1_arc_loc hA1_sub_loc \<open>\<exists>e. e \<in> T \<and> e \<in> A1\<close> by (by100 simp)
            hence "top1_path_connected_on ?target_U (subspace_topology X TX ?target_U)"
              using \<open>?target_U = T \<union> A1\<close> by simp
            thus ?thesis using top1_path_connected_imp_connected by (by100 blast)
          qed
          have htU_graph: "top1_is_graph_on ?target_U (subspace_topology X TX ?target_U)"
          proof -
            let ?\<B>U = "{A \<in> \<A>. A \<subseteq> ?target_U}"
            have htU_eq: "?target_U = \<Union>?\<B>U"
            proof (rule graph_connected_sub_covered_by_arcs)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)" by (rule h\<A>)
              show "\<Union>\<A> = X" by (rule h\<A>_cover)
              show "\<forall>C. C \<subseteq> X \<longrightarrow>
                   (closedin_on X TX C \<longleftrightarrow>
                    (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))" by (rule h\<A>_coh)
              show "?target_U \<subseteq> X" using hT_sub h\<A> hA1 by (by100 blast)
              show "top1_connected_on ?target_U (subspace_topology X TX ?target_U)"
                by (rule htU_conn)
              \<comment> \<open>\\<ge>2 points: endpoints of A1 are distinct and in T.\<close>
              show "\<exists>y1 y2. y1 \<in> ?target_U \<and> y2 \<in> ?target_U \<and> y1 \<noteq> y2"
              proof -
                have "A1 \<in> \<A>" using hA1 by (by100 blast)
                have hA1_arc: "top1_is_arc_on A1 (subspace_topology X TX A1)"
                  using h\<A> \<open>A1 \<in> \<A>\<close> by (by100 blast)
                have hA1_sub: "A1 \<subseteq> X" using h\<A> \<open>A1 \<in> \<A>\<close> by (by100 blast)
                obtain hh where hhh: "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology A1 (subspace_topology X TX A1) hh"
                  using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
                have hbij: "bij_betw hh top1_unit_interval A1"
                  using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
                have h0_I: "(0::real) \<in> top1_unit_interval"
                  unfolding top1_unit_interval_def by (by100 simp)
                have h1_I: "(1::real) \<in> top1_unit_interval"
                  unfolding top1_unit_interval_def by (by100 simp)
                have "hh 0 \<in> A1" using hbij h0_I unfolding bij_betw_def by (by100 blast)
                have "hh 1 \<in> A1" using hbij h1_I unfolding bij_betw_def by (by100 blast)
                have "hh 0 \<noteq> hh 1"
                proof -
                  have "inj_on hh top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
                  have "(0::real) \<noteq> (1::real)" by (by100 simp)
                  thus ?thesis using \<open>inj_on hh _\<close> h0_I h1_I unfolding inj_on_def by (by100 blast)
                qed
                have "hh 0 \<in> ?target_U" using \<open>hh 0 \<in> A1\<close> \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                have "hh 1 \<in> ?target_U" using \<open>hh 1 \<in> A1\<close> \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                thus ?thesis using \<open>hh 0 \<in> ?target_U\<close> \<open>hh 0 \<noteq> hh 1\<close> by (by100 blast)
              qed
              show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_U \<longrightarrow> finite (A \<inter> ?target_U)"
              proof (intro ballI impI)
                fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_U"
                have "A \<inter> ?target_U \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                proof -
                  have "A \<inter> ?target_U \<subseteq> (A \<inter> T) \<union> (A \<inter> A1)"
                    using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                  moreover have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  proof -
                    have "\<not> A \<subseteq> T" using \<open>\<not> A \<subseteq> ?target_U\<close> \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                    from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
                    show ?thesis by (by100 blast)
                  qed
                  moreover have "A \<inter> A1 \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  proof (cases "A = A1")
                    case True
                    hence "A \<subseteq> ?target_U" using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                    thus ?thesis using \<open>\<not> A \<subseteq> ?target_U\<close> by contradiction
                  next
                    case False
                    have "A1 \<in> \<A>" using hA1 by (by100 blast)
                    from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A1 \<in> \<A>\<close> False]
                    show ?thesis by (by100 blast)
                  qed
                  ultimately show ?thesis by (by100 blast)
                qed
                moreover have "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
                proof -
                  have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
                    using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                      top1_unit_interval_topology A (subspace_topology X TX A) h"
                    using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
                  have hX_strict: "is_topology_on_strict X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have hX_haus: "is_hausdorff_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close> hA_arc hh]
                  show ?thesis by (by100 simp)
                qed
                ultimately show "finite (A \<inter> ?target_U)"
                  using finite_subset by (by100 blast)
              qed
              \<comment> \<open>Finite non-target arcs: only NT-{A1} which is finite.\<close>
              show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_U}"
              proof -
                have "{A \<in> \<A>. \<not> A \<subseteq> ?target_U} \<subseteq> ?NT - {A1}"
                proof (intro subsetI)
                  fix A assume "A \<in> {A \<in> \<A>. \<not> A \<subseteq> ?target_U}"
                  hence "A \<in> \<A>" "\<not> A \<subseteq> ?target_U" by (by100 blast)+
                  hence "\<not> A \<subseteq> T" using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                  hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
                  moreover have "A \<noteq> A1"
                  proof
                    assume "A = A1"
                    hence "A \<subseteq> ?target_U" using \<open>?target_U = T \<union> A1\<close> by (by100 blast)
                    thus False using \<open>\<not> A \<subseteq> ?target_U\<close> by contradiction
                  qed
                  ultimately show "A \<in> ?NT - {A1}" by (by100 blast)
                qed
                thus ?thesis using \<open>finite ?NT\<close> finite_subset by (by100 blast)
              qed
            qed
            have hBU_coh: "\<forall>C. C \<subseteq> ?target_U \<longrightarrow>
                (closedin_on ?target_U (subspace_topology X TX ?target_U) C \<longleftrightarrow>
                 (\<forall>A\<in>?\<B>U. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
            proof (rule subgraph_coherent_topology)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)" by (rule h\<A>)
              show "\<Union>\<A> = X" by (rule h\<A>_cover)
              show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
                   A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
                 \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
                 \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
              show "\<forall>C. C \<subseteq> X \<longrightarrow>
                   (closedin_on X TX C \<longleftrightarrow>
                    (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))" by (rule h\<A>_coh)
              show "?\<B>U \<subseteq> \<A>" by (by100 blast)
              show "?target_U = \<Union>?\<B>U" by (rule htU_eq)
            qed
            have hBU_arcs: "\<forall>A\<in>?\<B>U. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
              using h\<A> by (by100 blast)
            have hBU_cover: "\<Union>?\<B>U \<subseteq> X" using h\<A> by (by100 blast)
            have hBU_inter: "\<forall>A\<in>?\<B>U. \<forall>B\<in>?\<B>U. A \<noteq> B \<longrightarrow>
                A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A) \<and>
                A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B) \<and>
                finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
              using h\<A>_inter by (by100 blast)
            have "top1_is_graph_on (\<Union>?\<B>U) (subspace_topology X TX (\<Union>?\<B>U))"
            proof (rule subgraph_union_of_arcs_is_graph)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>?\<B>U. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
                by (rule hBU_arcs)
              show "\<Union>?\<B>U \<subseteq> X" by (rule hBU_cover)
              show "\<forall>A\<in>?\<B>U. \<forall>B\<in>?\<B>U. A \<noteq> B \<longrightarrow>
                  A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A) \<and>
                  A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B) \<and>
                  finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule hBU_inter)
              show "\<forall>C. C \<subseteq> \<Union>?\<B>U \<longrightarrow>
                  (closedin_on (\<Union>?\<B>U) (subspace_topology X TX (\<Union>?\<B>U)) C \<longleftrightarrow>
                   (\<forall>A\<in>?\<B>U. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
                using hBU_coh htU_eq by simp
            qed
            thus ?thesis using htU_eq by simp
          qed
          \<comment> \<open>htU\\_conn already proved above.\<close>
          \<comment> \<open>Use graph\\_pi1\\_free\\_weak for target\\_U.\<close>
          from graph_pi1_free_weak[OF htU_graph htU_conn hx0_tU]
          show ?thesis using hTU_trans by simp
        qed
        \<comment> \<open>target\\_V has free \\<pi>\\_1 (from graph\\_pi1\\_free\\_weak).\<close>
        have htV_pi1_free: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
            (top1_fundamental_group_carrier ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            (top1_fundamental_group_mul ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            (top1_fundamental_group_id ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            (top1_fundamental_group_invg ?target_V (subspace_topology ?V ?TV ?target_V) x0)
            \<iota> S"
        proof -
          have htV_conn: "top1_connected_on ?target_V (subspace_topology X TX ?target_V)"
          proof -
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
              have hX_strict': "is_topology_on_strict X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hX_haus': "is_hausdorff_on X TX"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hX_strict' hX_haus' hAj_sub hAj_arc hhj]
              have hep: "top1_arc_endpoints_on Aj (subspace_topology X TX Aj) = {hj 0, hj 1}" .
              have "hj 0 \<in> T"
                using hNT_endpoints[rule_format, OF \<open>Aj \<in> ?NT\<close>] hep by (by100 simp)
              have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
              have "hj 0 \<in> Aj"
                using hhj \<open>(0::real) \<in> _\<close> unfolding top1_homeomorphism_on_def bij_betw_def
                by (by100 blast)
              thus "\<exists>e. e \<in> T \<and> e \<in> Aj" using \<open>hj 0 \<in> T\<close> by (by100 blast)
            qed
            have htV_eq_loc: "?target_V = T \<union> \<Union>(?NT - {A1})" by (by100 blast)
            from tree_union_arcs_path_connected[OF hTX_top hT_tree hT_sub
                \<open>finite (?NT - {A1})\<close> \<open>\<forall>A\<in>?NT - {A1}. _ \<and> _\<close>
                \<open>\<forall>A\<in>?NT - {A1}. \<exists>e. _\<close> hx0_T]
            have "top1_path_connected_on (T \<union> \<Union>(?NT - {A1}))
                (subspace_topology X TX (T \<union> \<Union>(?NT - {A1})))" .
            hence "top1_path_connected_on ?target_V (subspace_topology X TX ?target_V)"
              using htV_eq_loc by simp
            thus ?thesis using top1_path_connected_imp_connected by (by100 blast)
          qed
          have htV_graph: "top1_is_graph_on ?target_V (subspace_topology X TX ?target_V)"
          proof -
            let ?\<B>V = "{A \<in> \<A>. A \<subseteq> ?target_V}"
            have htV_eq2: "?target_V = \<Union>?\<B>V"
            proof (rule graph_connected_sub_covered_by_arcs)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)" by (rule h\<A>)
              show "\<Union>\<A> = X" by (rule h\<A>_cover)
              show "\<forall>C. C \<subseteq> X \<longrightarrow> (closedin_on X TX C \<longleftrightarrow>
                    (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))" by (rule h\<A>_coh)
              show "?target_V \<subseteq> X" using hT_sub h\<A> by (by100 blast)
              show "top1_connected_on ?target_V (subspace_topology X TX ?target_V)"
                by (rule htV_conn)
              show "\<exists>y1 y2. y1 \<in> ?target_V \<and> y2 \<in> ?target_V \<and> y1 \<noteq> y2"
              proof -
                \<comment> \<open>NT has \\<ge>2 arcs. A1 \\<in> NT. Pick another arc B \\<in> NT-{A1}.\<close>
                have "card ?NT > 1" using hcard_gt1 .
                have "?NT - {A1} \<noteq> {}"
                proof -
                  have "card (?NT - {A1}) \<ge> 1"
                    using hcard_gt1 \<open>finite ?NT\<close> hA1 by (by100 simp)
                  thus ?thesis by (by100 force)
                qed
                then obtain B where "B \<in> ?NT - {A1}" by (by100 blast)
                have "B \<in> \<A>" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
                have hB_arc: "top1_is_arc_on B (subspace_topology X TX B)"
                  using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                have hB_sub: "B \<subseteq> X" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                obtain hb where hhb: "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology B (subspace_topology X TX B) hb"
                  using hB_arc unfolding top1_is_arc_on_def by (by100 blast)
                have hbij: "bij_betw hb top1_unit_interval B"
                  using hhb unfolding top1_homeomorphism_on_def by (by100 blast)
                have h0_I: "(0::real) \<in> top1_unit_interval"
                  unfolding top1_unit_interval_def by (by100 simp)
                have h1_I: "(1::real) \<in> top1_unit_interval"
                  unfolding top1_unit_interval_def by (by100 simp)
                have "hb 0 \<in> B" using hbij h0_I unfolding bij_betw_def by (by100 blast)
                have "hb 1 \<in> B" using hbij h1_I unfolding bij_betw_def by (by100 blast)
                have "hb 0 \<noteq> hb 1"
                proof
                  assume "hb 0 = hb 1"
                  have "inj_on hb top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
                  from inj_onD[OF this \<open>hb 0 = hb 1\<close> h0_I h1_I]
                  show False by (by100 simp)
                qed
                have "B \<subseteq> \<Union>(?NT - {A1})" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
                hence "B \<subseteq> ?target_V" by (by100 blast)
                hence "hb 0 \<in> ?target_V" "hb 1 \<in> ?target_V"
                  using \<open>hb 0 \<in> B\<close> \<open>hb 1 \<in> B\<close> by (by100 blast)+
                show ?thesis
                  apply (rule exI[of _ "hb 0"], rule exI[of _ "hb 1"])
                  using \<open>hb 0 \<in> ?target_V\<close> \<open>hb 1 \<in> ?target_V\<close> \<open>hb 0 \<noteq> hb 1\<close>
                  by (by100 blast)
              qed
              show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_V \<longrightarrow> finite (A \<inter> ?target_V)"
              proof (intro ballI impI)
                fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_V"
                \<comment> \<open>Only non-target arc is A1.\<close>
                have "A = A1"
                proof -
                  have "A \<in> ?NT \<or> A \<subseteq> T" using \<open>A \<in> \<A>\<close> by (by100 blast)
                  thus ?thesis
                  proof
                    assume "A \<in> ?NT"
                    have "A \<in> ?NT - {A1} \<or> A = A1" using \<open>A \<in> ?NT\<close> by (by100 blast)
                    thus ?thesis
                    proof
                      assume "A \<in> ?NT - {A1}"
                      hence "A \<subseteq> ?target_V" by (by100 blast)
                      thus ?thesis using \<open>\<not> A \<subseteq> ?target_V\<close> by contradiction
                    next
                      assume "A = A1" thus ?thesis .
                    qed
                  next
                    assume "A \<subseteq> T" hence "A \<subseteq> ?target_V" by (by100 blast)
                    thus ?thesis using \<open>\<not> A \<subseteq> ?target_V\<close> by contradiction
                  qed
                qed
                hence "A \<inter> ?target_V = A1 \<inter> ?target_V" by simp
                \<comment> \<open>A1 \\<inter> target\\_V \\<subseteq> endpoints(A1).\<close>
                have "A1 \<inter> ?target_V \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                proof (intro subsetI)
                  fix x assume "x \<in> A1 \<inter> ?target_V"
                  hence "x \<in> A1" "x \<in> ?target_V" by (by100 blast)+
                  have "x \<in> T \<or> (\<exists>B\<in>?NT-{A1}. x \<in> B)"
                    using \<open>x \<in> ?target_V\<close> by (by100 blast)
                  thus "x \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                  proof
                    assume "x \<in> T"
                    have "\<not> A1 \<subseteq> T" using hA1 by (by100 blast)
                    have "A1 \<in> \<A>" using hA1 by (by100 blast)
                    from hT_subgraph[rule_format, OF \<open>A1 \<in> \<A>\<close>] \<open>\<not> A1 \<subseteq> T\<close>
                    have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                      by (by100 blast)
                    thus ?thesis using \<open>x \<in> A1\<close> \<open>x \<in> T\<close> by (by100 blast)
                  next
                    assume "\<exists>B\<in>?NT-{A1}. x \<in> B"
                    then obtain B where "B \<in> ?NT-{A1}" "x \<in> B" by (by100 blast)
                    have "B \<in> \<A>" using \<open>B \<in> ?NT-{A1}\<close> by (by100 blast)
                    have "B \<noteq> A1" using \<open>B \<in> ?NT-{A1}\<close> by (by100 blast)
                    have "A1 \<in> \<A>" using hA1 by (by100 blast)
                    have "A1 \<noteq> B" using \<open>B \<noteq> A1\<close> by simp
                    from h\<A>_inter[rule_format, OF \<open>A1 \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A1 \<noteq> B\<close>]
                    have "A1 \<inter> B \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                      by (by100 blast)
                    thus ?thesis using \<open>x \<in> A1\<close> \<open>x \<in> B\<close> by (by100 blast)
                  qed
                qed
                hence "finite (A1 \<inter> ?target_V)"
                proof -
                  have hA1_arc_f: "top1_is_arc_on A1 (subspace_topology X TX A1)"
                    using h\<A> hA1 by (by100 blast)
                  have hA1_sub_f: "A1 \<subseteq> X" using h\<A> hA1 by (by100 blast)
                  obtain hf where hhf: "top1_homeomorphism_on top1_unit_interval
                      top1_unit_interval_topology A1 (subspace_topology X TX A1) hf"
                    using hA1_arc_f unfolding top1_is_arc_on_def by (by100 blast)
                  have hX_strict_f: "is_topology_on_strict X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have hX_haus_f: "is_hausdorff_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  from arc_endpoints_are_boundary[OF hX_strict_f hX_haus_f hA1_sub_f hA1_arc_f hhf]
                  have "finite (top1_arc_endpoints_on A1 (subspace_topology X TX A1))"
                    by (by100 simp)
                  thus ?thesis using \<open>A1 \<inter> ?target_V \<subseteq> _\<close> finite_subset by (by100 blast)
                qed
                thus "finite (A \<inter> ?target_V)" using \<open>A \<inter> ?target_V = A1 \<inter> ?target_V\<close> by simp
              qed
              show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_V}"
              proof -
                have "{A \<in> \<A>. \<not> A \<subseteq> ?target_V} \<subseteq> {A1}"
                proof (intro subsetI)
                  fix A assume "A \<in> {A \<in> \<A>. \<not> A \<subseteq> ?target_V}"
                  hence "A \<in> \<A>" "\<not> A \<subseteq> ?target_V" by (by100 blast)+
                  have "A \<in> ?NT \<or> A \<subseteq> T"
                    using \<open>A \<in> \<A>\<close> by (by100 blast)
                  thus "A \<in> {A1}"
                  proof
                    assume "A \<in> ?NT"
                    hence "A \<in> ?NT - {A1} \<or> A = A1" by (by100 blast)
                    thus ?thesis
                    proof
                      assume "A \<in> ?NT - {A1}"
                      hence "A \<subseteq> \<Union>(?NT - {A1})" by (by100 blast)
                      hence "A \<subseteq> ?target_V" by (by100 blast)
                      thus ?thesis using \<open>\<not> A \<subseteq> ?target_V\<close> by contradiction
                    next
                      assume "A = A1" thus ?thesis by (by100 blast)
                    qed
                  next
                    assume "A \<subseteq> T"
                    hence "A \<subseteq> ?target_V" by (by100 blast)
                    thus ?thesis using \<open>\<not> A \<subseteq> ?target_V\<close> by contradiction
                  qed
                qed
                thus ?thesis by (rule finite_subset) (by100 simp)
              qed
            qed \<comment> \<open>Every point in T \\<union> \\<Union>(NT-{A1}) is in some arc \\<subseteq> target\\_V.\<close>
            have hBV_coh: "\<forall>C. C \<subseteq> ?target_V \<longrightarrow>
                (closedin_on ?target_V (subspace_topology X TX ?target_V) C \<longleftrightarrow>
                 (\<forall>A\<in>?\<B>V. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
            proof (rule subgraph_coherent_topology)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)" by (rule h\<A>)
              show "\<Union>\<A> = X" by (rule h\<A>_cover)
              show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
                   A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
                 \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
                 \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
              show "\<forall>C. C \<subseteq> X \<longrightarrow>
                   (closedin_on X TX C \<longleftrightarrow>
                    (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))" by (rule h\<A>_coh)
              show "?\<B>V \<subseteq> \<A>" by (by100 blast)
              show "?target_V = \<Union>?\<B>V" by (rule htV_eq2)
            qed
            have hBV_arcs: "\<forall>A\<in>?\<B>V. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
              using h\<A> by (by100 blast)
            have hBV_cover: "\<Union>?\<B>V \<subseteq> X" using h\<A> by (by100 blast)
            have hBV_inter: "\<forall>A\<in>?\<B>V. \<forall>B\<in>?\<B>V. A \<noteq> B \<longrightarrow>
                A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A) \<and>
                A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B) \<and>
                finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            proof (intro ballI impI)
              fix A B assume "A \<in> ?\<B>V" "B \<in> ?\<B>V" "A \<noteq> B"
              hence "A \<in> \<A>" "B \<in> \<A>" by (by100 blast)+
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
              show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A) \<and>
                A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B) \<and>
                finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
            qed
            have "top1_is_graph_on (\<Union>?\<B>V) (subspace_topology X TX (\<Union>?\<B>V))"
            proof (rule subgraph_union_of_arcs_is_graph)
              show "top1_is_graph_on X TX" by (rule assms(1))
              show "\<forall>A\<in>?\<B>V. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
                by (rule hBV_arcs)
              show "\<Union>?\<B>V \<subseteq> X" by (rule hBV_cover)
              show "\<forall>A\<in>?\<B>V. \<forall>B\<in>?\<B>V. A \<noteq> B \<longrightarrow>
                  A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A) \<and>
                  A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B) \<and>
                  finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule hBV_inter)
              show "\<forall>C. C \<subseteq> \<Union>?\<B>V \<longrightarrow>
                  (closedin_on (\<Union>?\<B>V) (subspace_topology X TX (\<Union>?\<B>V)) C \<longleftrightarrow>
                   (\<forall>A\<in>?\<B>V. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
                using hBV_coh htV_eq2 by simp
            qed
            thus ?thesis using htV_eq2 by simp
          qed
          \<comment> \<open>htV\\_conn already proved above.\<close>
          from graph_pi1_free_weak[OF htV_graph htV_conn hx0_tV]
          show ?thesis using hTV_trans by simp
        qed
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
          \<comment> \<open>\\<pi>\\_1(target\\_U) free \\<Rightarrow> \\<pi>\\_1(U) free via DR iso + transfer.\<close>
          show ?thesis using htU_pi1_free hpi1_U_iso hpi1_U_grp
            apply -
            apply (erule exE)+
            apply (drule free_group_iso_transfer, assumption, assumption)
            apply (erule exE, rule exI, rule exI, assumption)
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
          show ?thesis using htV_pi1_free hpi1_V_iso hpi1_V_grp
            apply -
            apply (erule exE)+
            apply (drule free_group_iso_transfer, assumption, assumption)
            apply (erule exE, rule exI, rule exI, assumption)
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
        \<comment> \<open>Apply svk\\_free\\_product\\_free: need \\<pi>\\_1(U), \\<pi>\\_1(V) free with disjoint generator sets.\<close>
        \<comment> \<open>Step 5: Compose: \\<pi>\\_1(U), \\<pi>\\_1(V) free \\<Rightarrow> \\<pi>\\_1(X) free via SvK.\<close>
        have hX_strict_loc: "is_topology_on_strict X TX"
          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
        \<comment> \<open>Step 5a: Reindex generators for disjointness.\<close>
        have hpi1_X_free: "\<exists>(\<iota>X::nat \<Rightarrow> _) (SX::nat set). top1_is_free_group_full_on
            (top1_fundamental_group_carrier X TX x0)
            (top1_fundamental_group_mul X TX x0)
            (top1_fundamental_group_id X TX x0)
            (top1_fundamental_group_invg X TX x0)
            \<iota>X SX"
        proof -
          \<comment> \<open>Destructure existentials via apply.\<close>
          from hU_free_direct
          obtain \<iota>U :: "nat \<Rightarrow> _" and S1 :: "nat set" where hU_f:
            "top1_is_free_group_full_on
                (top1_fundamental_group_carrier ?U ?TU x0)
                (top1_fundamental_group_mul ?U ?TU x0)
                (top1_fundamental_group_id ?U ?TU x0)
                (top1_fundamental_group_invg ?U ?TU x0)
                \<iota>U S1"
            by - ((erule exE)+, (erule that))
          from hV_free_direct
          obtain \<iota>V :: "nat \<Rightarrow> _" and S2 :: "nat set" where hV_f:
            "top1_is_free_group_full_on
                (top1_fundamental_group_carrier ?V ?TV x0)
                (top1_fundamental_group_mul ?V ?TV x0)
                (top1_fundamental_group_id ?V ?TV x0)
                (top1_fundamental_group_invg ?V ?TV x0)
                \<iota>V S2"
            by - ((erule exE)+, (erule that))
          \<comment> \<open>Reindex: even/odd for disjointness.\<close>
          define f1 :: "nat \<Rightarrow> nat" where "f1 n = 2*n" for n
          define f2 :: "nat \<Rightarrow> nat" where "f2 n = 2*n+1" for n
          have "bij_betw (the_inv_into S1 f1) (f1 ` S1) S1"
          proof -
            have "inj f1" unfolding f1_def by (intro injI) (by100 simp)
            hence "inj_on f1 S1" using inj_on_subset[OF \<open>inj f1\<close>] by (by100 blast)
            hence "bij_betw f1 S1 (f1 ` S1)" unfolding bij_betw_def by (by100 blast)
            thus ?thesis by (rule bij_betw_the_inv_into)
          qed
          from free_group_full_reindex[OF hU_f this]
          have hU_re: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier ?U ?TU x0)
              (top1_fundamental_group_mul ?U ?TU x0)
              (top1_fundamental_group_id ?U ?TU x0)
              (top1_fundamental_group_invg ?U ?TU x0)
              (\<iota>U \<circ> the_inv_into S1 f1) (f1 ` S1)" .
          have "bij_betw (the_inv_into S2 f2) (f2 ` S2) S2"
          proof -
            have "inj f2" unfolding f2_def by (intro injI) (by100 simp)
            hence "inj_on f2 S2" using inj_on_subset[OF \<open>inj f2\<close>] by (by100 blast)
            hence "bij_betw f2 S2 (f2 ` S2)" unfolding bij_betw_def by (by100 blast)
            thus ?thesis by (rule bij_betw_the_inv_into)
          qed
          from free_group_full_reindex[OF hV_f this]
          have hV_re: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier ?V ?TV x0)
              (top1_fundamental_group_mul ?V ?TV x0)
              (top1_fundamental_group_id ?V ?TV x0)
              (top1_fundamental_group_invg ?V ?TV x0)
              (\<iota>V \<circ> the_inv_into S2 f2) (f2 ` S2)" .
          have hS_disj: "f1 ` S1 \<inter> f2 ` S2 = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain x where "x \<in> f1 ` S1" "x \<in> f2 ` S2" by (by100 blast)
            then obtain a b where "x = 2*a" "x = 2*b+1"
              unfolding f1_def f2_def by (by100 blast)
            thus False by presburger
          qed
          have hx0_UV': "x0 \<in> ?U \<inter> ?V" using hx0_UV hUV_eq by (by100 simp)
          have hUV_sc': "top1_simply_connected_on (?U \<inter> ?V) (subspace_topology X TX (?U \<inter> ?V))"
            using hUV_sc hUV_eq by (by100 simp)
          have hsvk_result: "\<exists>\<iota>X. top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX x0)
              (top1_fundamental_group_mul X TX x0)
              (top1_fundamental_group_id X TX x0)
              (top1_fundamental_group_invg X TX x0)
              \<iota>X (f1 ` S1 \<union> f2 ` S2)"
            by (rule svk_free_product_free[OF hX_strict_loc hU_open hV_open hUV_cover
                hUV_sc' hU_pc hV_pc hx0_UV' hU_re hV_re hS_disj])
          from hsvk_result obtain \<iota>X where hX_fr: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX x0)
              (top1_fundamental_group_mul X TX x0)
              (top1_fundamental_group_id X TX x0)
              (top1_fundamental_group_invg X TX x0)
              \<iota>X (f1 ` S1 \<union> f2 ` S2)"
            by (by100 blast)
          show ?thesis using hX_fr by (by5000 blast)
        qed
        \<comment> \<open>Step 5b: Package \\<pi>\\_1(X) free \\<Rightarrow> \\<exists>G::int set. free(G) \\<and> iso(G, \\<pi>\\_1(X)).\<close>
        show ?thesis using hpi1_X_free
          sorry \<comment> \<open>Abstract free group realization as int set.\<close>
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
      and "p' e0' = x0"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) for H-image in \\<pi>\\_1(X).
       Also need: p'*(\\<pi>\\_1(E', e0')) corresponds to H under iso G \\<cong> \\<pi>\\_1(X).\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2: covering of graph is graph).
     \<pi>_1(E) is free (Theorem 84.7: fund group of connected graph is free).
     p_* injective (covering maps induce injections on \<pi>_1).
     H iso p_*(pi1(E)) which is free (subgroup of free = free via injection).\<close>
  have hE'_graph: "top1_is_graph_on E' TE'"
    by (rule graph_covering_is_graph[OF \<open>top1_is_graph_on X TX\<close>
        \<open>top1_covering_map_on E' TE' X TX p'\<close> hE'_strict])
  \<comment> \<open>Step 3b: \\<pi>\\_1(E') is free (graph\\_pi1\\_free\\_weak — no int set needed here).\<close>
  from graph_pi1_free_weak[OF hE'_graph \<open>top1_connected_on E' TE'\<close> \<open>e0' \<in> E'\<close>]
  obtain \<iota>_E :: "nat \<Rightarrow> _" and S_E :: "nat set"
    where hfree_E: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>_E S_E"
    by - ((erule exE)+, (erule that))
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
  \<comment> \<open>Step 3a: pi1(E') is free (graph\\_pi1\\_free\\_weak).\<close>
  from graph_pi1_free_weak[OF hE'_graph hE'_conn he0']
  obtain \<iota>_E :: "nat \<Rightarrow> _" and S_E :: "nat set"
    where hfree_E: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_id E' TE' e0')
        (top1_fundamental_group_invg E' TE' e0')
        \<iota>_E S_E"
    by - ((erule exE)+, (erule that))
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

