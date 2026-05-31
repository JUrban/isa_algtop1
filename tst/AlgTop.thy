theory AlgTop
  imports "AlgTopCached9.AlgTopCached9"
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




\<comment> \<open>free\_group\_hom\_subset\_injective + Theorem\_71\_3\_pi1\_free moved to AlgTopCached9.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful) is now Theorem\_71\_3 in AlgTopCached9.
   It states: \\<pi>\\_1(X, p) is free on J (the actual book statement).
   The old int-set packaging wrapper (Theorem\_71\_3\_wedge\_of\_circles\_general)
   was unused dead code and has been removed.\<close>





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
      \<comment> \<open>Book Step 3 (infinite case): same as Theorem 71.3.
         Key facts: (1) any loop lies in T \\<union> {finitely many arcs} (compactness),
         (2) any homotopy also lies in such a space,
         (3) finite subgraph has free \\<pi>\\_1 (finite case),
         (4) inclusion is injective on \\<pi>\\_1 (retraction: collapse non-Y' arcs).
         By (1)-(4), \\<pi>\\_1(Y) is free.\<close>
      \<comment> \<open>The finite subgraph T \\<union> F (for finite F \\<subseteq> ?NT) has free \\<pi>\\_1
         by graph\\_pi1\\_free\\_weak\\_finite. The inclusion T \\<union> F \\<hookrightarrow> Y is injective
         on \\<pi>\\_1 by free\\_group\\_hom\\_subset\\_injective (same as Theorem 71.3).
         Note: the retraction approach does NOT work here because arcs with
         two distinct endpoints in T cannot be collapsed continuously without
         identifying endpoints. The algebraic approach (free group embedding)
         is correct.\<close>
      \<comment> \<open>Step 1: Inclusion \\<pi>\\_1(T \\<union> F) \\<hookrightarrow> \\<pi>\\_1(Y) is injective.
         Uses free\\_group\\_hom\\_subset\\_injective from AlgTopCached9.\<close>
      have hincl_inj: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?NT \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
          inj_on (top1_fundamental_group_induced_on (T \<union> \<Union>F)
              (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x))
            (top1_fundamental_group_carrier (T \<union> \<Union>F)
              (subspace_topology Y TY (T \<union> \<Union>F)) y0)"
        sorry \<comment> \<open>Same proof as hincl\\_inj in Theorem 71.3:
           free\\_group\\_hom\\_subset\\_injective + finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb.
           The subgraph T \\<union> F has free \\<pi>\\_1 (from hfinite\\_subgraph\\_free).
           The inclusion maps generators of \\<pi>\\_1(T \\<union> F) to generators of \\<pi>\\_1(Y).
           By free group embedding: inclusion is injective.\<close>
      \<comment> \<open>Helper: any compact K \\<subseteq> Y meets finitely many non-tree arc interiors,
         hence K \\<subseteq> T \\<union> \\<Union>F for some finite F \\<subseteq> ?NT.\<close>
      have hcompact_in_finite: "\<And>K. K \<subseteq> Y \<Longrightarrow>
          top1_compact_on K (subspace_topology Y TY K) \<Longrightarrow>
          \<exists>F. finite F \<and> F \<subseteq> ?NT \<and> K \<subseteq> T \<union> \<Union>F"
      proof -
        fix K assume hK_sub: "K \<subseteq> Y" and hK_compact: "top1_compact_on K (subspace_topology Y TY K)"
        let ?FK = "{A \<in> ?NT. K \<inter> (A - top1_arc_endpoints_on A (subspace_topology Y TY A)) \<noteq> {}}"
        \<comment> \<open>Selection set argument (same as hloop\\_in\\_finite).\<close>
        have "\<forall>A\<in>?FK. \<exists>x. x \<in> K \<and> x \<in> A \<and>
            x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          by (by100 blast)
        define sel where "sel A = (SOME x. x \<in> K \<and> x \<in> A \<and>
            x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A))" for A
        have hsel: "\<forall>A\<in>?FK. sel A \<in> K \<and> sel A \<in> A \<and>
            sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
        proof (intro ballI conjI)
          fix A assume "A \<in> ?FK"
          hence "\<exists>x. x \<in> K \<and> x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            by (by100 blast)
          from someI_ex[OF this] show "sel A \<in> K" unfolding sel_def by (by100 blast)
          from someI_ex[OF \<open>\<exists>x. _\<close>] show "sel A \<in> A" unfolding sel_def by (by100 blast)
          from someI_ex[OF \<open>\<exists>x. _\<close>] show "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            unfolding sel_def by (by100 blast)
        qed
        let ?BK = "sel ` ?FK"
        have hBK_sub: "?BK \<subseteq> Y" using hsel hK_sub by (by100 blast)
        have hBK_in_K: "?BK \<subseteq> K" using hsel by (by100 blast)
        \<comment> \<open>\\<le>1 point per arc.\<close>
        have hBK_one: "\<forall>C\<in>\<A>. finite (C \<inter> ?BK) \<and> card (C \<inter> ?BK) \<le> 1"
        proof (intro ballI conjI)
          fix C assume "C \<in> \<A>"
          have "C \<inter> ?BK \<subseteq> (if C \<in> ?FK then {sel C} else {})"
          proof
            fix x assume "x \<in> C \<inter> ?BK"
            then obtain A where "A \<in> ?FK" "x = sel A" "x \<in> C" by (by100 blast)
            show "x \<in> (if C \<in> ?FK then {sel C} else {})"
            proof (cases "A = C")
              case True thus ?thesis using \<open>x = sel A\<close> \<open>A \<in> ?FK\<close> by (by100 simp)
            next
              case False
              have "A \<in> \<A>" using \<open>A \<in> ?FK\<close> by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>C \<in> \<A>\<close> False]
              have "A \<inter> C \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
              have "sel A \<in> A" using hsel \<open>A \<in> ?FK\<close> by (by100 blast)
              have "sel A \<in> C" using \<open>x \<in> C\<close> \<open>x = sel A\<close> by (by100 simp)
              hence "sel A \<in> A \<inter> C" using \<open>sel A \<in> A\<close> by (by100 blast)
              hence "sel A \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using \<open>A \<inter> C \<subseteq> _\<close> by (by100 blast)
              have "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using hsel \<open>A \<in> ?FK\<close> by (by100 blast)
              thus ?thesis using \<open>sel A \<in> top1_arc_endpoints_on A _\<close> by contradiction
            qed
          qed
          have hC_sub: "\<exists>S. C \<inter> ?BK \<subseteq> S \<and> finite S \<and> card S \<le> 1"
          proof (cases "C \<in> ?FK")
            case True
            hence "(if C \<in> ?FK then {sel C} else {}) = {sel C}" by (by100 simp)
            hence "C \<inter> ?BK \<subseteq> {sel C}"
              using \<open>C \<inter> ?BK \<subseteq> _\<close> by (by100 simp)
            moreover have "finite {sel C}" by (by100 simp)
            moreover have "card {sel C} \<le> 1" by (by100 simp)
            ultimately show ?thesis by (by100 blast)
          next
            case False
            hence "(if C \<in> ?FK then {sel C} else {}) = {}" by (by100 simp)
            hence "C \<inter> ?BK \<subseteq> {}"
              using \<open>C \<inter> ?BK \<subseteq> _\<close> by (by100 simp)
            moreover have "finite {}" by (by100 simp)
            moreover have "card {} \<le> (1::nat)" by (by100 simp)
            ultimately show ?thesis by (by100 blast)
          qed
          then obtain S where hS: "C \<inter> ?BK \<subseteq> S" "finite S" "card S \<le> 1"
            by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
          show "finite (C \<inter> ?BK)" using finite_subset[OF hS(1) hS(2)] .
          show "card (C \<inter> ?BK) \<le> 1" using card_mono[OF hS(2) hS(1)] hS(3) by (by100 simp)
        qed
        have hBK_one': "\<forall>A\<in>\<A>. finite (?BK \<inter> A) \<and> card (?BK \<inter> A) \<le> 1"
        proof (intro ballI conjI)
          fix A assume "A \<in> \<A>"
          from hBK_one[rule_format, OF this]
          have "finite (A \<inter> ?BK)" "card (A \<inter> ?BK) \<le> 1" by (by100 blast)+
          have "A \<inter> ?BK = ?BK \<inter> A" by (by100 blast)
          show "finite (?BK \<inter> A)" using \<open>finite (A \<inter> ?BK)\<close> \<open>A \<inter> ?BK = ?BK \<inter> A\<close> by (by100 simp)
          show "card (?BK \<inter> A) \<le> 1" using \<open>card (A \<inter> ?BK) \<le> 1\<close> \<open>A \<inter> ?BK = ?BK \<inter> A\<close> by (by100 simp)
        qed
        \<comment> \<open>Closed discrete.\<close>
        have hBK_cd: "\<forall>S. S \<subseteq> ?BK \<longrightarrow> closedin_on Y TY S"
          by (rule graph_selection_set_discrete[OF assms(1) hBK_sub h\<A> h\<A>_cover h\<A>_coh hBK_one'])
        \<comment> \<open>Compact + closed discrete = finite.\<close>
        have hTY_top: "is_topology_on Y TY"
          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        have "closedin_on Y TY ?BK" using hBK_cd by (by100 blast)
        have hBK_closed_K: "closedin_on K (subspace_topology Y TY K) ?BK"
        proof -
          from Theorem_17_2[OF hTY_top hK_sub, THEN iffD2]
          show ?thesis using \<open>closedin_on Y TY ?BK\<close> hBK_in_K by (by100 blast)
        qed
        have hBK_compact: "top1_compact_on ?BK (subspace_topology Y TY ?BK)"
        proof -
          from Theorem_26_2[OF hK_compact hBK_closed_K]
          have "top1_compact_on ?BK (subspace_topology K (subspace_topology Y TY K) ?BK)" .
          moreover have "subspace_topology K (subspace_topology Y TY K) ?BK =
              subspace_topology Y TY ?BK"
            by (rule subspace_topology_trans) (use hBK_in_K in blast)
          ultimately show ?thesis by (by5000 metis)
        qed
        have hBK_singletons_open: "\<forall>x\<in>?BK. {x} \<in> subspace_topology Y TY ?BK"
        proof (intro ballI)
          fix x assume "x \<in> ?BK"
          have "?BK - {x} \<subseteq> ?BK" by (by100 blast)
          hence "closedin_on Y TY (?BK - {x})" using hBK_cd by (by100 blast)
          hence "closedin_on ?BK (subspace_topology Y TY ?BK) (?BK - {x})"
            using Theorem_17_2[OF hTY_top, of ?BK] hBK_sub by (by100 blast)
          hence "?BK - (?BK - {x}) \<in> subspace_topology Y TY ?BK"
            unfolding closedin_on_def by (by100 blast)
          moreover have "?BK - (?BK - {x}) = {x}" using \<open>x \<in> ?BK\<close> by (by100 blast)
          ultimately show "{x} \<in> subspace_topology Y TY ?BK" by (by100 simp)
        qed
        have "?BK \<subseteq> \<Union>((\<lambda>x. {x}) ` ?BK)" by (by100 blast)
        have "(\<lambda>x. {x}) ` ?BK \<subseteq> subspace_topology Y TY ?BK"
          using hBK_singletons_open by (by100 blast)
        from compact_finite_subcover[OF hBK_compact this \<open>?BK \<subseteq> \<Union>((\<lambda>x. {x}) ` ?BK)\<close>]
        obtain Fc where hFc: "finite Fc" "Fc \<subseteq> (\<lambda>x. {x}) ` ?BK" "?BK \<subseteq> \<Union>Fc"
          by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
        have "finite (\<Union>Fc)"
        proof (rule finite_Union[OF hFc(1)])
          fix S assume "S \<in> Fc"
          then obtain x where "S = {x}" using hFc(2) by (by100 blast)
          thus "finite S" by (by100 simp)
        qed
        have "finite ?BK" using finite_subset[OF hFc(3) \<open>finite (\<Union>Fc)\<close>] .
        have "inj_on sel ?FK"
        proof (rule inj_onI)
          fix A B assume "A \<in> ?FK" "B \<in> ?FK" "sel A = sel B"
          have hA_in: "sel A \<in> A" "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            using hsel \<open>A \<in> ?FK\<close> by (by100 blast)+
          have hB_in: "sel B \<in> B" "sel B \<notin> top1_arc_endpoints_on B (subspace_topology Y TY B)"
            using hsel \<open>B \<in> ?FK\<close> by (by100 blast)+
          show "A = B"
          proof (rule ccontr)
            assume "A \<noteq> B"
            have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> ?FK\<close> \<open>B \<in> ?FK\<close> by (by100 blast)+
            from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
            have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
            have "sel A \<in> B" using hB_in(1) \<open>sel A = sel B\<close> by (by100 simp)
            have "sel A \<in> A \<inter> B" using hA_in(1) \<open>sel A \<in> B\<close> by (by100 blast)
            hence "sel A \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using \<open>A \<inter> B \<subseteq> _\<close> by (by100 blast)
            thus False using hA_in(2) by contradiction
          qed
        qed
        from finite_imageD[OF \<open>finite ?BK\<close> this]
        have "finite ?FK" .
        \<comment> \<open>K \\<subseteq> T \\<union> \\<Union>?FK.\<close>
        have "K \<subseteq> T \<union> \<Union>?FK"
        proof
          fix x assume "x \<in> K"
          hence "x \<in> Y" using hK_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          show "x \<in> T \<union> \<Union>?FK"
          proof (cases "A \<subseteq> T")
            case True thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
          next
            case False
            hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
            show ?thesis
            proof (cases "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)")
              case True
              hence "x \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              case xFalse: False
              hence "x \<in> A - top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using \<open>x \<in> A\<close> by (by100 blast)
              hence "A \<in> ?FK" using \<open>A \<in> ?NT\<close> \<open>x \<in> K\<close> by (by100 blast)
              thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
            qed
          qed
        qed
        thus "\<exists>F. finite F \<and> F \<subseteq> ?NT \<and> K \<subseteq> T \<union> \<Union>F"
          using \<open>finite ?FK\<close> by (by100 blast)
      qed
      \<comment> \<open>Step 2: Any loop in Y lies in T \\<union> (finitely many arcs).\<close>
      have hloop_in_finite: "\<And>f. top1_is_loop_on Y TY y0 f \<Longrightarrow>
          \<exists>F. finite F \<and> F \<subseteq> ?NT \<and> f ` top1_unit_interval \<subseteq> T \<union> \<Union>F"
      proof -
        fix f assume hf: "top1_is_loop_on Y TY y0 f"
        \<comment> \<open>f(I) is compact in Y.\<close>
        have hf_cont: "top1_continuous_map_on I_set I_top Y TY f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hf_sub: "f ` I_set \<subseteq> Y"
          using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>f(I) meets finitely many non-tree arc interiors.\<close>
        let ?F = "{A \<in> ?NT. f ` I_set \<inter> (A - top1_arc_endpoints_on A (subspace_topology Y TY A)) \<noteq> {}}"
        have hF_fin: "finite ?F"
        proof -
          \<comment> \<open>For each A \\<in> ?F, pick x\\_A \\<in> f(I) \\<inter> int(A).\<close>
          have "\<forall>A\<in>?F. \<exists>x. x \<in> f ` I_set \<and> x \<in> A \<and>
              x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            by (by100 blast)
          \<comment> \<open>Define sel via SOME for each A.\<close>
          define sel where "sel A = (SOME x. x \<in> f ` I_set \<and> x \<in> A \<and>
              x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A))" for A
          have hsel: "\<forall>A\<in>?F. sel A \<in> f ` I_set \<and> sel A \<in> A \<and>
              sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          proof (intro ballI conjI)
            fix A assume "A \<in> ?F"
            hence "\<exists>x. x \<in> f ` I_set \<and> x \<in> A \<and>
                x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              by (by100 blast)
            from someI_ex[OF this]
            show "sel A \<in> f ` I_set" unfolding sel_def by (by100 blast)
            from someI_ex[OF \<open>\<exists>x. _\<close>]
            show "sel A \<in> A" unfolding sel_def by (by100 blast)
            from someI_ex[OF \<open>\<exists>x. _\<close>]
            show "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              unfolding sel_def by (by100 blast)
          qed
          let ?B = "sel ` ?F"
          \<comment> \<open>?B picks at most 1 point per arc (interior points are in exactly one arc).\<close>
          have hB_sub: "?B \<subseteq> Y" using hsel hf_sub by (by100 blast)
          have hB_in_fI: "?B \<subseteq> f ` I_set" using hsel by (by100 blast)
          \<comment> \<open>For each arc C \\<in> \\<A>: |C \\<inter> ?B| \\<le> 1.\<close>
          have hB_one_per_arc: "\<forall>C\<in>\<A>. finite (C \<inter> ?B) \<and> card (C \<inter> ?B) \<le> 1"
          proof (intro ballI conjI)
            fix C assume "C \<in> \<A>"
            \<comment> \<open>C \\<inter> ?B \\<subseteq> {sel C} (at most).\<close>
            have "C \<inter> ?B \<subseteq> (if C \<in> ?F then {sel C} else {})"
            proof
              fix x assume "x \<in> C \<inter> ?B"
              then obtain A where "A \<in> ?F" "x = sel A" "x \<in> C" by (by100 blast)
              have "sel A \<in> A" using hsel \<open>A \<in> ?F\<close> by (by100 blast)
              have "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using hsel \<open>A \<in> ?F\<close> by (by100 blast)
              show "x \<in> (if C \<in> ?F then {sel C} else {})"
              proof (cases "A = C")
                case True thus ?thesis using \<open>x = sel A\<close> \<open>A \<in> ?F\<close> by (by100 simp)
              next
                case False
                \<comment> \<open>A \\<noteq> C. sel(A) \\<in> A \\<inter> C \\<subseteq> endpoints(A). But sel(A) \\<notin> endpoints(A). Contradiction.\<close>
                have "A \<in> \<A>" using \<open>A \<in> ?F\<close> by (by100 blast)
                from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>C \<in> \<A>\<close> False]
                have "A \<inter> C \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
                hence "sel A \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                  using \<open>sel A \<in> A\<close> \<open>x \<in> C\<close> \<open>x = sel A\<close> by (by100 blast)
                thus ?thesis using \<open>sel A \<notin> top1_arc_endpoints_on A _\<close> by contradiction
              qed
            qed
            \<comment> \<open>The if-then-else in the subset makes automation hard. Prove directly.\<close>
            have hC_sub_at_most_one: "\<exists>S. C \<inter> ?B \<subseteq> S \<and> finite S \<and> card S \<le> 1"
            proof (cases "C \<in> ?F")
              case True
              hence "(if C \<in> ?F then {sel C} else {}) = {sel C}" by (by100 simp)
              hence "C \<inter> ?B \<subseteq> {sel C}"
                using \<open>C \<inter> ?B \<subseteq> (if C \<in> ?F then {sel C} else {})\<close> by (by100 simp)
              moreover have "finite {sel C}" by (by100 simp)
              moreover have "card {sel C} \<le> 1" by (by100 simp)
              ultimately show ?thesis by (by100 blast)
            next
              case False
              hence "(if C \<in> ?F then {sel C} else {}) = {}" by (by100 simp)
              hence "C \<inter> ?B \<subseteq> {}"
                using \<open>C \<inter> ?B \<subseteq> (if C \<in> ?F then {sel C} else {})\<close> by (by100 simp)
              moreover have "finite {}" by (by100 simp)
              moreover have "card {} \<le> (1::nat)" by (by100 simp)
              ultimately show ?thesis by (by100 blast)
            qed
            then obtain S where hS: "C \<inter> ?B \<subseteq> S" "finite S" "card S \<le> 1"
              by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
            show "finite (C \<inter> ?B)" using finite_subset[OF hS(1) hS(2)] .
            show "card (C \<inter> ?B) \<le> 1"
              using card_mono[OF hS(2) hS(1)] hS(3) by (by100 simp)
          qed
          \<comment> \<open>By graph\\_selection\\_set\\_discrete: every subset of ?B is closed in Y.\<close>
          have hB_one_per_arc': "\<forall>A\<in>\<A>. finite (?B \<inter> A) \<and> card (?B \<inter> A) \<le> 1"
          proof (intro ballI conjI)
            fix A assume "A \<in> \<A>"
            have "A \<inter> ?B = ?B \<inter> A" by (by100 blast)
            from hB_one_per_arc[rule_format, OF \<open>A \<in> \<A>\<close>]
            show "finite (?B \<inter> A)" using \<open>A \<inter> ?B = ?B \<inter> A\<close> by (by100 simp)
            from hB_one_per_arc[rule_format, OF \<open>A \<in> \<A>\<close>]
            show "card (?B \<inter> A) \<le> 1" using \<open>A \<inter> ?B = ?B \<inter> A\<close> by (by100 simp)
          qed
          have hB_closed_discrete: "\<forall>S. S \<subseteq> ?B \<longrightarrow> closedin_on Y TY S"
            by (rule graph_selection_set_discrete[OF assms(1) hB_sub h\<A> h\<A>_cover h\<A>_coh hB_one_per_arc'])
          \<comment> \<open>?B \\<subseteq> f(I) compact. Closed discrete in compact = finite.\<close>
          have "finite ?B"
          proof -
            \<comment> \<open>f(I) is compact in Y.\<close>
            have hTY_top: "is_topology_on Y TY"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
            have hI_compact: "top1_compact_on I_set I_top"
              unfolding top1_unit_interval_def top1_unit_interval_topology_def
              using Theorem_27_1[of "0::real" 1] by (by100 simp)
            have hfI_compact: "top1_compact_on (f ` I_set) (subspace_topology Y TY (f ` I_set))"
              by (rule Theorem_26_5[OF top1_unit_interval_topology_is_topology_on hTY_top
                  hI_compact hf_cont])
            \<comment> \<open>?B \\<subseteq> f(I), ?B closed in Y \\<Longrightarrow> ?B compact.\<close>
            have hB_closed: "closedin_on Y TY ?B"
              using hB_closed_discrete by (by100 blast)
            have hB_closed_fI: "closedin_on (f ` I_set)
                (subspace_topology Y TY (f ` I_set)) ?B"
            proof -
              from Theorem_17_2[OF hTY_top hf_sub, THEN iffD2]
              have "\<And>D. closedin_on Y TY D \<Longrightarrow> D \<subseteq> f ` I_set \<Longrightarrow>
                  closedin_on (f ` I_set) (subspace_topology Y TY (f ` I_set)) D"
                by (by100 blast)
              thus ?thesis using hB_closed hB_in_fI by (by100 blast)
            qed
            have hB_compact: "top1_compact_on ?B (subspace_topology Y TY ?B)"
            proof -
              from Theorem_26_2[OF hfI_compact hB_closed_fI]
              have "top1_compact_on ?B (subspace_topology (f ` I_set)
                  (subspace_topology Y TY (f ` I_set)) ?B)" .
              moreover have "subspace_topology (f ` I_set)
                  (subspace_topology Y TY (f ` I_set)) ?B = subspace_topology Y TY ?B"
                by (rule subspace_topology_trans) (use hB_in_fI in blast)
              ultimately show ?thesis by (by5000 metis)
            qed
            \<comment> \<open>?B is compact with discrete (subspace) topology. Compact discrete \\<Longrightarrow> finite.\<close>
            \<comment> \<open>?B compact + discrete (all subsets closed) \\<Longrightarrow> finite.
               Open cover {{x} | x \\<in> ?B} has finite subcover.\<close>
            have hB_subsp_top: "is_topology_on ?B (subspace_topology Y TY ?B)"
              by (rule subspace_topology_is_topology_on[OF hTY_top])
                 (use hB_sub in blast)
            \<comment> \<open>Each {x} is open in ?B (complement is closed).\<close>
            have hB_singletons_open: "\<forall>x\<in>?B. {x} \<in> subspace_topology Y TY ?B"
            proof (intro ballI)
              fix x assume "x \<in> ?B"
              have "?B - {x} \<subseteq> ?B" by (by100 blast)
              hence "closedin_on Y TY (?B - {x})" using hB_closed_discrete by (by100 blast)
              hence "closedin_on ?B (subspace_topology Y TY ?B) (?B - {x})"
                using Theorem_17_2[OF hTY_top, of ?B] hB_sub by (by100 blast)
              hence "?B - (?B - {x}) \<in> subspace_topology Y TY ?B"
                unfolding closedin_on_def by (by100 blast)
              moreover have "?B - (?B - {x}) = {x}" using \<open>x \<in> ?B\<close> by (by100 blast)
              ultimately show "{x} \<in> subspace_topology Y TY ?B" by (by100 simp)
            qed
            \<comment> \<open>Cover: \\<Union>{{x} | x \\<in> ?B} = ?B.\<close>
            have hcover_B: "?B \<subseteq> \<Union>((\<lambda>x. {x}) ` ?B)" by (by100 blast)
            have hcover_open: "(\<lambda>x. {x}) ` ?B \<subseteq> subspace_topology Y TY ?B"
              using hB_singletons_open by (by100 blast)
            \<comment> \<open>Compactness: finite subcover.\<close>
            from compact_finite_subcover[OF hB_compact hcover_open hcover_B]
            obtain Fc where hFc: "finite Fc" "Fc \<subseteq> (\<lambda>x. {x}) ` ?B" "?B \<subseteq> \<Union>Fc"
              by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
            \<comment> \<open>Each element of Fc is a singleton, so \\<Union>Fc is finite.\<close>
            have "finite (\<Union>Fc)"
            proof (rule finite_Union[OF hFc(1)])
              fix S assume "S \<in> Fc"
              hence "S \<in> (\<lambda>x. {x}) ` ?B" using hFc(2) by (by100 blast)
              then obtain x where "x \<in> ?B" "S = {x}" by (by100 blast)
              thus "finite S" by (by100 simp)
            qed
            show "finite ?B" using finite_subset[OF hFc(3) \<open>finite (\<Union>Fc)\<close>] .
          qed
          \<comment> \<open>sel is injective on ?F (different arcs give different points).\<close>
          have "inj_on sel ?F"
          proof (rule inj_onI)
            fix A B assume "A \<in> ?F" "B \<in> ?F" "sel A = sel B"
            \<comment> \<open>sel(A) \\<in> A, sel(A) \\<notin> endpoints(A). Similarly for B.\<close>
            have hA_in: "sel A \<in> A" "sel A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hsel \<open>A \<in> ?F\<close> by (by100 blast)+
            have hB_in: "sel B \<in> B" "sel B \<notin> top1_arc_endpoints_on B (subspace_topology Y TY B)"
              using hsel \<open>B \<in> ?F\<close> by (by100 blast)+
            \<comment> \<open>If A \\<noteq> B: sel(A) \\<in> A \\<inter> B \\<subseteq> endpoints(A). Contradiction.\<close>
            show "A = B"
            proof (rule ccontr)
              assume "A \<noteq> B"
              have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> ?F\<close> \<open>B \<in> ?F\<close> by (by100 blast)+
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
              have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
              have "sel A \<in> B" using hB_in(1) \<open>sel A = sel B\<close> by (by100 simp)
              have "sel A \<in> A \<inter> B" using hA_in(1) \<open>sel A \<in> B\<close> by (by100 blast)
              hence "sel A \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using \<open>A \<inter> B \<subseteq> _\<close> by (by100 blast)
              thus False using hA_in(2) by contradiction
            qed
          qed
          from finite_imageD[OF \<open>finite ?B\<close> \<open>inj_on sel ?F\<close>]
          show "finite ?F" .
        qed
        have hF_NT: "?F \<subseteq> ?NT" by (by100 blast)
        have hf_in_F: "f ` I_set \<subseteq> T \<union> \<Union>?F"
        proof
          fix x assume "x \<in> f ` I_set"
          hence "x \<in> Y" using hf_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          show "x \<in> T \<union> \<Union>?F"
          proof (cases "A \<subseteq> T")
            case True thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
          next
            case False
            hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
            show ?thesis
            proof (cases "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)")
              case True
              \<comment> \<open>x is an endpoint of A. Endpoints of non-tree arcs are in T.\<close>
              hence "x \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              case xFalse: False
              \<comment> \<open>x is in the interior of A. So A \\<in> ?F.\<close>
              hence "x \<in> A - top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using \<open>x \<in> A\<close> by (by100 blast)
              hence "A \<in> ?F" using \<open>A \<in> ?NT\<close> \<open>x \<in> f ` I_set\<close> by (by100 blast)
              thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
            qed
          qed
        qed
        thus "\<exists>F. finite F \<and> F \<subseteq> ?NT \<and> f ` top1_unit_interval \<subseteq> T \<union> \<Union>F"
          using hF_fin hF_NT by (by100 blast)
      qed
      \<comment> \<open>Step 3: Any homotopy lies in T \\<union> (finitely many arcs).\<close>
      have hhtpy_in_finite: "\<And>f1 f2. top1_is_loop_on Y TY y0 f1 \<Longrightarrow>
          top1_is_loop_on Y TY y0 f2 \<Longrightarrow>
          top1_path_homotopic_on Y TY y0 y0 f1 f2 \<Longrightarrow>
          \<exists>F. finite F \<and> F \<subseteq> ?NT \<and>
              top1_path_homotopic_on (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0 y0 f1 f2"
      proof -
        fix f1 f2 assume hf1: "top1_is_loop_on Y TY y0 f1"
          and hf2: "top1_is_loop_on Y TY y0 f2"
          and hfg: "top1_path_homotopic_on Y TY y0 y0 f1 f2"
        \<comment> \<open>f1(I) and f2(I) lie in finite subgraphs.\<close>
        from hloop_in_finite[OF hf1] obtain F1 where hF1: "finite F1" "F1 \<subseteq> ?NT"
            "f1 ` top1_unit_interval \<subseteq> T \<union> \<Union>F1" by (by100 blast)
        from hloop_in_finite[OF hf2] obtain F2 where hF2: "finite F2" "F2 \<subseteq> ?NT"
            "f2 ` top1_unit_interval \<subseteq> T \<union> \<Union>F2" by (by100 blast)
        \<comment> \<open>Extract H from homotopy.\<close>
        from hfg[unfolded top1_path_homotopic_on_def]
        obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY H"
            and hH0: "\<forall>s\<in>I_set. H (s, 0) = f1 s" and hH1: "\<forall>s\<in>I_set. H (s, 1) = f2 s"
            and hHl: "\<forall>t\<in>I_set. H (0, t) = y0" and hHr: "\<forall>t\<in>I_set. H (1, t) = y0"
          by (by100 blast)
        \<comment> \<open>H(I\\<times>I) compact, lies in finitely many arcs.\<close>
        have hH_sub: "H ` (I_set \<times> I_set) \<subseteq> Y"
          using hH_cont unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>H is a loop (I \\<rightarrow> Y) for the purposes of the selection set argument.
           Actually H: I\\<times>I \\<rightarrow> Y. We need H(I\\<times>I) meets finitely many non-tree arcs.
           The same selection set argument applies to any compact subset.\<close>
        \<comment> \<open>For now: let FH cover H(I\\<times>I) the same way F1, F2 cover f1, f2.\<close>
        have "\<exists>FH. finite FH \<and> FH \<subseteq> ?NT \<and> H ` (I_set \<times> I_set) \<subseteq> T \<union> \<Union>FH"
        proof -
          \<comment> \<open>H(I\\<times>I) is compact.\<close>
          have hTY_top: "is_topology_on Y TY"
            using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
          have hI_compact: "top1_compact_on I_set I_top"
            unfolding top1_unit_interval_def top1_unit_interval_topology_def
            using Theorem_27_1[of "0::real" 1] by (by100 simp)
          have hII_compact: "top1_compact_on (I_set \<times> I_set)
              (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
            by (rule Theorem_26_7[OF hI_compact hI_compact])
          have hH_cont': "top1_continuous_map_on (I_set \<times> I_set)
              (product_topology_on top1_unit_interval_topology top1_unit_interval_topology) Y TY H"
            using hH_cont unfolding II_topology_def by (by100 simp)
          have hHI_compact: "top1_compact_on (H ` (I_set \<times> I_set))
              (subspace_topology Y TY (H ` (I_set \<times> I_set)))"
          proof -
            have hII_top: "is_topology_on (I_set \<times> I_set)
                (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
              using product_topology_on_is_topology_on[OF
                top1_unit_interval_topology_is_topology_on
                top1_unit_interval_topology_is_topology_on] .
            from Theorem_26_5[OF hII_top hTY_top hII_compact hH_cont']
            show ?thesis .
          qed
          from hcompact_in_finite[OF hH_sub hHI_compact]
          show ?thesis .
        qed
        then obtain FH where hFH: "finite FH" "FH \<subseteq> ?NT"
            "H ` (I_set \<times> I_set) \<subseteq> T \<union> \<Union>FH"
          by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
        let ?F = "F1 \<union> F2 \<union> FH"
        have "finite ?F" using hF1(1) hF2(1) hFH(1) by (by100 simp)
        have "?F \<subseteq> ?NT" using hF1(2) hF2(2) hFH(2) by (by100 blast)
        \<comment> \<open>H maps into T \\<union> \\<Union>?F, f1 and f2 map into T \\<union> \\<Union>?F.\<close>
        have hH_in_F: "H ` (I_set \<times> I_set) \<subseteq> T \<union> \<Union>?F"
          using hFH(3) by (by5000 blast)
        have hf1_in_F: "f1 ` I_set \<subseteq> T \<union> \<Union>?F"
          using hF1(3) by (by5000 blast)
        have hf2_in_F: "f2 ` I_set \<subseteq> T \<union> \<Union>?F"
          using hF2(3) by (by5000 blast)
        \<comment> \<open>Package as path\\_homotopic\\_on in the subspace T \\<union> \\<Union>?F.\<close>
        have "top1_path_homotopic_on (T \<union> \<Union>?F)
            (subspace_topology Y TY (T \<union> \<Union>?F)) y0 y0 f1 f2"
        proof -
          let ?Y0 = "T \<union> \<Union>?F"
          let ?TY0 = "subspace_topology Y TY ?Y0"
          have hY0_sub: "?Y0 \<subseteq> Y" using hT_sub h\<A> hF1(2) hF2(2) hFH(2) by (by5000 blast)
          have hTY_top: "is_topology_on Y TY"
            using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
          have hII_top: "is_topology_on (I_set \<times> I_set) II_topology"
            unfolding II_topology_def
            using product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on] .
          \<comment> \<open>H continuous into ?Y0 (restrict range).\<close>
          have hH_cont_Y0: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y0 ?TY0 H"
            using Theorem_18_2(5)[OF hII_top hTY_top hTY_top, rule_format]
              hH_cont hH_in_F hY0_sub by (by100 blast)
          \<comment> \<open>f1 continuous into ?Y0.\<close>
          have hf1_cont: "top1_continuous_map_on I_set I_top Y TY f1"
            using hf1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hf1_cont_Y0: "top1_continuous_map_on I_set I_top ?Y0 ?TY0 f1"
            using Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTY_top hTY_top,
                rule_format] hf1_cont hf1_in_F hY0_sub by (by100 blast)
          have hf1_0: "f1 0 = y0" "f1 1 = y0"
            using hf1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          \<comment> \<open>f2 continuous into ?Y0.\<close>
          have hf2_cont: "top1_continuous_map_on I_set I_top Y TY f2"
            using hf2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hf2_cont_Y0: "top1_continuous_map_on I_set I_top ?Y0 ?TY0 f2"
            using Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTY_top hTY_top,
                rule_format] hf2_cont hf2_in_F hY0_sub by (by100 blast)
          have hf2_0: "f2 0 = y0" "f2 1 = y0"
            using hf2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          \<comment> \<open>Package as path\\_homotopic\\_on.\<close>
          show ?thesis
            unfolding top1_path_homotopic_on_def top1_is_path_on_def
            using hH_cont_Y0 hH0 hH1 hHl hHr hf1_cont_Y0 hf1_0 hf2_cont_Y0 hf2_0
            by (by100 blast)
        qed
        show "\<exists>F. finite F \<and> F \<subseteq> ?NT \<and>
            top1_path_homotopic_on (T \<union> \<Union>F)
                (subspace_topology Y TY (T \<union> \<Union>F)) y0 y0 f1 f2"
          apply (rule exI[of _ ?F])
          using \<open>finite ?F\<close> \<open>?F \<subseteq> ?NT\<close>
            \<open>top1_path_homotopic_on (T \<union> \<Union>?F) _ y0 y0 f1 f2\<close>
          by (by100 blast)
      qed
      \<comment> \<open>Step 4: For finite F \\<subseteq> ?NT, T \\<union> (\\<Union>F) is a subgraph with free \\<pi>\\_1.
         This follows from graph\\_pi1\\_free\\_weak\\_finite.\<close>
      have hfinite_subgraph_free: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?NT \<Longrightarrow>
          \<exists>\<iota> S. top1_is_free_group_full_on
              (top1_fundamental_group_carrier (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_mul (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_id (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_invg (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              \<iota> S"
      proof -
        fix F0' assume hF0'fin: "finite F0'" and hF0'_NT: "F0' \<subseteq> ?NT"
        let ?Y' = "T \<union> \<Union>F0'"
        \<comment> \<open>T \\<union> \\<Union>F0' is a connected graph.\<close>
        have hY'_graph: "top1_is_graph_on ?Y' (subspace_topology Y TY ?Y')"
        proof -
          let ?\<B> = "{A \<in> \<A>. A \<subseteq> ?Y'}"
          have h\<B>_eq: "?Y' = \<Union>?\<B>"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> ?Y'"
            thus "x \<in> \<Union>?\<B>"
            proof
              assume "x \<in> T"
              then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" using hT_coverage by (by100 blast)
              have "A \<subseteq> ?Y'" using \<open>A \<subseteq> T\<close> by (by100 blast)
              thus ?thesis using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> by (by100 blast)
            next
              assume "x \<in> \<Union>F0'"
              then obtain A where "A \<in> F0'" "x \<in> A" by (by100 blast)
              have "A \<in> \<A>" using hF0'_NT \<open>A \<in> F0'\<close> by (by100 blast)
              have "A \<subseteq> ?Y'" using \<open>A \<in> F0'\<close> by (by100 blast)
              thus ?thesis using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> by (by100 blast)
            qed
          next
            fix x assume "x \<in> \<Union>?\<B>" thus "x \<in> ?Y'" by (by100 blast)
          qed
          have h\<B>_coh: "\<forall>C. C \<subseteq> ?Y' \<longrightarrow>
              (closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
               (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
            by (rule subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh _ h\<B>_eq])
               (by100 blast)
          have h\<B>_arcs: "\<forall>A\<in>?\<B>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
            using h\<A> by (by100 blast)
          have h\<B>_sub: "\<Union>?\<B> \<subseteq> Y" using h\<A> by (by100 blast)
          have h\<B>_inter: "\<forall>A\<in>?\<B>. \<forall>B\<in>?\<B>. A \<noteq> B \<longrightarrow>
              A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            using h\<A>_inter by (by100 blast)
          have h\<B>_coh': "\<forall>C. C \<subseteq> \<Union>?\<B> \<longrightarrow>
              (closedin_on (\<Union>?\<B>) (subspace_topology Y TY (\<Union>?\<B>)) C \<longleftrightarrow>
               (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
            using h\<B>_coh h\<B>_eq by (by100 simp)
          from subgraph_union_of_arcs_is_graph[OF assms(1) h\<B>_arcs h\<B>_sub h\<B>_inter h\<B>_coh']
          show ?thesis using h\<B>_eq by (by100 simp)
        qed
        have hY'_conn: "top1_connected_on ?Y' (subspace_topology Y TY ?Y')"
        proof -
          have hTY'_top: "is_topology_on Y TY"
            using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
          have hF0'_arcs: "\<forall>A\<in>F0'. top1_is_arc_on A (subspace_topology Y TY A) \<and> A \<subseteq> Y"
            using h\<A> hF0'_NT by (by100 blast)
          have hF0'_meets_T: "\<forall>A\<in>F0'. \<exists>e. e \<in> T \<and> e \<in> A"
          proof (intro ballI)
            fix A assume "A \<in> F0'"
            hence "A \<in> ?NT" using hF0'_NT by (by100 blast)
            have "A \<in> \<A>" using \<open>A \<in> ?NT\<close> by (by100 blast)
            have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            have "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            then obtain ha where hha: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A (subspace_topology Y TY A) ha"
              unfolding top1_is_arc_on_def by (by100 blast)
            have hstrict_Y: "is_topology_on_strict Y TY"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            have hhaus_Y: "is_hausdorff_on Y TY"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            from arc_endpoints_are_boundary[OF hstrict_Y hhaus_Y \<open>A \<subseteq> Y\<close>
                \<open>top1_is_arc_on A _\<close> hha]
            have "ha 0 \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
            hence "ha 0 \<in> T"
              using hNT_endpoints \<open>A \<in> ?NT\<close> by (by100 blast)
            have "ha 0 \<in> A"
            proof -
              have "(0::real) \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 simp)
              thus ?thesis using hha unfolding top1_homeomorphism_on_def
                top1_continuous_map_on_def by (by100 blast)
            qed
            thus "\<exists>e. e \<in> T \<and> e \<in> A" using \<open>ha 0 \<in> T\<close> by (by100 blast)
          qed
          from tree_union_arcs_path_connected[OF hTY'_top hT_tree hT_sub hF0'fin
              hF0'_arcs hF0'_meets_T hT_x0]
          have "top1_path_connected_on ?Y' (subspace_topology Y TY ?Y')" .
          thus ?thesis by (rule path_connected_imp_connected)
        qed
        have hy0_Y': "y0 \<in> ?Y'" using hT_x0 by (by100 blast)
        \<comment> \<open>Apply graph\\_pi1\\_free\\_weak\\_finite to the finite subgraph.\<close>
        show "\<exists>\<iota> S. top1_is_free_group_full_on
            (top1_fundamental_group_carrier ?Y' (subspace_topology Y TY ?Y') y0)
            (top1_fundamental_group_mul ?Y' (subspace_topology Y TY ?Y') y0)
            (top1_fundamental_group_id ?Y' (subspace_topology Y TY ?Y') y0)
            (top1_fundamental_group_invg ?Y' (subspace_topology Y TY ?Y') y0) \<iota> S"
        proof -
          \<comment> \<open>Apply graph\\_pi1\\_free\\_weak\\_finite with arcs = {A \\<in> \\<A>. A \\<subseteq> Y'}, tree = T.\<close>
          let ?\<B> = "{A \<in> \<A>. A \<subseteq> ?Y'}"
          \<comment> \<open>Non-tree arcs of Y' are exactly F0'.\<close>
          have hNT_Y': "{A \<in> ?\<B>. \<not> A \<subseteq> T} = F0'"
          proof (rule set_eqI, rule iffI)
            fix A assume "A \<in> {A \<in> ?\<B>. \<not> A \<subseteq> T}"
            hence "A \<in> \<A>" "A \<subseteq> ?Y'" "\<not> A \<subseteq> T" by (by100 blast)+
            hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
            \<comment> \<open>A \\<subseteq> T \\<union> \\<Union>F0', A \\<notin> T. Pick x \\<in> A - T. x is not an endpoint (endpoints \\<in> T).\<close>
            from \<open>\<not> A \<subseteq> T\<close> obtain x where "x \<in> A" "x \<notin> T" by (by100 blast)
            have "x \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hNT_endpoints \<open>A \<in> ?NT\<close> \<open>x \<notin> T\<close> by (by100 blast)
            \<comment> \<open>x \\<in> A \\<subseteq> ?Y' = T \\<union> \\<Union>F0'. x \\<notin> T. So x \\<in> \\<Union>F0'.\<close>
            have "x \<in> \<Union>F0'" using \<open>A \<subseteq> ?Y'\<close> \<open>x \<in> A\<close> \<open>x \<notin> T\<close> by (by100 blast)
            then obtain B where "B \<in> F0'" "x \<in> B" by (by100 blast)
            \<comment> \<open>x \\<in> int(A) \\<inter> B. If A \\<noteq> B: x \\<in> A \\<inter> B \\<subseteq> endpoints(A). Contradiction.\<close>
            have "A = B"
            proof (rule ccontr)
              assume "A \<noteq> B"
              have "B \<in> \<A>" using \<open>B \<in> F0'\<close> hF0'_NT by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
              have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
              hence "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using \<open>x \<in> A\<close> \<open>x \<in> B\<close> by (by100 blast)
              thus False using \<open>x \<notin> top1_arc_endpoints_on A _\<close> by contradiction
            qed
            thus "A \<in> F0'" using \<open>B \<in> F0'\<close> by (by100 simp)
          next
            fix A assume "A \<in> F0'"
            have "A \<in> ?NT" using \<open>A \<in> F0'\<close> hF0'_NT by (by100 blast)
            hence "A \<in> \<A>" "\<not> A \<subseteq> T" by (by100 blast)+
            have "A \<subseteq> ?Y'" using \<open>A \<in> F0'\<close> by (by100 blast)
            thus "A \<in> {A \<in> ?\<B>. \<not> A \<subseteq> T}" using \<open>A \<in> \<A>\<close> \<open>A \<subseteq> ?Y'\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
          qed
          have "finite {A \<in> ?\<B>. \<not> A \<subseteq> T}" using hNT_Y' hF0'fin by (by100 simp)
          \<comment> \<open>Delegate to graph\\_pi1\\_free\\_weak\\_finite.\<close>
          show ?thesis
            sorry \<comment> \<open>Delegation to graph\\_pi1\\_free\\_weak\\_finite.
               All preconditions verified: Y' graph + connected + y0 \\<in> Y' + finite NT + arcs + coherent + tree + endpoints.
               Type matching issue with subspace\\_topology prevents direct application.\<close>
        qed
      qed
      \<comment> \<open>Step 5: Combine: \\<pi>\\_1(Y) is free.
         For each c \\<in> \\<pi>\\_1(Y), c lies in \\<pi>\\_1 of some T \\<union> F (Step 2).
         That \\<pi>\\_1 is free (Step 4).
         Inclusion is injective (Steps 1 + Lemma\\_55\\_1).
         Hence \\<pi>\\_1(Y) is free.\<close>
      \<comment> \<open>Assembly: define generators and verify free\\_group\\_full\\_on.
         For each A \\<in> ?NT, the generator loop g\\_A goes: path in T from y0 to
         one endpoint of A, traverse A, path in T back from other endpoint to y0.
         \\<pi>\\_1(Y) is free on {[g\\_A] | A \\<in> ?NT}.
         The proof mirrors Theorem 71.3, with retraction giving inclusion injectivity.\<close>
      \<comment> \<open>The key simplification vs 71.3: inclusion T\\<union>\\<Union>F \\<hookrightarrow> Y is injective on \\<pi>\\_1
         because T\\<union>\\<Union>F is a retract of Y (hretract). So Lemma\\_55\\_1\\_retract\\_injective
         directly gives: if f ~ g in Y and both are loops in T\\<union>\\<Union>F, then f ~ g in T\\<union>\\<Union>F.
         This replaces the complex free\\_group\\_hom\\_subset\\_injective argument from 71.3.\<close>
      \<comment> \<open>Condition 4 (generated): every loop lies in some T\\<union>\\<Union>F (hloop\\_in\\_finite).
         In T\\<union>\\<Union>F, \\<pi>\\_1 is free, hence generated by the g\\_A for A \\<in> F.
         Under inclusion, these map to the g\\_A in \\<pi>\\_1(Y).\<close>
      \<comment> \<open>Condition 5 (no word = id): word uses finitely many generators from F.
         Word non-trivial in T\\<union>\\<Union>F (freeness). By retraction/Lemma 55.1:
         inclusion injective. Hence word non-trivial in Y.\<close>
      show ?thesis
        sorry \<comment> \<open>Full assembly. Needs generator construction (paths in tree + arc traversal).
           Each condition follows from Steps 1-4 + retraction injectivity.
           ~500 lines following the 71.3 pattern, but simpler due to retraction.\<close>
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

