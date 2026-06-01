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
    show ?thesis
    proof -
      \<comment> \<open>Step A: Define \\<Phi>: Cov(p) \\<rightarrow> N(H)/H.
         For h \\<in> Cov(p): h(e0) \\<in> p\\<inverse>(b0). Since E is path-connected, choose
         path \\<gamma>: e0 \\<rightarrow> h(e0). Then p\\<circ>\\<gamma> is a loop at b0, so [p\\<circ>\\<gamma>] \\<in> \\<pi>\\_1(B,b0).
         Show [p\\<circ>\\<gamma>] \\<in> N(H). Define \\<Phi>(h) = [p\\<circ>\\<gamma>]\\<cdot>H.\<close>
      \<comment> \<open>Step B: \\<Phi> is well-defined (different path gives same coset).
         If \\<gamma>' is another path e0 \\<rightarrow> h(e0), then \\<gamma>*rev(\\<gamma>') is a loop at e0,
         so [p\\<circ>(\\<gamma>*rev(\\<gamma>'))] \\<in> H. Hence [p\\<circ>\\<gamma>] and [p\\<circ>\\<gamma>'] differ by H.\<close>
      \<comment> \<open>Step C: \\<Phi> is a group homomorphism.
         \\<Phi>(h\\<circ>k) = [p\\<circ>(\\<gamma>*(h\\<circ>\\<delta>))] H where \\<gamma>: e0\\<rightarrow>h(e0), \\<delta>: e0\\<rightarrow>k(e0).
         = [p\\<circ>\\<gamma>]*[p\\<circ>\\<delta>] H = \\<Phi>(h)*\\<Phi>(k) (since p\\<circ>h = p).\<close>
      \<comment> \<open>Step D: \\<Phi> is injective.
         \\<Phi>(h) = eH \\<Rightarrow> [p\\<circ>\\<gamma>] \\<in> H \\<Rightarrow> \\<gamma> lifts to a loop at e0 (unique lift)
         \\<Rightarrow> h(e0) = e0 \\<Rightarrow> h = id (covering transformation is determined by value at e0).\<close>
      \<comment> \<open>Step E: \\<Phi> is surjective.
         For [\\<alpha>]\\<cdot>H \\<in> N(H)/H: \\<alpha> is a loop at b0 with [\\<alpha>] \\<in> N(H).
         Lift \\<alpha> to \\<tilde>\\<alpha> in E starting at e0. Define h by unique lifting:
         h = (unique covering transformation sending e0 to \\<tilde>\\<alpha>(1)).
         Then \\<Phi>(h) = [p\\<circ>\\<tilde>\\<alpha>]\\<cdot>H = [\\<alpha>]\\<cdot>H.\<close>
      \<comment> \<open>Step A: Define \\<Psi>: Cov(p) \\<rightarrow> p\\<inverse>(b0) by \\<Psi>(h) = h(e0).
         \\<Psi> is injective (covering transformation determined by value at one point).\<close>
      define \<Psi> where "\<Psi> h = h e0" for h :: "'e \<Rightarrow> 'e"
      have h\<Psi>_fiber: "\<forall>h\<in>?Cov. \<Psi> h \<in> E \<and> p (\<Psi> h) = b0"
      proof (intro ballI conjI)
        fix h assume "h \<in> ?Cov"
        hence hct: "top1_covering_transformation_on E TE B TB p h" by (by100 blast)
        have "top1_homeomorphism_on E TE E TE h"
          using hct unfolding top1_covering_transformation_on_def by (by100 blast)
        hence "bij_betw h E E" unfolding top1_homeomorphism_on_def by (by100 blast)
        hence "h ` E = E" unfolding bij_betw_def by (by100 blast)
        hence "h e0 \<in> E" using assms(6) by (by100 blast)
        thus "\<Psi> h \<in> E" unfolding \<Psi>_def by simp
        have "\<forall>e\<in>E. p (h e) = p e"
          using hct unfolding top1_covering_transformation_on_def by (by100 blast)
        hence "p (h e0) = p e0" using assms(6) by (by100 blast)
        thus "p (\<Psi> h) = b0" unfolding \<Psi>_def using assms(7) by simp
      qed
      \<comment> \<open>\\<Psi> injective: covering transformation determined by value at e0.\<close>
      have h\<Psi>_inj: "inj_on \<Psi> ?Cov"
      proof (rule inj_onI)
        fix h k assume hh: "h \<in> ?Cov" and hk: "k \<in> ?Cov" and heq: "\<Psi> h = \<Psi> k"
        hence "h e0 = k e0" unfolding \<Psi>_def by simp
        have hh_ct: "top1_covering_transformation_on E TE B TB p h"
          using hh by (by100 blast)
        have hk_ct: "top1_covering_transformation_on E TE B TB p k"
          using hk by (by100 blast)
        have hh_cont: "top1_continuous_map_on E TE E TE h"
          using hh_ct unfolding top1_covering_transformation_on_def top1_homeomorphism_on_def
          by (by100 blast)
        have hk_cont: "top1_continuous_map_on E TE E TE k"
          using hk_ct unfolding top1_covering_transformation_on_def top1_homeomorphism_on_def
          by (by100 blast)
        have hlift: "\<forall>e\<in>E. p (h e) = p (k e)"
        proof (intro ballI)
          fix e assume "e \<in> E"
          have "p (h e) = p e"
            using hh_ct \<open>e \<in> E\<close> unfolding top1_covering_transformation_on_def by (by100 blast)
          moreover have "p (k e) = p e"
            using hk_ct \<open>e \<in> E\<close> unfolding top1_covering_transformation_on_def by (by100 blast)
          ultimately show "p (h e) = p (k e)" by simp
        qed
        have hTE_l: "is_topology_on E TE"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hTB_l: "is_topology_on B TB"
          using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
        have hE_conn: "top1_connected_on E TE"
          by (rule path_connected_imp_connected[OF assms(4)])
        from covering_lift_unique_connected[OF assms(3) hTE_l hTB_l hTE_l hE_conn
            hh_cont hk_cont hlift assms(6) \<open>h e0 = k e0\<close>]
        have hE_eq: "\<forall>e\<in>E. h e = k e" .
        \<comment> \<open>Outside E: both CTs map to identity.\<close>
        have hout_h: "\<forall>e. e \<notin> E \<longrightarrow> h e = e"
          using hh_ct unfolding top1_covering_transformation_on_def by (by100 blast)
        have hout_k: "\<forall>e. e \<notin> E \<longrightarrow> k e = e"
          using hk_ct unfolding top1_covering_transformation_on_def by (by100 blast)
        show "h = k"
        proof (rule ext)
          fix e show "h e = k e"
          proof (cases "e \<in> E")
            case True thus ?thesis using hE_eq by (by100 blast)
          next
            case False
            hence "h e = e" using hout_h by simp
            moreover have "k e = e" using False hout_k by simp
            ultimately show ?thesis by simp
          qed
        qed
      qed
      \<comment> \<open>Step B: Image of \\<Psi> = \\<Phi>(N(H)/H).
         h(e0) = e1 iff \\<exists> CT sending e0 to e1 iff [p\\<circ>\\<gamma>] \\<in> N(H)
         (by Theorem 79.2 + basepoint\\_change\\_image\\_hom).\<close>
      have h\<Psi>_image: "\<Psi> ` ?Cov = {e \<in> E. p e = b0 \<and>
          top1_fundamental_group_image_hom E TE e B TB b0 p = ?H}"
      proof (rule set_eqI, rule iffI)
        \<comment> \<open>Forward: \\<Psi>(h) \\<in> RHS.\<close>
        fix e1 assume "e1 \<in> \<Psi> ` ?Cov"
        then obtain h where hh: "h \<in> ?Cov" and he1: "\<Psi> h = e1" by (by100 blast)
        hence hct: "top1_covering_transformation_on E TE B TB p h" by (by100 blast)
        have "e1 \<in> E" using h\<Psi>_fiber hh he1 by (by100 blast)
        have "p e1 = b0" using h\<Psi>_fiber hh he1 by (by100 blast)
        \<comment> \<open>h is a covering equivalence (E,e0)\\<rightarrow>(E,e1).\<close>
        \<comment> \<open>By Theorem 79.2: \\<exists> such equiv \\<Leftrightarrow> p*(\\<pi>\\_1(E,e0)) = p*(\\<pi>\\_1(E,e1)).\<close>
        have "top1_fundamental_group_image_hom E TE e1 B TB b0 p = ?H"
        proof -
          \<comment> \<open>h: (E,e0) \\<rightarrow> (E,e1) is a homeomorphism with p\\<circ>h = p and h(e0) = e1.\<close>
          have "top1_homeomorphism_on E TE E TE h"
            using hct unfolding top1_covering_transformation_on_def by (by100 blast)
          have "\<forall>e\<in>E. p (h e) = p e"
            using hct unfolding top1_covering_transformation_on_def by (by100 blast)
          have "h e0 = e1" using he1 unfolding \<Psi>_def by simp
          \<comment> \<open>Apply Theorem 79.2 direction \\<Rightarrow>.\<close>
          \<comment> \<open>From Theorem 79.2 with E'=E, p'=p, e0'=e1:
             (\\<exists>h. homeo \\<and> p\\<circ>h = p \\<and> h(e0) = e1) \\<leftrightarrow> image\\_hom(E,e0) = image\\_hom(E,e1).\<close>
          have hb0B: "b0 \<in> B"
            using top1_covering_map_on_surj[OF assms(3)] assms(6) assms(7) by (by100 blast)
          from Theorem_79_2[OF assms(1) assms(2) assms(1) assms(3) assms(7)
              assms(3) \<open>p e1 = b0\<close> assms(4) assms(4) assms(5) assms(5) assms(6) \<open>e1 \<in> E\<close> hb0B]
          have hiff: "(\<exists>h'. top1_homeomorphism_on E TE E TE h' \<and> (\<forall>e\<in>E. p (h' e) = p e) \<and> h' e0 = e1) \<longleftrightarrow>
              ?H = top1_fundamental_group_image_hom E TE e1 B TB b0 p" .
          have hexists: "\<exists>h'. top1_homeomorphism_on E TE E TE h' \<and> (\<forall>e\<in>E. p (h' e) = p e) \<and> h' e0 = e1"
            by (rule exI[of _ h],
                intro conjI,
                rule \<open>top1_homeomorphism_on E TE E TE h\<close>,
                rule \<open>\<forall>e\<in>E. p (h e) = p e\<close>,
                rule \<open>h e0 = e1\<close>)
          from hiff hexists have "?H = top1_fundamental_group_image_hom E TE e1 B TB b0 p"
            by (by100 blast)
          thus ?thesis by simp
        qed
        show "e1 \<in> {e \<in> E. p e = b0 \<and>
            top1_fundamental_group_image_hom E TE e B TB b0 p = ?H}"
          using \<open>e1 \<in> E\<close> \<open>p e1 = b0\<close> \<open>top1_fundamental_group_image_hom _ _ e1 _ _ _ _ = ?H\<close>
          by (by100 blast)
      next
        \<comment> \<open>Backward: e1 \\<in> RHS \\<Rightarrow> e1 \\<in> image(\\<Psi>).\<close>
        fix e1 assume "e1 \<in> {e \<in> E. p e = b0 \<and>
            top1_fundamental_group_image_hom E TE e B TB b0 p = ?H}"
        hence he1E: "e1 \<in> E" and hpe1: "p e1 = b0"
            and him: "top1_fundamental_group_image_hom E TE e1 B TB b0 p = ?H"
          by (by100 blast)+
        \<comment> \<open>p*(\\<pi>\\_1(E,e1)) = H = p*(\\<pi>\\_1(E,e0)). By Theorem 79.2 \\<Leftarrow>:
           \\<exists> covering equivalence h: (E,e0) \\<rightarrow> (E,e1) with p\\<circ>h = p.\<close>
        \<comment> \<open>By Theorem 79.2 backward: image\\_hom = H \\<Rightarrow> \\<exists> covering equivalence h.\<close>
        have hb0B_bwd: "b0 \<in> B"
          using top1_covering_map_on_surj[OF assms(3)] assms(6) assms(7) by (by100 blast)
        from Theorem_79_2[OF assms(1) assms(2) assms(1) assms(3) assms(7)
            assms(3) hpe1 assms(4) assms(4) assms(5) assms(5) assms(6) he1E hb0B_bwd]
        have "(\<exists>h. top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e) \<and> h e0 = e1) \<longleftrightarrow>
            ?H = top1_fundamental_group_image_hom E TE e1 B TB b0 p" .
        hence "\<exists>h. top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e) \<and> h e0 = e1"
          using him by simp
        then obtain h' where hh'_homeo: "top1_homeomorphism_on E TE E TE h'"
            and hh'_lift: "\<forall>e\<in>E. p (h' e) = p e" and hh'_e0: "h' e0 = e1"
          by (by100 blast)
        \<comment> \<open>h' is a covering transformation: homeomorphism + p\\<circ>h' = p + outside E = id.\<close>
        \<comment> \<open>Issue: h' might not be id outside E. Need to adjust.\<close>
        define h_adj where "h_adj e = (if e \<in> E then h' e else e)" for e
        have hh_adj_ct: "top1_covering_transformation_on E TE B TB p h_adj"
          unfolding top1_covering_transformation_on_def
        proof (intro conjI)
          \<comment> \<open>h\\_adj is a homeomorphism on E: same as h' on E.\<close>
          have h_agree: "\<forall>e\<in>E. h_adj e = h' e"
            unfolding h_adj_def by (by100 simp)
          show "top1_homeomorphism_on E TE E TE h_adj"
            unfolding top1_homeomorphism_on_def
          proof (intro conjI)
            have hTE: "is_topology_on E TE"
              using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
            show "is_topology_on E TE" by (rule hTE)
            show "is_topology_on E TE" by (rule hTE)
            \<comment> \<open>bij\\_betw: h\\_adj on E = h' on E, which is bijective.\<close>
            have "bij_betw h' E E" using hh'_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            show "bij_betw h_adj E E"
            proof -
              have "\<forall>e\<in>E. h_adj e = h' e" using h_agree .
              have "h_adj ` E = h' ` E"
              proof (rule image_cong)
                fix e assume "e \<in> E" thus "h_adj e = h' e" using h_agree by (by100 blast)
              qed simp
              moreover have "inj_on h_adj E"
              proof (rule inj_onI)
                fix x y assume "x \<in> E" "y \<in> E" "h_adj x = h_adj y"
                hence "h' x = h' y" using h_agree by (by100 auto)
                moreover have "inj_on h' E"
                  using \<open>bij_betw h' E E\<close> unfolding bij_betw_def by (by100 blast)
                ultimately show "x = y"
                  using \<open>x \<in> E\<close> \<open>y \<in> E\<close> unfolding inj_on_def by (by100 blast)
              qed
              ultimately show ?thesis using \<open>bij_betw h' E E\<close>
                unfolding bij_betw_def by (by100 blast)
            qed
            \<comment> \<open>Continuity: preimage under h\\_adj = preimage under h' (on E).\<close>
            show "top1_continuous_map_on E TE E TE h_adj"
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix e assume "e \<in> E" thus "h_adj e \<in> E"
                using h_agree \<open>bij_betw h' E E\<close> unfolding bij_betw_def by (by100 blast)
            next
              fix V assume "V \<in> TE"
              have "{e \<in> E. h_adj e \<in> V} = {e \<in> E. h' e \<in> V}"
                using h_agree by (by100 auto)
              moreover have "{e \<in> E. h' e \<in> V} \<in> TE"
                using hh'_homeo \<open>V \<in> TE\<close>
                unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
              ultimately show "{e \<in> E. h_adj e \<in> V} \<in> TE" by simp
            qed
            \<comment> \<open>Inverse continuity: inv\\_into E h\\_adj = inv\\_into E h' (agree on E).\<close>
            show "top1_continuous_map_on E TE E TE (inv_into E h_adj)"
            proof -
              \<comment> \<open>inv\\_into E h\\_adj agrees with inv\\_into E h' on E.\<close>
              have hinv_agree: "\<forall>e\<in>E. inv_into E h_adj e = inv_into E h' e"
              proof (intro ballI)
                fix e assume "e \<in> E"
                have "inj_on h_adj E" using \<open>bij_betw h_adj E E\<close> unfolding bij_betw_def by (by100 blast)
                have "inj_on h' E" using \<open>bij_betw h' E E\<close> unfolding bij_betw_def by (by100 blast)
                have "e \<in> h_adj ` E" using \<open>e \<in> E\<close> \<open>bij_betw h_adj E E\<close>
                  unfolding bij_betw_def by (by100 blast)
                then obtain x where "x \<in> E" "h_adj x = e" by (by100 blast)
                have "h_adj x = h' x" using h_agree \<open>x \<in> E\<close> by (by100 blast)
                hence "h' x = e" using \<open>h_adj x = e\<close> by simp
                have "inv_into E h_adj e = x"
                  using inv_into_f_f[OF \<open>inj_on h_adj E\<close> \<open>x \<in> E\<close>] \<open>h_adj x = e\<close> by simp
                moreover have "inv_into E h' e = x"
                  using inv_into_f_f[OF \<open>inj_on h' E\<close> \<open>x \<in> E\<close>] \<open>h' x = e\<close> by simp
                ultimately show "inv_into E h_adj e = inv_into E h' e" by simp
              qed
              \<comment> \<open>h' inverse is continuous.\<close>
              have hinv_cont: "top1_continuous_map_on E TE E TE (inv_into E h')"
                using hh'_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              \<comment> \<open>Transfer continuity via pointwise agreement.\<close>
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix e assume "e \<in> E"
                thus "inv_into E h_adj e \<in> E"
                  using hinv_agree hinv_cont unfolding top1_continuous_map_on_def by (by100 auto)
              next
                fix V assume "V \<in> TE"
                have "{e \<in> E. inv_into E h_adj e \<in> V} = {e \<in> E. inv_into E h' e \<in> V}"
                  using hinv_agree by (by100 auto)
                thus "{e \<in> E. inv_into E h_adj e \<in> V} \<in> TE"
                  using hinv_cont \<open>V \<in> TE\<close> unfolding top1_continuous_map_on_def by (by100 auto)
              qed
            qed
          qed
          show "\<forall>e\<in>E. p (h_adj e) = p e"
            using hh'_lift h_agree by (by100 auto)
          show "\<forall>e. e \<notin> E \<longrightarrow> h_adj e = e"
            unfolding h_adj_def by (by100 simp)
        qed
        have "h_adj e0 = e1" using hh'_e0 assms(6) unfolding h_adj_def by (by100 simp)
        hence "\<Psi> h_adj = e1" unfolding \<Psi>_def by simp
        moreover have "h_adj \<in> ?Cov" using hh_adj_ct by (by100 blast)
        ultimately show "e1 \<in> \<Psi> ` ?Cov" by (by100 blast)
      qed
      \<comment> \<open>Step C: \\<Phi>\\<inverse>\\<circ>\\<Psi> is a homomorphism.
         Key: for h,k \\<in> Cov(p), choose \\<gamma>: e0\\<rightarrow>h(e0), \\<delta>: e0\\<rightarrow>k(e0).
         Then h\\<circ>\\<delta>: h(e0)\\<rightarrow>h(k(e0)). So \\<gamma>*(h\\<circ>\\<delta>) lifts \\<alpha>*\\<beta>
         where \\<alpha>=p\\<circ>\\<gamma>, \\<beta>=p\\<circ>\\<delta>. The lifting correspondence gives
         \\<Phi>([\\<alpha>*\\<beta>]H) = (\\<gamma>*(h\\<circ>\\<delta>))(1) = h(k(e0)) = \\<Psi>(h\\<circ>k).\<close>
      \<comment> \<open>Since \\<Phi> is a bijection (Theorem 54.4/54.6), and \\<Psi> is injective
         with the right image, \\<Phi>\\<inverse>\\<circ>\\<Psi> is a bijection Cov(p) \\<rightarrow> N(H)/H.
         The homomorphism property follows from the path composition.\<close>
      show ?thesis sorry \<comment> \<open>Assembly: \\<Phi>\\<inverse>\\<circ>\\<Psi> is a group isomorphism Cov(p) \\<cong> N(H)/H.\<close>
    qed
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


\<comment> \<open>Helper: apply graph\\_pi1\\_free\\_weak\\_finite to a graph given all preconditions.
   This wrapper avoids let-binding expansion issues when applying inside proofs.\<close>
lemma graph_pi1_free_weak_apply:
  assumes "top1_is_graph_on Y_sub TY_sub"
      and "top1_connected_on Y_sub TY_sub"
      and "y0 \<in> Y_sub"
      and "finite {A \<in> \<A>_sub. \<not> A \<subseteq> T_sub}"
      and "\<forall>A\<in>\<A>_sub. A \<subseteq> Y_sub \<and> top1_is_arc_on A (subspace_topology Y_sub TY_sub A)"
      and "\<Union>\<A>_sub = Y_sub"
      and "\<forall>A\<in>\<A>_sub. \<forall>B\<in>\<A>_sub. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y_sub TY_sub A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y_sub TY_sub B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and "\<forall>C. C \<subseteq> Y_sub \<longrightarrow>
           (closedin_on Y_sub TY_sub C \<longleftrightarrow>
            (\<forall>A\<in>\<A>_sub. closedin_on A (subspace_topology Y_sub TY_sub A) (A \<inter> C)))"
      and "top1_is_tree_on T_sub (subspace_topology Y_sub TY_sub T_sub)"
      and "T_sub \<subseteq> Y_sub"
      and "\<forall>A\<in>\<A>_sub. A \<subseteq> T_sub \<or>
           A \<inter> T_sub \<subseteq> top1_arc_endpoints_on A (subspace_topology Y_sub TY_sub A)"
      and "y0 \<in> T_sub"
      and "\<forall>A\<in>{A\<in>\<A>_sub. \<not> A \<subseteq> T_sub}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y_sub TY_sub A). e \<in> T_sub"
  shows "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
      (top1_fundamental_group_carrier Y_sub TY_sub y0)
      (top1_fundamental_group_mul Y_sub TY_sub y0)
      (top1_fundamental_group_id Y_sub TY_sub y0)
      (top1_fundamental_group_invg Y_sub TY_sub y0)
      \<iota> S"
  by (rule graph_pi1_free_weak_finite[where n="card {A \<in> \<A>_sub. \<not> A \<subseteq> T_sub}",
      OF assms(1) assms(2) assms(3) _ assms(4) assms(5) assms(6) assms(7) assms(8)
         assms(9) assms(10) assms(11) assms(12) assms(13)])
     (by100 simp)

text \<open>Helper: free\\_group\\_full\\_on depends only on \\<iota> restricted to S.
  If \\<iota>1 and \\<iota>2 agree on S, the predicates are equivalent.\<close>
lemma free_group_full_on_cong:
  assumes hfree: "top1_is_free_group_full_on G mul e invg \<iota>1 S"
      and heq: "\<forall>s\<in>S. \<iota>1 s = \<iota>2 s"
  shows "top1_is_free_group_full_on G mul e invg \<iota>2 S"
proof -
  from hfree have h1: "top1_is_group_on G mul e invg"
    and h2: "\<forall>s\<in>S. \<iota>1 s \<in> G"
    and h3: "inj_on \<iota>1 S"
    and h4: "G = top1_subgroup_generated_on G mul e invg (\<iota>1 ` S)"
    and h5: "\<forall>ws. ws \<noteq> [] \<longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>1 s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws ! i) \<in> S) \<longrightarrow>
        top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota>1 s, b)) ws) \<noteq> e"
    unfolding top1_is_free_group_full_on_def by (by100 blast)+
  have himg: "\<iota>2 ` S = \<iota>1 ` S"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> \<iota>2 ` S"
    then obtain s where "s \<in> S" "x = \<iota>2 s" by (by100 blast)
    hence "x = \<iota>1 s" using heq by (by100 simp)
    thus "x \<in> \<iota>1 ` S" using \<open>s \<in> S\<close> by (by100 blast)
  next
    fix x assume "x \<in> \<iota>1 ` S"
    then obtain s where "s \<in> S" "x = \<iota>1 s" by (by100 blast)
    hence "x = \<iota>2 s" using heq by (by100 simp)
    thus "x \<in> \<iota>2 ` S" using \<open>s \<in> S\<close> by (by100 blast)
  qed
  show ?thesis unfolding top1_is_free_group_full_on_def
  proof (intro conjI)
    show "top1_is_group_on G mul e invg" by (rule h1)
    show "\<forall>s\<in>S. \<iota>2 s \<in> G" using h2 heq by (by100 simp)
    show "inj_on \<iota>2 S" using h3 heq unfolding inj_on_def by (by100 simp)
    show "G = top1_subgroup_generated_on G mul e invg (\<iota>2 ` S)"
      using h4 himg by (by100 simp)
    show "\<forall>ws. ws \<noteq> [] \<longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>2 s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws ! i) \<in> S) \<longrightarrow>
        top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota>2 s, b)) ws) \<noteq> e"
    proof (intro allI impI)
      fix ws assume hne: "ws \<noteq> []"
        and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>2 s, b)) ws)"
        and hS: "\<forall>i<length ws. fst (ws ! i) \<in> S"
      \<comment> \<open>Key: map (\\<lambda>(s,b). (\\<iota>2 s, b)) ws = map (\\<lambda>(s,b). (\\<iota>1 s, b)) ws.\<close>
      have hmap_eq: "map (\<lambda>(s, b). (\<iota>2 s, b)) ws = map (\<lambda>(s, b). (\<iota>1 s, b)) ws"
      proof (rule list_eq_iff_nth_eq[THEN iffD2], intro conjI allI impI)
        show "length (map (\<lambda>(s, b). (\<iota>2 s, b)) ws) = length (map (\<lambda>(s, b). (\<iota>1 s, b)) ws)"
          by (by100 simp)
      next
        fix i assume "i < length (map (\<lambda>(s, b). (\<iota>2 s, b)) ws)"
        hence hi: "i < length ws" by (by100 simp)
        obtain s b where hab: "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
        have "fst (ws ! i) = s" using hab by (by100 simp)
        have "s \<in> S" using hS hi \<open>fst (ws ! i) = s\<close> by (by100 blast)
        hence "\<iota>1 s = \<iota>2 s" using heq by (by100 blast)
        show "map (\<lambda>(s, b). (\<iota>2 s, b)) ws ! i = map (\<lambda>(s, b). (\<iota>1 s, b)) ws ! i"
          using hi hab \<open>\<iota>1 s = \<iota>2 s\<close> by (by100 simp)
      qed
      have hred1: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>1 s, b)) ws)"
        using hred hmap_eq by (by100 simp)
      from h5 hne hred1 hS
      have "top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota>1 s, b)) ws) \<noteq> e"
        by (by100 blast)
      thus "top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota>2 s, b)) ws) \<noteq> e"
        using hmap_eq[symmetric] by simp
    qed
  qed
qed

text \<open>Algebraic helper: if G is isomorphic to Z and g generates G, then G is free on \{g\}.
  This is the key lemma for the base case of harc\_loops\_free (book Step 2).
  Proof: conditions 1-3 are trivial. Condition 4 is the generation assumption.
  Condition 5: a single-generator reduced word is g\^n or (invg g)\^n (n $\ge$ 1).
  Under any iso $\phi$: G $\to$ Z, $\phi$(g) = $\pm$1 (since g generates G $\cong$ Z),
  so $\phi$(g\^n) = $\pm$n $\ne$ 0, hence g\^n $\ne$ e.\<close>
lemma iso_Z_generator_free_single:
  assumes hiso: "top1_groups_isomorphic_on G mulG top1_Z_group top1_Z_mul"
      and hgrp: "top1_is_group_on G mulG eG invgG"
      and hg: "g \<in> G"
      and hgen: "G = top1_subgroup_generated_on G mulG eG invgG {g}"
  shows "top1_is_free_group_full_on G mulG eG invgG (\<lambda>_. g) {()}"
  unfolding top1_is_free_group_full_on_def
proof (intro conjI)
  show "top1_is_group_on G mulG eG invgG" by (rule hgrp)
  show "\<forall>s\<in>{()}. (\<lambda>_. g) s \<in> G" using hg by (by100 blast)
  show "inj_on (\<lambda>_. g) {()}" unfolding inj_on_def by (by100 blast)
  show "G = top1_subgroup_generated_on G mulG eG invgG ((\<lambda>_. g) ` {()})"
    using hgen by (by100 simp)
  \<comment> \<open>Condition 5: no non-trivial reduced word = e.
     Single-generator reduced words are all-True or all-False.
     Under iso to Z, g maps to \\<pm>1, so g\^n maps to \\<pm>n \\<ne> 0.\<close>
  \<comment> \<open>Condition 5: no non-trivial reduced word evaluates to e.
     A reduced word over {()} with generator g has all entries (g, True) or (g, False).
     Word product = g\^n or (invg g)\^n. Under iso to Z, this is \\<pm>n \\<ne> 0.\<close>
  show "\<forall>ws::(unit \<times> bool) list.
      ws \<noteq> [] \<longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>_. g) s, b)) ws) \<longrightarrow>
      (\<forall>i<length ws. fst (ws ! i) \<in> {()}) \<longrightarrow>
      top1_group_word_product mulG eG invgG (map (\<lambda>(s, b). ((\<lambda>_. g) s, b)) ws) \<noteq> eG"
  proof (intro allI impI)
    fix ws :: "(unit \<times> bool) list"
    assume hne: "ws \<noteq> []"
      and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (g, b)) ws)"
      and hS: "\<forall>i<length ws. fst (ws ! i) \<in> {()}"
    \<comment> \<open>Get iso \\<phi>: G \\<rightarrow> Z.\<close>
    from hiso obtain \<phi> where h\<phi>: "top1_group_iso_on G mulG top1_Z_group top1_Z_mul \<phi>"
      unfolding top1_groups_isomorphic_on_def by (by100 blast)
    \<comment> \<open>\\<phi> is a hom with \\<phi>(g) generating Z, so \\<phi>(g) = \\<pm>1.\<close>
    have h\<phi>_hom: "top1_group_hom_on G mulG top1_Z_group top1_Z_mul \<phi>"
      using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
    have h\<phi>_bij: "bij_betw \<phi> G top1_Z_group"
      using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
    have h\<phi>_inj: "inj_on \<phi> G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>\\<phi>(g) generates Z \\<Rightarrow> \\<phi>(g) = \\<pm>1.\<close>
    have h\<phi>g_gen: "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {\<phi> g}"
    proof -
      have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
      have hg_sub: "{g} \<subseteq> G" using hg by (by100 blast)
      have h\<phi>_surj: "\<phi> ` G = top1_Z_group" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
      from surj_hom_generated[OF hgrp hZ_grp h\<phi>_hom h\<phi>_surj hg_sub hgen]
      show ?thesis by (by100 simp)
    qed
    have h\<phi>g_pm1: "\<phi> g = 1 \<or> \<phi> g = -1"
    proof -
      \<comment> \<open>1 \\<in> subgroup\\_generated {\\<phi>(g)} in Z. By word representation,
         1 is a product of \\<phi>(g) and -\\<phi>(g), i.e. 1 = n * \\<phi>(g) for some n.
         So \\<phi>(g) divides 1 in Z, hence \\<phi>(g) = \\<pm>1.\<close>
      have h1_in: "(1::int) \<in> top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {\<phi> g}"
        using h\<phi>g_gen unfolding top1_Z_group_def by (by100 blast)
      have h\<phi>g_Z: "\<phi> g \<in> top1_Z_group" using hg h\<phi>_bij unfolding bij_betw_def top1_Z_group_def
        by (by100 blast)
      have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
      from subgroup_generated_word_repr[OF hZ_grp _ h1_in]
      have "1 = top1_Z_id \<or> (\<exists>ws. length ws > 0 \<and>
          (\<forall>i<length ws. ws ! i \<in> {\<phi> g} \<or> (\<exists>s\<in>{\<phi> g}. ws ! i = top1_Z_invg s)) \<and>
          foldr top1_Z_mul ws top1_Z_id = 1)"
        unfolding top1_Z_group_def by (by100 blast)
      hence "\<phi> g dvd (1::int)"
      proof (elim disjE)
        assume "1 = top1_Z_id" thus ?thesis unfolding top1_Z_id_def by (by100 simp)
      next
        assume "\<exists>ws. length ws > 0 \<and>
            (\<forall>i<length ws. ws ! i \<in> {\<phi> g} \<or> (\<exists>s\<in>{\<phi> g}. ws ! i = top1_Z_invg s)) \<and>
            foldr top1_Z_mul ws top1_Z_id = 1"
        then obtain ws' where hlen: "length ws' > 0"
            and hels: "\<forall>i<length ws'. ws' ! i \<in> {\<phi> g} \<or> (\<exists>s\<in>{\<phi> g}. ws' ! i = top1_Z_invg s)"
            and hsum: "foldr top1_Z_mul ws' top1_Z_id = 1" by (by100 blast)
        \<comment> \<open>Each element of ws' is \\<phi>(g) or -(\\<phi>(g)). So foldr (+) ws' 0 is a multiple of \\<phi>(g).\<close>
        have "\<forall>x \<in> set ws'. x = \<phi> g \<or> x = -(\<phi> g)"
        proof (intro ballI)
          fix x assume "x \<in> set ws'"
          then obtain i where "i < length ws'" "ws' ! i = x"
            using in_set_conv_nth[of x ws'] by (by100 blast)
          from hels[rule_format, OF \<open>i < length ws'\<close>]
          show "x = \<phi> g \<or> x = -(\<phi> g)"
            using \<open>ws' ! i = x\<close> unfolding top1_Z_invg_def by (by100 blast)
        qed
        hence "\<exists>n::int. foldr top1_Z_mul ws' top1_Z_id = n * \<phi> g"
        proof (induction ws')
          case Nil
          have "foldr top1_Z_mul [] top1_Z_id = 0" unfolding top1_Z_id_def by (by100 simp)
          also have "(0::int) = 0 * \<phi> g" by (by100 simp)
          finally show ?case by (by100 blast)
        next
          case (Cons a ws'')
          have "a = \<phi> g \<or> a = -(\<phi> g)" using Cons.prems by (by100 simp)
          have IH: "\<exists>n. foldr top1_Z_mul ws'' top1_Z_id = n * \<phi> g"
            using Cons.prems Cons.IH by (by100 simp)
          then obtain n where hn: "foldr top1_Z_mul ws'' top1_Z_id = n * \<phi> g" by (by100 blast)
          from \<open>a = \<phi> g \<or> a = -(\<phi> g)\<close>
          have "\<exists>m::int. a = m * \<phi> g"
          proof
            assume "a = \<phi> g"
            hence "a = 1 * \<phi> g" by (by100 simp)
            thus ?thesis by (by100 blast)
          next
            assume "a = - \<phi> g"
            hence "a = (-1) * \<phi> g" by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          then obtain m :: int where hm: "a = m * \<phi> g" by (by100 blast)
          have "foldr top1_Z_mul (a # ws'') top1_Z_id = a + foldr top1_Z_mul ws'' top1_Z_id"
            unfolding top1_Z_mul_def top1_Z_id_def by (by100 simp)
          also have "... = m * \<phi> g + n * \<phi> g" using hm hn by (by100 simp)
          also have "... = (m + n) * \<phi> g" by (by100 algebra)
          finally show ?case by (by100 blast)
        qed
        then obtain n where "foldr top1_Z_mul ws' top1_Z_id = n * \<phi> g" by (by100 blast)
        hence "1 = n * \<phi> g" using hsum by (by100 simp)
        have "\<phi> g dvd (1::int)"
        proof -
          from \<open>1 = n * \<phi> g\<close> have "(1::int) = \<phi> g * n"
            by (by100 algebra)
          thus ?thesis unfolding dvd_def by (by100 blast)
        qed
        thus ?thesis .
      qed
      thus ?thesis using int_one_le_iff_zero_less zdvd_imp_le by (by5000 fastforce)
    qed
    \<comment> \<open>Word product under \\<phi> is \\<pm>n for reduced word of length n.\<close>
    have h_word_ne: "top1_group_word_product mulG eG invgG (map (\<lambda>(s, b). (g, b)) ws) \<noteq> eG"
    proof -
      \<comment> \<open>Apply hom\\_word\\_product to get \\<phi>(word\\_product) = word\\_product in Z.\<close>
      let ?ws_g = "map (\<lambda>(s, b). (g, b)) ws"
      have hg_entries: "\<forall>i<length ?ws_g. fst (?ws_g ! i) \<in> G"
      proof (intro allI impI)
        fix i assume "i < length ?ws_g"
        hence "i < length ws" by (by100 simp)
        obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
        hence "?ws_g ! i = (g, b)" using \<open>i < length ws\<close> by (by100 simp)
        thus "fst (?ws_g ! i) \<in> G" using hg by (by100 simp)
      qed
      have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
      from hom_word_product[OF hgrp hZ_grp h\<phi>_hom hg_entries]
      have h\<phi>_wp: "\<phi> (top1_group_word_product mulG eG invgG ?ws_g) =
          top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg (map (\<lambda>(x, b). (\<phi> x, b)) ?ws_g)" .
      \<comment> \<open>The Z word product is \\<pm>length(ws) since \\<phi>(g) = \\<pm>1.\<close>
      \<comment> \<open>The double map simplifies: map (\\<lambda>(x,b). (\\<phi> x, b)) (map (\\<lambda>(s,b). (g, b)) ws) = map (\\<lambda>(s,b). (\\<phi> g, b)) ws.\<close>
      have hmap_simp: "map (\<lambda>(x, b). (\<phi> x, b)) ?ws_g = map (\<lambda>(s, b). (\<phi> g, b)) ws"
        by (induction ws) (by100 auto)+
      have h\<phi>_wp_ne: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (map (\<lambda>(x, b). (\<phi> x, b)) ?ws_g) \<noteq> top1_Z_id"
      proof -
        \<comment> \<open>Reduced word over single generator: all entries have same bool.\<close>
        \<comment> \<open>Word product in Z = n * \\<phi>(g) or -n * \\<phi>(g), where n = length.\<close>
        \<comment> \<open>Word product in Z of single-generator reduced word.\<close>
        \<comment> \<open>Since \\<phi>(g) = \\<pm>1 and length \\<ge> 1, the product is \\<pm>length \\<ne> 0.\<close>
        \<comment> \<open>Since the word is reduced and single-generator, all entries have the same bool.\<close>
        have h_consec: "\<And>j. j + 1 < length ws \<Longrightarrow> snd (ws ! j) = snd (ws ! (j + 1))"
        proof -
          fix j assume hj1: "j + 1 < length ws"
          \<comment> \<open>In map (\\<lambda>(s,b). (g,b)) ws, fst at j = fst at j+1 = g.\<close>
          let ?mws = "map (\<lambda>(s, b). (g, b)) ws"
          have hj1m: "j + 1 < length ?mws" using hj1 by (by100 simp)
          have hj: "j < length ws" using hj1 by (by100 simp)
          obtain s1 b1 where "ws ! j = (s1, b1)" by (cases "ws ! j") (by100 blast)
          hence "?mws ! j = (g, b1)" using hj by (by100 simp)
          obtain s2 b2 where "ws ! (j+1) = (s2, b2)" by (cases "ws ! (j+1)") (by100 blast)
          hence "?mws ! (j+1) = (g, b2)" using hj1 by (by100 simp)
          have "fst (?mws ! j) = fst (?mws ! (j+1))"
            using \<open>?mws ! j = (g, b1)\<close> \<open>?mws ! (j+1) = (g, b2)\<close> by (by100 simp)
          \<comment> \<open>If snd differed, the word would not be reduced.\<close>
          have "\<not> (fst (?mws ! j) = fst (?mws ! (j+1)) \<and> snd (?mws ! j) \<noteq> snd (?mws ! (j+1)))"
            using cancel_pair_not_reduced[OF hj1m] hred by (by100 blast)
          hence "snd (?mws ! j) = snd (?mws ! (j+1))"
            using \<open>fst (?mws ! j) = fst (?mws ! (j+1))\<close> by (by100 blast)
          hence "b1 = b2" using \<open>?mws ! j = (g, b1)\<close> \<open>?mws ! (j+1) = (g, b2)\<close> by (by100 simp)
          thus "snd (ws ! j) = snd (ws ! (j + 1))"
            using \<open>ws ! j = (s1, b1)\<close> \<open>ws ! (j+1) = (s2, b2)\<close> by (by100 simp)
        qed
        have h_uniform_bool: "\<forall>i<length ws. snd (ws ! i) = snd (ws ! 0)"
        proof -
          \<comment> \<open>By transitivity: snd(ws!i) = snd(ws!(i-1)) = ... = snd(ws!0).\<close>
          { fix i have "i < length ws \<longrightarrow> snd (ws ! i) = snd (ws ! 0)"
            proof (induction i)
              case 0 thus ?case by (by100 simp)
            next
              case (Suc j)
              show ?case
              proof (intro impI)
                assume "Suc j < length ws"
                hence "j < length ws" by (by100 simp)
                hence "snd (ws ! j) = snd (ws ! 0)" using Suc.IH by (by100 simp)
                moreover have "snd (ws ! j) = snd (ws ! (j + 1))"
                  using h_consec \<open>Suc j < length ws\<close> by (by100 simp)
                ultimately show "snd (ws ! Suc j) = snd (ws ! 0)" by (by100 simp)
              qed
            qed }
          thus ?thesis by (by100 blast)
        qed
        \<comment> \<open>Word product in Z for uniform-bool list.\<close>
        obtain b0 where hb0: "snd (ws ! 0) = b0" by (by100 blast)
        have h_ne_0: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (map (\<lambda>(s, b). (\<phi> g, b)) ws) \<noteq> (0::int)"
        proof -
          \<comment> \<open>All entries have bool b0. Case split on b0.\<close>
          have h_all_b0: "\<forall>i<length ws. snd (ws ! i) = b0"
            using h_uniform_bool hb0 by (by100 blast)
          have "\<exists>n::int. top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
              (map (\<lambda>(s, b). (\<phi> g, b)) ws) = n \<and> \<bar>n\<bar> = int (length ws)"
          proof (cases b0)
            case True
            \<comment> \<open>All True: word product = length * \\<phi>(g).\<close>
            have h_all_True: "\<forall>i<length ws. snd (ws ! i) = True"
              using h_all_b0 True by (by100 simp)
            have hval: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                (map (\<lambda>(s, b). (\<phi> g, b)) ws) = int (length ws) * \<phi> g"
              using h_all_True
            proof (induction ws)
              case Nil thus ?case unfolding top1_Z_id_def by (by100 simp)
            next
              case (Cons a ws')
              obtain s1 b1 where ha: "a = (s1, b1)" by (cases a) (by100 blast)
              have hb1: "b1 = True"
                using Cons.prems[rule_format, of 0] ha by (by100 simp)
              have h_ws'_all: "\<forall>i<length ws'. snd (ws' ! i) = True"
              proof (intro allI impI)
                fix i assume "i < length ws'"
                from Cons.prems[rule_format, of "Suc i"]
                show "snd (ws' ! i) = True" using \<open>i < length ws'\<close> by (by100 simp)
              qed
              from Cons.IH[OF h_ws'_all]
              have IH: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                  (map (\<lambda>(s, b). (\<phi> g, b)) ws') = int (length ws') * \<phi> g" .
              have "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                  (map (\<lambda>(s, b). (\<phi> g, b)) (a # ws')) =
                  top1_Z_mul (\<phi> g) (top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                      (map (\<lambda>(s, b). (\<phi> g, b)) ws'))"
                using ha hb1 by (by100 simp)
              also have "... = \<phi> g + int (length ws') * \<phi> g"
                using IH unfolding top1_Z_mul_def by (by100 simp)
              also have "... = (1 + int (length ws')) * \<phi> g" by (by100 algebra)
              also have "... = int (length (a # ws')) * \<phi> g" by (by100 simp)
              finally show ?case .
            qed
            have "\<bar>int (length ws) * \<phi> g\<bar> = int (length ws)"
              using h\<phi>g_pm1 by (by100 auto)
            thus ?thesis using hval by (by100 blast)
          next
            case False
            \<comment> \<open>All False: word product = -(length * \\<phi>(g)).\<close>
            have h_all_False: "\<forall>i<length ws. snd (ws ! i) = False"
              using h_all_b0 False by (by100 simp)
            have hval: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                (map (\<lambda>(s, b). (\<phi> g, b)) ws) = -(int (length ws) * \<phi> g)"
              using h_all_False
            proof (induction ws)
              case Nil thus ?case unfolding top1_Z_id_def by (by100 simp)
            next
              case (Cons a ws')
              obtain s1 b1 where ha: "a = (s1, b1)" by (cases a) (by100 blast)
              have hb1: "b1 = False"
                using Cons.prems[rule_format, of 0] ha by (by100 simp)
              have h_ws'_all: "\<forall>i<length ws'. snd (ws' ! i) = False"
              proof (intro allI impI)
                fix i assume "i < length ws'"
                from Cons.prems[rule_format, of "Suc i"]
                show "snd (ws' ! i) = False" using \<open>i < length ws'\<close> by (by100 simp)
              qed
              from Cons.IH[OF h_ws'_all]
              have IH: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                  (map (\<lambda>(s, b). (\<phi> g, b)) ws') = -(int (length ws') * \<phi> g)" .
              have "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                  (map (\<lambda>(s, b). (\<phi> g, b)) (a # ws')) =
                  top1_Z_mul (top1_Z_invg (\<phi> g)) (top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
                      (map (\<lambda>(s, b). (\<phi> g, b)) ws'))"
                using ha hb1 by (by100 simp)
              also have "... = -(\<phi> g) + (-(int (length ws') * \<phi> g))"
                using IH unfolding top1_Z_mul_def top1_Z_invg_def by (by100 simp)
              also have "... = -((1 + int (length ws')) * \<phi> g)" by (by100 algebra)
              also have "... = -(int (length (a # ws')) * \<phi> g)" by (by100 simp)
              finally show ?case .
            qed
            have "\<bar>-(int (length ws) * \<phi> g)\<bar> = int (length ws)"
              using h\<phi>g_pm1 by (by100 auto)
            thus ?thesis using hval by (by100 blast)
          qed
          then obtain n where hn: "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
              (map (\<lambda>(s, b). (\<phi> g, b)) ws) = n" and habs: "\<bar>n\<bar> = int (length ws)"
            by (by100 blast)
          have "length ws \<ge> 1" using hne by (cases ws) (by100 simp)+
          hence "int (length ws) \<ge> 1" by (by100 simp)
          hence "n \<noteq> 0" using habs by (by100 linarith)
          thus ?thesis using hn by (by100 simp)
        qed
        \<comment> \<open>Transfer: map (\\<lambda>(x,b). (\\<phi> x, b)) (map (\\<lambda>(s,b). (g,b)) ws) = map (\\<lambda>(s,b). (\\<phi> g, b)) ws.\<close>
        have hmap_eq: "map (\<lambda>(x, b). (\<phi> x, b)) (map (\<lambda>(s, b). (g, b)) ws) =
            map (\<lambda>(s, b). (\<phi> g, b)) ws"
        proof (induction ws)
          case Nil thus ?case by (by100 simp)
        next
          case (Cons a ws')
          obtain s1 b1 where "a = (s1, b1)" by (cases a) (by100 blast)
          thus ?case using Cons.IH by (by100 simp)
        qed
        have hmap_comp: "map (\<lambda>(s, b). (\<phi> g, b)) ws =
            map ((\<lambda>(x, b). (\<phi> x, b)) \<circ> (\<lambda>(s, b). (g, b))) ws"
        proof (induction ws)
          case Nil thus ?case by (by100 simp)
        next
          case (Cons a ws')
          obtain s1 b1 where "a = (s1, b1)" by (cases a) (by100 blast)
          thus ?case using Cons.IH unfolding comp_def by (by100 simp)
        qed
        from h_ne_0[unfolded hmap_comp]
        show ?thesis unfolding top1_Z_id_def by (by100 simp)
      qed
      \<comment> \<open>Since \\<phi> is injective and \\<phi>(eG) = 0 = top1\\_Z\\_id, word\\_product \\<ne> eG.\<close>
      have h\<phi>_e: "\<phi> eG = top1_Z_id"
        by (rule hom_preserves_id[OF hgrp hZ_grp h\<phi>_hom])
      show ?thesis
      proof
        assume "top1_group_word_product mulG eG invgG ?ws_g = eG"
        hence "\<phi> (top1_group_word_product mulG eG invgG ?ws_g) = \<phi> eG" by simp
        hence "\<phi> (top1_group_word_product mulG eG invgG ?ws_g) = top1_Z_id" using h\<phi>_e by simp
        thus False using h\<phi>_wp h\<phi>_wp_ne by simp
      qed
    qed
    thus "top1_group_word_product mulG eG invgG (map (\<lambda>(s, b). ((\<lambda>_. g) s, b)) ws) \<noteq> eG"
      by (by100 simp)
  qed
qed

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
      \<comment> \<open>Step 1: Inclusion \\<pi>\\_1(T \\<union> F) \\<hookrightarrow> \\<pi>\\_1(Y) is injective.
         Uses Lemma\\_55\\_1\\_retract\\_injective + hhtpy\\_in\\_finite.\<close>
      have hincl_inj: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?NT \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
          inj_on (top1_fundamental_group_induced_on (T \<union> \<Union>F)
              (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x))
            (top1_fundamental_group_carrier (T \<union> \<Union>F)
              (subspace_topology Y TY (T \<union> \<Union>F)) y0)"
      proof -
        fix F assume hFfin: "finite F" and hF_NT: "F \<subseteq> ?NT" and hF_ne: "F \<noteq> {}"
        let ?YF = "T \<union> \<Union>F"
        let ?TYF = "subspace_topology Y TY ?YF"
        let ?incl = "top1_fundamental_group_induced_on ?YF ?TYF y0 Y TY y0 (\<lambda>x. x)"
        have hYF_sub: "?YF \<subseteq> Y" using hT_sub h\<A> hF_NT by (by100 blast)
        have hy0_YF: "y0 \<in> ?YF" using hT_x0 by (by100 blast)
        have hTY_top: "is_topology_on Y TY"
          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        show "inj_on ?incl (top1_fundamental_group_carrier ?YF ?TYF y0)"
        proof (rule inj_onI)
          fix c1 c2 assume hc1: "c1 \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
              and hc2: "c2 \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
              and heq: "?incl c1 = ?incl c2"
          \<comment> \<open>Extract representative loops.\<close>
          from hc1[unfolded top1_fundamental_group_carrier_def]
          obtain f1 where hf1_loop: "top1_is_loop_on ?YF ?TYF y0 f1"
              and hc1_eq: "c1 = {g. top1_loop_equiv_on ?YF ?TYF y0 f1 g}"
            by (by100 blast)
          from hc2[unfolded top1_fundamental_group_carrier_def]
          obtain f2 where hf2_loop: "top1_is_loop_on ?YF ?TYF y0 f2"
              and hc2_eq: "c2 = {g. top1_loop_equiv_on ?YF ?TYF y0 f2 g}"
            by (by100 blast)
          \<comment> \<open>Lift to loops in Y.\<close>
          have hf1Y: "top1_is_loop_on Y TY y0 f1"
          proof -
            have "top1_continuous_map_on I_set I_top ?YF ?TYF f1"
              using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            have "top1_continuous_map_on I_set I_top Y TY (id \<circ> f1)"
              by (rule top1_continuous_map_on_comp[OF \<open>top1_continuous_map_on I_set I_top ?YF ?TYF f1\<close>
                  Theorem_18_2(2)[OF hTY_top hTY_top hTY_top, rule_format, OF hYF_sub]])
            hence "top1_continuous_map_on I_set I_top Y TY f1" by (by100 simp)
            moreover have "f1 0 = y0" "f1 1 = y0"
              using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
            ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
              by (by100 blast)
          qed
          have hf2Y: "top1_is_loop_on Y TY y0 f2"
          proof -
            have "top1_continuous_map_on I_set I_top ?YF ?TYF f2"
              using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            have "top1_continuous_map_on I_set I_top Y TY (id \<circ> f2)"
              by (rule top1_continuous_map_on_comp[OF \<open>top1_continuous_map_on I_set I_top ?YF ?TYF f2\<close>
                  Theorem_18_2(2)[OF hTY_top hTY_top hTY_top, rule_format, OF hYF_sub]])
            hence "top1_continuous_map_on I_set I_top Y TY f2" by (by100 simp)
            moreover have "f2 0 = y0" "f2 1 = y0"
              using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
            ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
              by (by100 blast)
          qed
          \<comment> \<open>incl(c1) = incl(c2) means f1 \\<sim> f2 in Y.
             Following ac9 proof: f1 \\<in> incl c1, hence f1 \\<in> incl c2 (by heq).
             Extract f' with loop\\_equiv(?YF, f2, f'), loop\\_equiv(Y, f', f1).
             Then f2 ~ f' in ?YF, hence in Y. f' ~ f1 in Y. Transitivity: f1 ~ f2 in Y.\<close>
          have "top1_path_homotopic_on Y TY y0 y0 f1 f2"
          proof -
            \<comment> \<open>f1 \\<in> ?incl c1.\<close>
            have "f1 \<in> ?incl c1"
            proof -
              have "f1 \<in> {l. top1_loop_equiv_on ?YF ?TYF y0 f1 l}"
              proof -
                have hTYF_top: "is_topology_on ?YF ?TYF"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hYF_sub])
                from top1_loop_equiv_on_refl[OF hf1_loop] show ?thesis by (by100 blast)
              qed
              moreover have "(\<lambda>x. x) \<circ> f1 = f1" by (by100 auto)
              hence "top1_loop_equiv_on Y TY y0 ((\<lambda>x. x) \<circ> f1) f1"
                using top1_loop_equiv_on_refl[OF hf1Y] by (by100 simp)
              ultimately show ?thesis
                unfolding top1_fundamental_group_induced_on_def hc1_eq by (by100 blast)
            qed
            hence "f1 \<in> ?incl c2" using heq by (by100 simp)
            then obtain f' where hf'2: "top1_loop_equiv_on ?YF ?TYF y0 f2 f'"
                and hf'1: "top1_loop_equiv_on Y TY y0 ((\<lambda>x. x) \<circ> f') f1"
              unfolding top1_fundamental_group_induced_on_def hc2_eq by (by100 blast)
            have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
            have hf'1': "top1_loop_equiv_on Y TY y0 f' f1" using hf'1 \<open>(\<lambda>x. x) \<circ> f' = f'\<close>
              by (by100 simp)
            have "top1_loop_equiv_on Y TY y0 f2 f'"
            proof -
              from hf'2[unfolded top1_loop_equiv_on_def]
              have "top1_path_homotopic_on ?YF ?TYF y0 y0 f2 f'" by (by100 blast)
              from path_homotopic_subspace_to_ambient[OF hTY_top hYF_sub _ this]
              have "top1_path_homotopic_on Y TY y0 y0 f2 f'" by (by100 blast)
              have "top1_is_loop_on Y TY y0 f'"
                using hf'1' unfolding top1_loop_equiv_on_def by (by100 blast)
              thus ?thesis unfolding top1_loop_equiv_on_def
                using hf2Y \<open>top1_is_loop_on Y TY y0 f'\<close>
                  \<open>top1_path_homotopic_on Y TY y0 y0 f2 f'\<close> by (by100 blast)
            qed
            from top1_loop_equiv_on_trans[OF hTY_top this hf'1']
            have "top1_loop_equiv_on Y TY y0 f2 f1" .
            from top1_loop_equiv_on_sym[OF this]
            show "top1_path_homotopic_on Y TY y0 y0 f1 f2"
              unfolding top1_loop_equiv_on_def by (by100 blast)
          qed
          \<comment> \<open>By hhtpy\\_in\\_finite: f1 \\<sim> f2 in T \\<union> \\<Union>F' for some F'.\<close>
          from hhtpy_in_finite[OF hf1Y hf2Y \<open>top1_path_homotopic_on Y TY y0 y0 f1 f2\<close>]
          obtain F' where hF'fin: "finite F'" and hF'_NT: "F' \<subseteq> ?NT"
              and hF'htpy: "top1_path_homotopic_on (T \<union> \<Union>F')
                  (subspace_topology Y TY (T \<union> \<Union>F')) y0 y0 f1 f2"
            by (by100 blast)
          let ?FF = "F \<union> F'"
          let ?YFF = "T \<union> \<Union>?FF"
          let ?TYFF = "subspace_topology Y TY ?YFF"
          \<comment> \<open>Lift homotopy from T \\<union> \\<Union>F' to T \\<union> \\<Union>(F \\<union> F').\<close>
          have hF'_sub_FF: "T \<union> \<Union>F' \<subseteq> ?YFF" by (by100 blast)
          have hYFF_sub': "?YFF \<subseteq> Y" using hYF_sub hF_NT hF'_NT h\<A> by (by100 blast)
          have hhtpy_FF: "top1_path_homotopic_on ?YFF ?TYFF y0 y0 f1 f2"
          proof -
            have hTYFF_top: "is_topology_on ?YFF ?TYFF"
              by (rule subspace_topology_is_topology_on[OF hTY_top hYFF_sub'])
            have "subspace_topology ?YFF ?TYFF (T \<union> \<Union>F') =
                subspace_topology Y TY (T \<union> \<Union>F')"
              by (rule subspace_topology_trans) (use hF'_sub_FF in blast)
            from path_homotopic_subspace_to_ambient[OF hTYFF_top hF'_sub_FF
                this[symmetric] hF'htpy]
            show ?thesis .
          qed
          \<comment> \<open>T \\<union> \\<Union>F is a retract of T \\<union> \\<Union>(F \\<union> F').
             Construction: for each A \\<in> F'\\\\F with endpoints a,b \\<in> T:
             - T is path-connected (tree = SC = PC)
             - Choose path p\\_A: [0,1] \\<rightarrow> T from a to b
             - h\\_A: [0,1] \\<rightarrow> A the arc homeomorphism
             - Define r|A = p\\_A \\<circ> h\\_A\\<inverse> (continuous, maps A to T)
             - r(a) = p\\_A(0) = a, r(b) = p\\_A(1) = b (agrees at endpoints)
             - r|\\_{T \\<union> \\<Union>F} = id
             Continuity via pasting\\_lemma\\_two\\_closed:
             - T \\<union> \\<Union>(F \\<union> F') = (T \\<union> \\<Union>F) \\<union> A\\_1 \\<union> ... \\<union> A\\_k (closed cover)
             - r continuous on each piece, agrees on overlaps
             - By iterated pasting: r continuous\<close>
          have hretract: "top1_retract_of_on ?YFF ?TYFF ?YF"
          proof -
            \<comment> \<open>T is path-connected (tree = SC \\<Longrightarrow> PC).\<close>
            have hT_pc: "top1_path_connected_on T (subspace_topology Y TY T)"
            proof -
              from hT_tree[unfolded top1_is_tree_on_def]
              have "top1_simply_connected_on T (subspace_topology Y TY T)" by (by100 blast)
              from top1_simply_connected_on_path_connected[OF this]
              show ?thesis .
            qed
            \<comment> \<open>For each arc A \\<in> F'\\\\F: define retraction rA: A \\<rightarrow> T.
               rA = p\\_A \\<circ> h\\_A\\<inverse> where h\\_A: [0,1] \\<rightarrow> A, p\\_A: [0,1] \\<rightarrow> T (tree path).\<close>
            have hG_finite: "finite (F' - F)" using hF'fin by (by100 simp)
            have hG_NT: "F' - F \<subseteq> ?NT" using hF'_NT by (by100 blast)
            \<comment> \<open>For each A \\<in> F'\\\\F, retraction data exists.\<close>
            have hretract_data: "\<forall>A \<in> F' - F. \<exists>rA.
                top1_continuous_map_on A (subspace_topology Y TY A) T (subspace_topology Y TY T) rA \<and>
                (\<forall>x \<in> A \<inter> T. rA x = x)"
            proof (intro ballI)
              fix A assume "A \<in> F' - F"
              hence "A \<in> ?NT" using hG_NT by (by100 blast)
              hence "A \<in> \<A>" by (by100 blast)
              have hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
              have hA_sub: "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
              from hA_arc[unfolded top1_is_arc_on_def]
              obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
                by (by100 blast)
              let ?a = "h 0" let ?b = "h 1"
              have hstrict_Y: "is_topology_on_strict Y TY"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have hhaus_Y: "is_hausdorff_on Y TY"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hstrict_Y hhaus_Y hA_sub hA_arc hh]
              have hep_eq: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {?a, ?b}" .
              have ha_ep: "?a \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using hep_eq by (by100 blast)
              have hb_ep: "?b \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                using hep_eq by (by100 blast)
              have ha_T: "?a \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> ha_ep by (by100 blast)
              have hb_T: "?b \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> hb_ep by (by100 blast)
              have h0_I: "(0::real) \<in> I_set" and h1_I: "(1::real) \<in> I_set"
                unfolding top1_unit_interval_def by (by100 simp)+
              have ha_A: "?a \<in> A"
                using hh h0_I unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
                by (by100 blast)
              have hb_A: "?b \<in> A"
                using hh h1_I unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
                by (by100 blast)
              \<comment> \<open>Path from a to b in T.\<close>
              from hT_pc[unfolded top1_path_connected_on_def]
              have "\<exists>p. top1_is_path_on T (subspace_topology Y TY T) ?a ?b p"
                using ha_T hb_T by (by100 blast)
              then obtain p where hp: "top1_is_path_on T (subspace_topology Y TY T) ?a ?b p"
                by (by100 blast)
              \<comment> \<open>h\\<inverse>: A \\<rightarrow> [0,1] is continuous.\<close>
              have hinv: "top1_homeomorphism_on A (subspace_topology Y TY A) I_set I_top (inv_into I_set h)"
                by (rule homeomorphism_inverse[OF hh])
              \<comment> \<open>rA = p \\<circ> h\\<inverse>: A \\<rightarrow> T.\<close>
              let ?rA = "p \<circ> inv_into I_set h"
              have hinv_cont: "top1_continuous_map_on A (subspace_topology Y TY A) I_set I_top (inv_into I_set h)"
                using hinv unfolding top1_homeomorphism_on_def by (by100 blast)
              have hp_cont: "top1_continuous_map_on I_set I_top T (subspace_topology Y TY T) p"
                using hp unfolding top1_is_path_on_def by (by100 blast)
              have "top1_continuous_map_on A (subspace_topology Y TY A) T (subspace_topology Y TY T) ?rA"
                by (rule top1_continuous_map_on_comp[OF hinv_cont hp_cont])
              moreover have "\<forall>x \<in> A \<inter> T. ?rA x = x"
              proof (intro ballI)
                fix x assume "x \<in> A \<inter> T"
                \<comment> \<open>x is an endpoint of A: x \\<in> {h 0, h 1}.\<close>
                have "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                proof -
                  from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
                  have "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" .
                  moreover have "\<not> A \<subseteq> T" using \<open>A \<in> ?NT\<close> by (by100 blast)
                  ultimately have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    by (by100 blast)
                  thus ?thesis using \<open>x \<in> A \<inter> T\<close> by (by100 blast)
                qed
                hence "x = ?a \<or> x = ?b" using hep_eq by (by100 blast)
                thus "?rA x = x"
                proof
                  assume "x = ?a"
                  have hh_bij: "bij_betw h I_set A"
                    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hh_inj: "inj_on h I_set"
                    using hh_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into I_set h ?a = 0"
                    using inv_into_f_f[OF hh_inj h0_I] by (by100 simp)
                  moreover have "p 0 = ?a" using hp unfolding top1_is_path_on_def by (by100 blast)
                  ultimately show "?rA x = x" using \<open>x = ?a\<close> by (by100 simp)
                next
                  assume "x = ?b"
                  have hh_bij: "bij_betw h I_set A"
                    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hh_inj: "inj_on h I_set"
                    using hh_bij unfolding bij_betw_def by (by100 blast)
                  have "inv_into I_set h ?b = 1"
                    using inv_into_f_f[OF hh_inj h1_I] by (by100 simp)
                  moreover have "p 1 = ?b" using hp unfolding top1_is_path_on_def by (by100 blast)
                  ultimately show "?rA x = x" using \<open>x = ?b\<close> by (by100 simp)
                qed
              qed
              ultimately show "\<exists>rA. top1_continuous_map_on A (subspace_topology Y TY A) T (subspace_topology Y TY T) rA \<and>
                  (\<forall>x \<in> A \<inter> T. rA x = x)" by (by100 blast)
            qed
            \<comment> \<open>Choose retraction functions.\<close>
            from bchoice[OF hretract_data]
            obtain rr where hrr: "\<forall>A \<in> F' - F.
                top1_continuous_map_on A (subspace_topology Y TY A) T (subspace_topology Y TY T) (rr A) \<and>
                (\<forall>x \<in> A \<inter> T. rr A x = x)" by (by100 blast)
            \<comment> \<open>Define r: ?YFF \\<rightarrow> ?YF.\<close>
            define r where "r x = (if x \<in> ?YF then x
              else rr (THE A. A \<in> F' - F \<and> x \<in> A \<and> x \<notin> T) x)" for x
            \<comment> \<open>r maps ?YFF into ?YF.\<close>
            have hr_maps: "\<forall>x \<in> ?YFF. r x \<in> ?YF"
            proof (intro ballI)
              fix x assume "x \<in> ?YFF"
              show "r x \<in> ?YF"
              proof (cases "x \<in> ?YF")
                case True thus ?thesis unfolding r_def by (by100 simp)
              next
                case False
                hence hx_not_T: "x \<notin> T" and hx_not_F: "x \<notin> \<Union>F" by (by100 blast)+
                from \<open>x \<in> ?YFF\<close> False have "x \<in> \<Union>(F' - F)" by (by100 blast)
                then obtain A where "A \<in> F' - F" "x \<in> A" by (by100 blast)
                \<comment> \<open>A is the unique such arc (arc interiors are disjoint).\<close>
                have hA_unique: "\<And>B. B \<in> F' - F \<Longrightarrow> x \<in> B \<Longrightarrow> x \<notin> T \<Longrightarrow> B = A"
                proof -
                  fix B assume "B \<in> F' - F" "x \<in> B" "x \<notin> T"
                  show "B = A"
                  proof (rule ccontr)
                    assume "B \<noteq> A"
                    have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> F' - F\<close> \<open>B \<in> F' - F\<close> hG_NT by (by100 blast)+
                    from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>B \<noteq> A\<close>[symmetric]]
                    have "B \<inter> A \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
                    hence "x \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>x \<in> A\<close> \<open>x \<in> B\<close> by (by100 blast)
                    hence "x \<in> T" using hNT_endpoints \<open>B \<in> F' - F\<close> hG_NT by (by100 blast)
                    thus False using \<open>x \<notin> T\<close> by contradiction
                  qed
                qed
                have hthe: "(THE A. A \<in> F' - F \<and> x \<in> A \<and> x \<notin> T) = A"
                  by (rule the_equality) (use \<open>A \<in> F' - F\<close> \<open>x \<in> A\<close> hx_not_T hA_unique in blast)+
                have "r x = rr A x" unfolding r_def using False hthe by (by100 simp)
                moreover have "rr A x \<in> T"
                  using hrr \<open>A \<in> F' - F\<close> \<open>x \<in> A\<close>
                  unfolding top1_continuous_map_on_def by (by100 blast)
                ultimately have "r x \<in> T" by (by100 simp)
                thus ?thesis by (by100 blast)
              qed
            qed
            \<comment> \<open>r fixes ?YF.\<close>
            have hr_fixes: "\<forall>x \<in> ?YF. r x = x"
              unfolding r_def by (by100 simp)
            \<comment> \<open>r continuous: use pasting\\_lemma\\_two\\_closed on ?YF and \\<Union>(F'\\\\F).\<close>
            \<comment> \<open>r continuous via Theorem 18.3 (pasting lemma for two closed sets).\<close>
            have hTYFF_top: "is_topology_on ?YFF ?TYFF"
              by (rule subspace_topology_is_topology_on[OF hTY_top]) (use hYF_sub hF_NT hF'_NT h\<A> in blast)
            have hTYF_top: "is_topology_on ?YF ?TYF"
              by (rule subspace_topology_is_topology_on[OF hTY_top hYF_sub])
            \<comment> \<open>?YF closed in ?YFF.\<close>
            \<comment> \<open>?YF closed in Y (coherent topology: A \\<inter> ?YF closed in A for each arc).\<close>
            have hYF_closed_Y: "closedin_on Y TY ?YF"
            proof -
              have "?YF \<subseteq> Y" by (rule hYF_sub)
              from h\<A>_coh[rule_format, OF this]
              have "closedin_on Y TY ?YF \<longleftrightarrow>
                  (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> ?YF))" .
              moreover have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> ?YF)"
              proof (intro ballI)
                fix A assume "A \<in> \<A>"
                have hA_sub: "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                have hA_haus: "is_hausdorff_on A (subspace_topology Y TY A)"
                proof -
                  have "is_hausdorff_on Y TY"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  from Theorem_17_11[THEN conjunct2, THEN conjunct2, rule_format, OF conjI[OF this hA_sub]]
                  show ?thesis .
                qed
                show "closedin_on A (subspace_topology Y TY A) (A \<inter> ?YF)"
                proof (cases "A \<subseteq> T \<or> A \<in> F")
                  case True
                  hence "A \<inter> ?YF = A" by (by100 blast)
                  moreover have "closedin_on A (subspace_topology Y TY A) A"
                  proof -
                    have "is_topology_on A (subspace_topology Y TY A)"
                      by (rule subspace_topology_is_topology_on[OF hTY_top hA_sub])
                    from Theorem_17_1[OF this]
                    show ?thesis by (by100 blast)
                  qed
                  ultimately show ?thesis by (by100 simp)
                next
                  case False
                  \<comment> \<open>A is a non-tree arc not in F. A \\<inter> ?YF \\<subseteq> endpoints(A), which is finite.\<close>
                  have "A \<inter> ?YF \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                  proof
                    fix x assume "x \<in> A \<inter> ?YF"
                    hence "x \<in> A" "x \<in> T \<union> \<Union>F" by (by100 blast)+
                    show "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    proof (cases "x \<in> T")
                      case True
                      from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] False
                      have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                        by (by100 blast)
                      thus ?thesis using \<open>x \<in> A\<close> True by (by100 blast)
                    next
                      case xnT: False
                      hence "x \<in> \<Union>F" using \<open>x \<in> T \<union> \<Union>F\<close> by (by100 blast)
                      then obtain B where "B \<in> F" "x \<in> B" by (by100 blast)
                      have "B \<in> \<A>" using \<open>B \<in> F\<close> hF_NT by (by100 blast)
                      have "A \<noteq> B" using False \<open>B \<in> F\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> this]
                      have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                        by (by100 blast)
                      thus ?thesis using \<open>x \<in> A\<close> \<open>x \<in> B\<close> by (by100 blast)
                    qed
                  qed
                  moreover have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
                  proof -
                    have hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)"
                      using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    from hA_arc[unfolded top1_is_arc_on_def]
                    obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
                      by (by100 blast)
                    have "is_topology_on_strict Y TY"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have "is_hausdorff_on Y TY"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF \<open>is_topology_on_strict Y TY\<close>
                        \<open>is_hausdorff_on Y TY\<close> hA_sub hA_arc hh]
                    have "top1_arc_endpoints_on A (subspace_topology Y TY A) = {h 0, h 1}" .
                    thus ?thesis by (by100 simp)
                  qed
                  ultimately have "finite (A \<inter> ?YF)" using finite_subset by (by100 blast)
                  moreover have "A \<inter> ?YF \<subseteq> A" by (by100 blast)
                  ultimately show ?thesis
                    using Theorem_17_8[OF hA_haus] by (by100 blast)
                qed
              qed
              ultimately show ?thesis by (by100 blast)
            qed
            have hYF_closed: "closedin_on ?YFF ?TYFF ?YF"
            proof -
              have "?YF \<subseteq> ?YFF" by (by100 blast)
              from Theorem_17_2[OF hTY_top hYFF_sub', THEN iffD2]
              show ?thesis using hYF_closed_Y \<open>?YF \<subseteq> ?YFF\<close> by (by100 blast)
            qed
            \<comment> \<open>Each arc in F'\\\\F is closed in Y, hence in ?YFF. Finite union is closed.\<close>
            have hG_closed: "closedin_on ?YFF ?TYFF (\<Union>(F' - F))"
            proof -
              have "\<forall>A \<in> F' - F. closedin_on ?YFF ?TYFF A"
              proof (intro ballI)
                fix A assume "A \<in> F' - F"
                \<comment> \<open>A is closed in Y (compact subset of Hausdorff Y).\<close>
                have "A \<in> \<A>" using \<open>A \<in> F' - F\<close> hG_NT by (by100 blast)
                have hA_sub: "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                have "closedin_on Y TY A"
                proof -
                  have "A \<subseteq> Y" by (rule hA_sub)
                  from h\<A>_coh[rule_format, OF this]
                  have "closedin_on Y TY A \<longleftrightarrow>
                      (\<forall>B\<in>\<A>. closedin_on B (subspace_topology Y TY B) (B \<inter> A))" .
                  moreover have "\<forall>B\<in>\<A>. closedin_on B (subspace_topology Y TY B) (B \<inter> A)"
                  proof (intro ballI)
                    fix B assume "B \<in> \<A>"
                    show "closedin_on B (subspace_topology Y TY B) (B \<inter> A)"
                    proof (cases "B = A")
                      case True
                      have "is_topology_on B (subspace_topology Y TY B)"
                        by (rule subspace_topology_is_topology_on[OF hTY_top])
                           (use h\<A> \<open>B \<in> \<A>\<close> in blast)
                      have "B \<inter> A = B" using True by (by100 blast)
                      moreover from Theorem_17_1[OF \<open>is_topology_on B (subspace_topology Y TY B)\<close>]
                      have "closedin_on B (subspace_topology Y TY B) B" by (by100 blast)
                      ultimately show ?thesis by (by100 simp)
                    next
                      case False
                      from h\<A>_inter[rule_format, OF \<open>B \<in> \<A>\<close> \<open>A \<in> \<A>\<close> False]
                      have "finite (B \<inter> A)" by (by100 blast)
                      have "B \<inter> A \<subseteq> B" by (by100 blast)
                      have "is_hausdorff_on B (subspace_topology Y TY B)"
                      proof -
                        have "is_hausdorff_on Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have "B \<subseteq> Y" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                        from Theorem_17_11[THEN conjunct2, THEN conjunct2, rule_format,
                            OF conjI[OF \<open>is_hausdorff_on Y TY\<close> this]]
                        show ?thesis .
                      qed
                      from Theorem_17_8[OF this \<open>finite (B \<inter> A)\<close> \<open>B \<inter> A \<subseteq> B\<close>]
                      show ?thesis .
                    qed
                  qed
                  ultimately show ?thesis by (by100 blast)
                qed
                \<comment> \<open>A closed in Y \\<Longrightarrow> A closed in ?YFF.\<close>
                have "A \<subseteq> ?YFF" using \<open>A \<in> F' - F\<close> by (by100 blast)
                from Theorem_17_2[OF hTY_top hYFF_sub', THEN iffD2]
                show "closedin_on ?YFF ?TYFF A"
                  using \<open>closedin_on Y TY A\<close> \<open>A \<subseteq> ?YFF\<close> by (by100 blast)
              qed
              from closedin_Union_finite[OF hTYFF_top hG_finite this]
              show ?thesis .
            qed
            \<comment> \<open>?YF \\<union> \\<Union>(F'\\\\F) = ?YFF.\<close>
            have hcover: "?YF \<union> \<Union>(F' - F) = ?YFF" by (by100 blast)
            \<comment> \<open>r continuous on ?YF (identity).\<close>
            have hr_YF: "top1_continuous_map_on ?YF (subspace_topology ?YFF ?TYFF ?YF) ?YF ?TYF r"
            proof -
              have hsubsp: "subspace_topology ?YFF ?TYFF ?YF = ?TYF"
                by (rule subspace_topology_trans) blast
              show ?thesis unfolding hsubsp top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix x assume "x \<in> ?YF" thus "r x \<in> ?YF" using hr_fixes by (by100 simp)
              next
                fix V assume "V \<in> ?TYF"
                hence "V \<subseteq> ?YF" unfolding subspace_topology_def by (by100 blast)
                have hr_id: "\<And>x. x \<in> ?YF \<Longrightarrow> r x = x" using hr_fixes by (by100 blast)
                have "{x \<in> ?YF. r x \<in> V} = V"
                proof (rule set_eqI, rule iffI)
                  fix x assume "x \<in> {x \<in> ?YF. r x \<in> V}"
                  hence "x \<in> ?YF" "r x \<in> V" by (by100 blast)+
                  hence "x \<in> V" using hr_id by (by100 simp)
                  thus "x \<in> V" .
                next
                  fix x assume "x \<in> V"
                  hence "x \<in> ?YF" using \<open>V \<subseteq> ?YF\<close> by (by100 blast)
                  hence "r x = x" using hr_id by (by100 blast)
                  thus "x \<in> {x \<in> ?YF. r x \<in> V}" using \<open>x \<in> V\<close> \<open>x \<in> ?YF\<close> by (by100 simp)
                qed
                thus "{x \<in> ?YF. r x \<in> V} \<in> ?TYF" using \<open>V \<in> ?TYF\<close> by (by100 simp)
              qed
            qed
            \<comment> \<open>r continuous on \\<Union>(F'\\\\F).\<close>
            have hr_G: "top1_continuous_map_on (\<Union>(F' - F))
                (subspace_topology ?YFF ?TYFF (\<Union>(F' - F))) ?YF ?TYF r"
            proof -
              have hsubsp_G: "subspace_topology ?YFF ?TYFF (\<Union>(F' - F)) =
                  subspace_topology Y TY (\<Union>(F' - F))"
                by (rule subspace_topology_trans) blast
              have hG_sub_Y: "\<Union>(F' - F) \<subseteq> Y" using h\<A> hG_NT by (by100 blast)
              have hG_top: "is_topology_on (\<Union>(F' - F)) (subspace_topology Y TY (\<Union>(F' - F)))"
                by (rule subspace_topology_is_topology_on[OF hTY_top hG_sub_Y])
              \<comment> \<open>Key: r|A = rr(A) for each A \\<in> F'\\\\F (on ALL of A, including endpoints).\<close>
              have hr_eq_rr: "\<And>A x. A \<in> F' - F \<Longrightarrow> x \<in> A \<Longrightarrow> r x = rr A x"
              proof -
                fix A x assume "A \<in> F' - F" "x \<in> A"
                show "r x = rr A x"
                proof (cases "x \<in> ?YF")
                  case True
                  hence "x \<in> T"
                  proof -
                    from True have "x \<in> T \<or> x \<in> \<Union>F" by (by100 blast)
                    thus "x \<in> T"
                    proof
                      assume "x \<in> T" thus ?thesis .
                    next
                      assume "x \<in> \<Union>F"
                      then obtain B where "B \<in> F" "x \<in> B" by (by100 blast)
                      have "A \<noteq> B" using \<open>A \<in> F' - F\<close> \<open>B \<in> F\<close> by (by100 blast)
                      have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> F' - F\<close> hG_NT \<open>B \<in> F\<close> hF_NT
                        by (by100 blast)+
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
                      have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                        by (by100 blast)
                      hence "x \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                        using \<open>x \<in> A\<close> \<open>x \<in> B\<close> by (by100 blast)
                      thus "x \<in> T" using hNT_endpoints \<open>A \<in> F' - F\<close> hG_NT by (by100 blast)
                    qed
                  qed
                  hence "x \<in> A \<inter> T" using \<open>x \<in> A\<close> by (by100 blast)
                  from hrr[rule_format, OF \<open>A \<in> F' - F\<close>]
                  have "\<forall>x \<in> A \<inter> T. rr A x = x" by (by100 blast)
                  hence "rr A x = x" using \<open>x \<in> A \<inter> T\<close> by (by100 blast)
                  thus ?thesis using True unfolding r_def by (by100 simp)
                next
                  case False
                  have hA_unique: "(THE A'. A' \<in> F' - F \<and> x \<in> A' \<and> x \<notin> T) = A"
                  proof (rule the_equality)
                    show "A \<in> F' - F \<and> x \<in> A \<and> x \<notin> T"
                      using \<open>A \<in> F' - F\<close> \<open>x \<in> A\<close> False by (by100 blast)
                  next
                    fix A' assume "A' \<in> F' - F \<and> x \<in> A' \<and> x \<notin> T"
                    show "A' = A"
                    proof (rule ccontr)
                      assume "A' \<noteq> A"
                      have "A \<in> \<A>" "A' \<in> \<A>" using \<open>A \<in> F' - F\<close> \<open>A' \<in> F' - F \<and> _\<close> hG_NT
                        by (by100 blast)+
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
                      have "A' \<inter> A \<subseteq> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
                        by (by100 blast)
                      hence "x \<in> top1_arc_endpoints_on A' (subspace_topology Y TY A')"
                        using \<open>x \<in> A\<close> \<open>A' \<in> F' - F \<and> _\<close> by (by100 blast)
                      hence "x \<in> T" using hNT_endpoints \<open>A' \<in> F' - F \<and> _\<close> hG_NT by (by100 blast)
                      thus False using \<open>A' \<in> F' - F \<and> x \<in> A' \<and> x \<notin> T\<close> by (by100 blast)
                    qed
                  qed
                  thus ?thesis unfolding r_def using False hA_unique by (by100 simp)
                qed
              qed
              \<comment> \<open>Show continuity via open preimage characterization.
                 For each V open in ?YF: {x \\<in> \\<Union>(F'\\\\F). r x \\<in> V} is open in \\<Union>(F'\\\\F).
                 Proof: the complement is a finite union of Y-closed sets.\<close>
              show ?thesis unfolding hsubsp_G top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix x assume "x \<in> \<Union>(F' - F)"
                thus "r x \<in> ?YF" using hr_maps by (by100 blast)
              next
                fix V assume "V \<in> ?TYF"
                \<comment> \<open>Show {x \\<in> \\<Union>(F'\\\\F). r x \\<in> V} \\<in> subspace\\_topology Y TY (\\<Union>(F'\\\\F)).\<close>
                \<comment> \<open>Complement: D = {x \\<in> \\<Union>(F'\\\\F). r x \\<notin> V} = \\<Union>{A \\ rr(A)\\<inverse>(V) | A \\<in> F'\\\\F}.
                   Each A \\ rr(A)\\<inverse>(V) is closed in Y. Finite union: D closed in Y.
                   Hence {x \\<in> \\<Union>(F'\\\\F). r x \\<in> V} = (Y \\ D) \\<inter> \\<Union>(F'\\\\F) is open.\<close>
                let ?S = "{x \<in> \<Union>(F' - F). r x \<in> V}"
                \<comment> \<open>Each arc's complement is closed in Y.\<close>
                \<comment> \<open>For each A \\<in> F'\\\\F: {x \\<in> A. r x \\<notin> V} is closed in Y.
                   Proof: rr(A) continuous \\<Longrightarrow> preimage of complement is closed in A.
                   A closed in Y \\<Longrightarrow> closed-in-A is closed-in-Y.\<close>
                have hD_closed: "\<forall>A \<in> F' - F. closedin_on Y TY {x \<in> A. r x \<notin> V}"
                proof (intro ballI)
                  fix A assume "A \<in> F' - F"
                  have "A \<in> \<A>" using \<open>A \<in> F' - F\<close> hG_NT by (by100 blast)
                  have hA_sub_Y: "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  \<comment> \<open>A is closed in Y (from hG\\_closed\\_Y proof).\<close>
                  have "closedin_on Y TY A"
                  proof -
                    from hG_closed
                    have "closedin_on ?YFF ?TYFF (\<Union>(F' - F))" .
                    from Theorem_17_2[OF hTY_top hYFF_sub', THEN iffD1, OF this]
                    obtain D where "closedin_on Y TY D" "\<Union>(F' - F) = D \<inter> ?YFF" by (by100 blast)
                    have "A \<subseteq> \<Union>(F' - F)" using \<open>A \<in> F' - F\<close> by (by100 blast)
                    have "A \<subseteq> D" using \<open>A \<subseteq> \<Union>(F' - F)\<close> \<open>\<Union>(F' - F) = D \<inter> ?YFF\<close> by (by100 blast)
                    have "\<forall>B\<in>\<A>. closedin_on B (subspace_topology Y TY B) (B \<inter> A)"
                    proof (intro ballI)
                      fix B assume "B \<in> \<A>"
                      show "closedin_on B (subspace_topology Y TY B) (B \<inter> A)"
                      proof (cases "B = A")
                        case True
                        have "is_topology_on B (subspace_topology Y TY B)"
                          by (rule subspace_topology_is_topology_on[OF hTY_top])
                             (use h\<A> \<open>B \<in> \<A>\<close> in blast)
                        have "B \<inter> A = B" using True by (by100 blast)
                        from Theorem_17_1[OF \<open>is_topology_on B _\<close>]
                        have "closedin_on B (subspace_topology Y TY B) B" by (by100 blast)
                        thus ?thesis using \<open>B \<inter> A = B\<close> by (by100 simp)
                      next
                        case False
                        from h\<A>_inter[rule_format, OF \<open>B \<in> \<A>\<close> \<open>A \<in> \<A>\<close> False]
                        have "finite (B \<inter> A)" by (by100 blast)
                        have "B \<inter> A \<subseteq> B" by (by100 blast)
                        have "is_hausdorff_on B (subspace_topology Y TY B)"
                        proof -
                          have "is_hausdorff_on Y TY"
                            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                          have "B \<subseteq> Y" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                          from Theorem_17_11[THEN conjunct2, THEN conjunct2, rule_format,
                              OF conjI[OF \<open>is_hausdorff_on Y TY\<close> this]]
                          show ?thesis .
                        qed
                        from Theorem_17_8[OF this \<open>finite (B \<inter> A)\<close> \<open>B \<inter> A \<subseteq> B\<close>]
                        show ?thesis .
                      qed
                    qed
                    from h\<A>_coh[rule_format, OF hA_sub_Y, THEN iffD2, OF this]
                    show "closedin_on Y TY A" .
                  qed
                  \<comment> \<open>{x \\<in> A. r x \\<notin> V} = {x \\<in> A. rr A x \\<notin> V} (since r|A = rr(A)).\<close>
                  have hset_eq: "{x \<in> A. r x \<notin> V} = {x \<in> A. rr A x \<notin> V}"
                  proof (rule set_eqI, rule iffI)
                    fix x assume "x \<in> {x \<in> A. r x \<notin> V}"
                    hence "x \<in> A" "r x \<notin> V" by (by100 blast)+
                    have "r x = rr A x" by (rule hr_eq_rr[OF \<open>A \<in> F' - F\<close> \<open>x \<in> A\<close>])
                    hence "rr A x \<notin> V" using \<open>r x \<notin> V\<close> by (by100 simp)
                    thus "x \<in> {x \<in> A. rr A x \<notin> V}" using \<open>x \<in> A\<close> by (by100 blast)
                  next
                    fix x assume "x \<in> {x \<in> A. rr A x \<notin> V}"
                    hence "x \<in> A" "rr A x \<notin> V" by (by100 blast)+
                    have "r x = rr A x" by (rule hr_eq_rr[OF \<open>A \<in> F' - F\<close> \<open>x \<in> A\<close>])
                    hence "r x \<notin> V" using \<open>rr A x \<notin> V\<close> by (by100 simp)
                    thus "x \<in> {x \<in> A. r x \<notin> V}" using \<open>x \<in> A\<close> by (by100 blast)
                  qed
                  \<comment> \<open>{x \\<in> A. rr A x \\<notin> V} is closed in A (complement of continuous preimage of open).\<close>
                  have "closedin_on A (subspace_topology Y TY A) {x \<in> A. rr A x \<notin> V}"
                  proof -
                    \<comment> \<open>rr(A) continuous from A to T.\<close>
                    from hrr[rule_format, OF \<open>A \<in> F' - F\<close>]
                    have hrr_cont: "top1_continuous_map_on A (subspace_topology Y TY A) T
                        (subspace_topology Y TY T) (rr A)" by (by100 blast)
                    have hrr_maps: "\<forall>x\<in>A. rr A x \<in> T"
                      using hrr_cont unfolding top1_continuous_map_on_def by (by100 blast)
                    \<comment> \<open>V open in ?YF. V \\<inter> T open in T (subspace from Y).\<close>
                    have "V \<in> ?TYF" by (rule \<open>V \<in> ?TYF\<close>)
                    from \<open>V \<in> ?TYF\<close>[unfolded subspace_topology_def]
                    obtain W where "W \<in> TY" "V = W \<inter> ?YF" by (by100 blast)
                    have "W \<inter> T \<in> subspace_topology Y TY T"
                      unfolding subspace_topology_def using \<open>W \<in> TY\<close> by (by100 blast)
                    \<comment> \<open>Preimage of W \\<inter> T under rr(A) is open in A.\<close>
                    have "{x \<in> A. rr A x \<in> W \<inter> T} \<in> subspace_topology Y TY A"
                      using hrr_cont \<open>W \<inter> T \<in> subspace_topology Y TY T\<close>
                      unfolding top1_continuous_map_on_def by (by100 blast)
                    \<comment> \<open>{x \\<in> A. rr A x \\<in> V} = {x \\<in> A. rr A x \\<in> W \\<inter> T} (since rr maps into T).\<close>
                    have "{x \<in> A. rr A x \<in> V} = {x \<in> A. rr A x \<in> W \<inter> T}"
                    proof (rule set_eqI, rule iffI)
                      fix x assume "x \<in> {x \<in> A. rr A x \<in> V}"
                      hence "x \<in> A" "rr A x \<in> V" by (by100 blast)+
                      hence "rr A x \<in> W" "rr A x \<in> ?YF" using \<open>V = W \<inter> ?YF\<close> by (by100 blast)+
                      hence "rr A x \<in> T" using hrr_maps \<open>x \<in> A\<close> by (by100 blast)
                      thus "x \<in> {x \<in> A. rr A x \<in> W \<inter> T}" using \<open>x \<in> A\<close> \<open>rr A x \<in> W\<close> by (by100 blast)
                    next
                      fix x assume "x \<in> {x \<in> A. rr A x \<in> W \<inter> T}"
                      hence "x \<in> A" "rr A x \<in> W" "rr A x \<in> T" by (by100 blast)+
                      hence "rr A x \<in> V" using \<open>V = W \<inter> ?YF\<close> by (by100 blast)
                      thus "x \<in> {x \<in> A. rr A x \<in> V}" using \<open>x \<in> A\<close> by (by100 blast)
                    qed
                    \<comment> \<open>Complement: {x \\<in> A. rr A x \\<notin> V} = A - {x \\<in> A. rr A x \\<in> V}.\<close>
                    have "{x \<in> A. rr A x \<notin> V} = A - {x \<in> A. rr A x \<in> V}" by (by100 blast)
                    also have "\<dots> = A - {x \<in> A. rr A x \<in> W \<inter> T}"
                      using \<open>{x \<in> A. rr A x \<in> V} = {x \<in> A. rr A x \<in> W \<inter> T}\<close> by (by100 simp)
                    finally have hD_eq: "{x \<in> A. rr A x \<notin> V} = A - {x \<in> A. rr A x \<in> W \<inter> T}" .
                    \<comment> \<open>{x \\<in> A. rr A x \\<in> W \\<inter> T} is open in A, so its complement is closed.\<close>
                    have "{x \<in> A. rr A x \<in> W \<inter> T} \<subseteq> A" by (by100 blast)
                    have "closedin_on A (subspace_topology Y TY A) (A - {x \<in> A. rr A x \<in> W \<inter> T})"
                      unfolding closedin_on_def
                    proof (intro conjI)
                      show "A - {x \<in> A. rr A x \<in> W \<inter> T} \<subseteq> A" by (by100 blast)
                      show "A - (A - {x \<in> A. rr A x \<in> W \<inter> T}) \<in> subspace_topology Y TY A"
                      proof -
                        have "A - (A - {x \<in> A. rr A x \<in> W \<inter> T}) = {x \<in> A. rr A x \<in> W \<inter> T}"
                          by (by100 blast)
                        thus ?thesis using \<open>{x \<in> A. rr A x \<in> W \<inter> T} \<in> subspace_topology Y TY A\<close>
                          by (by100 simp)
                      qed
                    qed
                    thus ?thesis using hD_eq by (by100 simp)
                  qed
                  \<comment> \<open>Closed in A + A closed in Y \\<Longrightarrow> closed in Y.\<close>
                  from Theorem_17_2[OF hTY_top hA_sub_Y, THEN iffD1, OF this]
                  obtain C where "closedin_on Y TY C" "{x \<in> A. rr A x \<notin> V} = C \<inter> A"
                    by (by100 blast)
                  have "{x \<in> A. rr A x \<notin> V} \<subseteq> A" by (by100 blast)
                  have "closedin_on Y TY {x \<in> A. rr A x \<notin> V}"
                  proof -
                    have "{x \<in> A. rr A x \<notin> V} = C \<inter> A" by (rule \<open>{x \<in> A. rr A x \<notin> V} = C \<inter> A\<close>)
                    moreover have "closedin_on Y TY (C \<inter> A)"
                      by (rule closedin_inter2[OF hTY_top \<open>closedin_on Y TY C\<close> \<open>closedin_on Y TY A\<close>])
                    ultimately show ?thesis by (by100 simp)
                  qed
                  thus "closedin_on Y TY {x \<in> A. r x \<notin> V}" using hset_eq by (by100 simp)
                qed
                \<comment> \<open>Finite union of Y-closed sets is Y-closed.\<close>
                have "closedin_on Y TY (\<Union>A \<in> F' - F. {x \<in> A. r x \<notin> V})"
                proof -
                  have "finite ((\<lambda>A. {x \<in> A. r x \<notin> V}) ` (F' - F))"
                    using hG_finite by (by100 simp)
                  moreover have "\<forall>S \<in> (\<lambda>A. {x \<in> A. r x \<notin> V}) ` (F' - F). closedin_on Y TY S"
                    using hD_closed by (by100 blast)
                  ultimately show ?thesis
                    using closedin_Union_finite[OF hTY_top] by (by100 blast)
                qed
                moreover have "\<Union>(F' - F) - ?S = (\<Union>A \<in> F' - F. {x \<in> A. r x \<notin> V})"
                  by (by100 blast)
                ultimately have "closedin_on Y TY (\<Union>(F' - F) - ?S)" by (by100 simp)
                hence "?S = (Y - (\<Union>(F' - F) - ?S)) \<inter> \<Union>(F' - F)"
                  using hG_sub_Y by (by100 blast)
                moreover have "(Y - (\<Union>(F' - F) - ?S)) \<in> TY"
                  using \<open>closedin_on Y TY (\<Union>(F' - F) - ?S)\<close> unfolding closedin_on_def
                  by (by100 blast)
                ultimately show "?S \<in> subspace_topology Y TY (\<Union>(F' - F))"
                  unfolding subspace_topology_def by (by100 blast)
              qed
            qed
            \<comment> \<open>Apply pasting\\_lemma\\_two\\_closed.\<close>
            have hr_maps': "\<forall>x \<in> ?YFF. r x \<in> ?YF" using hr_maps by (by100 blast)
            have hr_cont: "top1_continuous_map_on ?YFF ?TYFF ?YF ?TYF r"
              by (rule pasting_lemma_two_closed[OF hTYFF_top hTYF_top hYF_closed hG_closed
                  hcover hr_maps' hr_YF hr_G])
            have hYF_sub_FF': "?YF \<subseteq> ?YFF" by (by100 blast)
            have hsubsp_eq': "subspace_topology ?YFF ?TYFF ?YF = ?TYF"
              by (rule subspace_topology_trans) (use hYF_sub_FF' in blast)
            show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
              using hYF_sub_FF' hr_cont[folded hsubsp_eq'] hr_fixes by (by100 blast)
          qed
          \<comment> \<open>By Lemma 55.1: f1 \\<sim> f2 in T \\<union> \\<Union>F.\<close>
          have hYF_sub_FF: "?YF \<subseteq> ?YFF" by (by100 blast)
          have hYFF_sub: "?YFF \<subseteq> Y" using hYF_sub hF_NT hF'_NT h\<A> by (by100 blast)
          have hsubsp_eq: "subspace_topology ?YFF ?TYFF ?YF = ?TYF"
            by (rule subspace_topology_trans) (use hYF_sub_FF in blast)
          from Lemma_55_1_retract_injective[OF hretract hy0_YF
              hf1_loop[folded hsubsp_eq] hf2_loop[folded hsubsp_eq] hhtpy_FF]
          have "top1_path_homotopic_on ?YF ?TYF y0 y0 f1 f2"
            using hsubsp_eq by (by100 simp)
          \<comment> \<open>Hence c1 = c2: f1 ~ f2 in ?YF \\<Longrightarrow> loop\\_equiv f1 f2 \\<Longrightarrow> c1 = c2.\<close>
          have "top1_loop_equiv_on ?YF ?TYF y0 f1 f2"
            unfolding top1_loop_equiv_on_def
            using hf1_loop hf2_loop \<open>top1_path_homotopic_on ?YF ?TYF y0 y0 f1 f2\<close>
            by (by100 blast)
          show "c1 = c2"
          proof -
            have hTYF_top: "is_topology_on ?YF ?TYF"
              by (rule subspace_topology_is_topology_on[OF hTY_top hYF_sub])
            have "\<forall>g. top1_loop_equiv_on ?YF ?TYF y0 f1 g \<longleftrightarrow>
                top1_loop_equiv_on ?YF ?TYF y0 f2 g"
            proof (intro allI iffI)
              fix g assume "top1_loop_equiv_on ?YF ?TYF y0 f1 g"
              from top1_loop_equiv_on_trans[OF hTYF_top
                  top1_loop_equiv_on_sym[OF \<open>top1_loop_equiv_on ?YF ?TYF y0 f1 f2\<close>] this]
              show "top1_loop_equiv_on ?YF ?TYF y0 f2 g" .
            next
              fix g assume "top1_loop_equiv_on ?YF ?TYF y0 f2 g"
              from top1_loop_equiv_on_trans[OF hTYF_top
                  \<open>top1_loop_equiv_on ?YF ?TYF y0 f1 f2\<close> this]
              show "top1_loop_equiv_on ?YF ?TYF y0 f1 g" .
            qed
            thus "c1 = c2" using hc1_eq hc2_eq by (by100 blast)
          qed
        qed
      qed
      \<comment> \<open>Step 4: For finite F \\<subseteq> ?NT, T \\<union> (\\<Union>F) is a subgraph with free \\<pi>\\_1.
         This follows from graph\\_pi1\\_free\\_weak\\_finite.\<close>
      have hfinite_subgraph_free: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?NT \<Longrightarrow>
          \<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
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
        show "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
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
          \<comment> \<open>The tree T in ?Y' has the same topology: subspace\\_topology ?Y' ?TY' T = subspace\\_topology Y TY T
             (by subspace\\_topology\\_trans since T \\<subseteq> ?Y').\<close>
          have hT_tree_Y': "top1_is_tree_on T (subspace_topology ?Y' (subspace_topology Y TY ?Y') T)"
          proof -
            have "subspace_topology ?Y' (subspace_topology Y TY ?Y') T =
                subspace_topology Y TY T"
              by (rule subspace_topology_trans) (by100 blast)
            thus ?thesis using hT_tree by (by100 simp)
          qed
          \<comment> \<open>Arc topology in ?Y' = arc topology in Y.\<close>
          have h\<B>_arcs_Y': "\<forall>A\<in>?\<B>. A \<subseteq> ?Y' \<and>
              top1_is_arc_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
          proof (intro ballI conjI)
            fix A assume "A \<in> ?\<B>"
            show "A \<subseteq> ?Y'" using \<open>A \<in> ?\<B>\<close> by (by100 blast)
            have "A \<in> \<A>" using \<open>A \<in> ?\<B>\<close> by (by100 blast)
            have "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            moreover have "subspace_topology ?Y' (subspace_topology Y TY ?Y') A =
                subspace_topology Y TY A"
              by (rule subspace_topology_trans) (use \<open>A \<in> ?\<B>\<close> in blast)
            ultimately show "top1_is_arc_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
              by (by100 simp)
          qed
          \<comment> \<open>Coherent topology for ?Y'.\<close>
          have h\<B>_eq': "?Y' = \<Union>?\<B>"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> ?Y'"
            thus "x \<in> \<Union>?\<B>"
            proof
              assume "x \<in> T"
              then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" using hT_coverage by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              assume "x \<in> \<Union>F0'"
              then obtain A where "A \<in> F0'" "x \<in> A" by (by100 blast)
              have "A \<in> \<A>" using hF0'_NT \<open>A \<in> F0'\<close> by (by100 blast)
              thus ?thesis using \<open>x \<in> A\<close> \<open>A \<in> F0'\<close> by (by100 blast)
            qed
          next
            fix x assume "x \<in> \<Union>?\<B>" thus "x \<in> ?Y'" by (by100 blast)
          qed
          have h\<B>_coh_base: "\<forall>C. C \<subseteq> ?Y' \<longrightarrow>
              (closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
               (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
            by (rule subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh _ h\<B>_eq'])
               (by100 blast)
          have h\<B>_coh_Y': "\<forall>C. C \<subseteq> ?Y' \<longrightarrow>
              (closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
               (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A) (A \<inter> C)))"
          proof (intro allI impI)
            fix C assume "C \<subseteq> ?Y'"
            from h\<B>_coh_base[rule_format, OF this]
            have "closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
                (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology Y TY A) (A \<inter> C))" .
            moreover have "\<forall>A\<in>?\<B>. subspace_topology ?Y' (subspace_topology Y TY ?Y') A =
                subspace_topology Y TY A"
              by (intro ballI, rule subspace_topology_trans) blast
            ultimately show "closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
                (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A) (A \<inter> C))"
              by (by100 simp)
          qed
          \<comment> \<open>Intersection conditions.\<close>
          have h\<B>_inter_Y': "\<forall>A\<in>?\<B>. \<forall>B\<in>?\<B>. A \<noteq> B \<longrightarrow>
              A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?Y' (subspace_topology Y TY ?Y') B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
          proof (intro ballI impI)
            fix A B assume "A \<in> ?\<B>" "B \<in> ?\<B>" "A \<noteq> B"
            have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> ?\<B>\<close> \<open>B \<in> ?\<B>\<close> by (by100 blast)+
            from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
            have hinter: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
              \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
              \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
            have "subspace_topology ?Y' (subspace_topology Y TY ?Y') A = subspace_topology Y TY A"
              by (rule subspace_topology_trans) (use \<open>A \<in> ?\<B>\<close> in blast)
            have "subspace_topology ?Y' (subspace_topology Y TY ?Y') B = subspace_topology Y TY B"
              by (rule subspace_topology_trans) (use \<open>B \<in> ?\<B>\<close> in blast)
            show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)
              \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?Y' (subspace_topology Y TY ?Y') B)
              \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
              using hinter \<open>subspace_topology ?Y' _ A = _\<close> \<open>subspace_topology ?Y' _ B = _\<close>
              by (by100 simp)
          qed
          \<comment> \<open>Subgraph/endpoint conditions.\<close>
          have hT_subgraph_Y': "\<forall>A\<in>?\<B>. A \<subseteq> T \<or>
              A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
          proof (intro ballI)
            fix A assume "A \<in> ?\<B>"
            have "A \<in> \<A>" using \<open>A \<in> ?\<B>\<close> by (by100 blast)
            from hT_subgraph[rule_format, OF this]
            have "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" .
            moreover have "subspace_topology ?Y' (subspace_topology Y TY ?Y') A =
                subspace_topology Y TY A"
              by (rule subspace_topology_trans) (use \<open>A \<in> ?\<B>\<close> in blast)
            ultimately show "A \<subseteq> T \<or>
                A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
              by (by100 simp)
          qed
          \<comment> \<open>Apply graph\\_pi1\\_free\\_weak\\_finite. All preconditions verified above.\<close>
          \<comment> \<open>Rewrite all preconditions to use the graph topology.\<close>
          have "top1_is_graph_on ?Y' (subspace_topology Y TY ?Y')" by (rule hY'_graph)
          have "top1_connected_on ?Y' (subspace_topology Y TY ?Y')" by (rule hY'_conn)
          \<comment> \<open>Endpoint condition for non-tree arcs of Y'.\<close>
          have hNT_ep_Y': "\<forall>A\<in>{A \<in> ?\<B>. \<not> A \<subseteq> T}.
              \<forall>e\<in>top1_arc_endpoints_on A
                  (subspace_topology ?Y' (subspace_topology Y TY ?Y') A). e \<in> T"
          proof (intro ballI)
            fix A e assume "A \<in> {A \<in> ?\<B>. \<not> A \<subseteq> T}"
                and "e \<in> top1_arc_endpoints_on A
                    (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
            have "A \<in> ?NT" using \<open>A \<in> _\<close> hNT_Y' by (by100 blast)
            have "subspace_topology ?Y' (subspace_topology Y TY ?Y') A =
                subspace_topology Y TY A"
              by (rule subspace_topology_trans) (use \<open>A \<in> {A \<in> ?\<B>. _}\<close> in blast)
            hence "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using \<open>e \<in> _\<close> by (by100 simp)
            thus "e \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> by (by100 blast)
          qed
          have hcard_NT: "card {A \<in> ?\<B>. \<not> A \<subseteq> T} \<le> card F0'"
            using hNT_Y' by (by100 simp)
          have hfin_NT: "finite {A \<in> ?\<B>. \<not> A \<subseteq> T}"
            using hNT_Y' hF0'fin by (by100 simp)
          have hT_sub_Y': "T \<subseteq> ?Y'" by (by100 blast)
          show ?thesis
          proof (rule graph_pi1_free_weak_apply[where \<A>_sub="?\<B>" and T_sub=T])
            show "top1_is_graph_on ?Y' (subspace_topology Y TY ?Y')" by (rule hY'_graph)
            show "top1_connected_on ?Y' (subspace_topology Y TY ?Y')" by (rule hY'_conn)
            show "y0 \<in> ?Y'" by (rule hy0_Y')
            show "finite {A \<in> ?\<B>. \<not> A \<subseteq> T}" by (rule hfin_NT)
            show "\<forall>A\<in>?\<B>. A \<subseteq> ?Y' \<and> top1_is_arc_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
              by (rule h\<B>_arcs_Y')
            show "\<Union>?\<B> = ?Y'" using h\<B>_eq' by (by100 simp)
            show "\<forall>A\<in>?\<B>. \<forall>B\<in>?\<B>. A \<noteq> B \<longrightarrow>
                A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A) \<and>
                A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?Y' (subspace_topology Y TY ?Y') B) \<and>
                finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
              by (rule h\<B>_inter_Y')
            show "\<forall>C. C \<subseteq> ?Y' \<longrightarrow>
                (closedin_on ?Y' (subspace_topology Y TY ?Y') C \<longleftrightarrow>
                 (\<forall>A\<in>?\<B>. closedin_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A) (A \<inter> C)))"
              by (rule h\<B>_coh_Y')
            show "top1_is_tree_on T (subspace_topology ?Y' (subspace_topology Y TY ?Y') T)"
              by (rule hT_tree_Y')
            show "T \<subseteq> ?Y'" by (rule hT_sub_Y')
            show "\<forall>A\<in>?\<B>. A \<subseteq> T \<or>
                A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A)"
              by (rule hT_subgraph_Y')
            show "y0 \<in> T" by (rule hT_x0)
            show "\<forall>A\<in>{A \<in> ?\<B>. \<not> A \<subseteq> T}.
                \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?Y' (subspace_topology Y TY ?Y') A). e \<in> T"
              by (rule hNT_ep_Y')
          qed
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
      \<comment> \<open>Inclusion injectivity: same as Theorem 71.3 (free\\_group\\_hom\\_subset\\_injective).
         Note: retraction approach does NOT work for arcs with 2 distinct T-endpoints.\<close>
      \<comment> \<open>Condition 4 (generated): every loop lies in some T\\<union>\\<Union>F (hloop\\_in\\_finite).
         In T\\<union>\\<Union>F, \\<pi>\\_1 is free, hence generated by the g\\_A for A \\<in> F.
         Under inclusion, these map to the g\\_A in \\<pi>\\_1(Y).\<close>
      \<comment> \<open>Condition 5 (no word = id): word uses finitely many generators from F.
         Word non-trivial in T\\<union>\\<Union>F (freeness). By hincl\\_inj:
         inclusion injective. Hence word non-trivial in Y.\<close>
      \<comment> \<open>Assembly: define generators and verify free\\_group\\_full\\_on.
         Same as Theorem 71.3 but with arc-based generators instead of S1 loops.\<close>
      \<comment> \<open>For each non-tree arc A, define the generator loop:
         g\\_A = (path in T from y0 to endpoint a) * (arc path from a to b) * (rev path from y0 to b).
         This requires: (1) paths from y0 to each endpoint exist (tree path-connected),
         (2) arc traversal path exists (homeomorphism I \\<rightarrow> A).
         \\<iota>(A) = [g\\_A] in \\<pi>\\_1(Y, y0).\<close>
      \<comment> \<open>Then verify 5 conditions of free\\_group\\_full\\_on:
         1. Group: fundamental\\_group\\_is\\_group \\<checkmark>
         2. \\<iota>(A) \\<in> carrier: g\\_A is a loop \\<checkmark>
         3. inj\\_on: from hincl\\_inj
         4. Generated: from hloop\\_in\\_finite + hfinite\\_subgraph\\_free
         5. No word = id: from hincl\\_inj + hfinite\\_subgraph\\_free\<close>
      show ?thesis
      proof -
        \<comment> \<open>Generator construction: for each A \\<in> ?NT, define the generator loop g\\_A.
           g\\_A = tree\\_path(y0, a) * arc\\_path(a, b) * rev(tree\\_path(y0, b))
           where a, b are the endpoints of A.\<close>
        have hT_pc: "top1_path_connected_on T (subspace_topology Y TY T)"
        proof -
          from hT_tree[unfolded top1_is_tree_on_def top1_simply_connected_on_def]
          show ?thesis by (by100 blast)
        qed
        have hTY_top: "is_topology_on Y TY"
          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>For each A \\<in> ?NT, get homeomorphism h\\_A and endpoints.\<close>
        have "\<forall>A \<in> ?NT. \<exists>h. top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
          using h\<A> unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Choose the generator map: for each A \\<in> ?NT, construct the specific generator loop.
           The generator loop g\\_A = \\<gamma>\\_a * (h * rev(\\<gamma>\\_b)) depends on choices of h, \\<gamma>\\_a, \\<gamma>\\_b,
           but the HOMOTOPY CLASS [g\\_A] is canonical (independent of choices, since T is SC).
           We construct a specific representative and take its homotopy class.\<close>
        have hgen_exists_full: "\<forall>A \<in> ?NT. \<exists>gloop. top1_is_loop_on Y TY y0 gloop
            \<and> gloop ` top1_unit_interval \<subseteq> T \<union> A
            \<and> (\<exists>h_arc \<gamma>a' \<gamma>b'. gloop = top1_path_product \<gamma>a' (top1_path_product h_arc (top1_path_reverse \<gamma>b'))
                \<and> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology Y TY A) h_arc
                \<and> \<gamma>a' ` I_set \<subseteq> T \<and> \<gamma>b' ` I_set \<subseteq> T)"
        proof (intro ballI)
          fix A assume "A \<in> ?NT"
          hence "A \<in> \<A>" by (by100 blast)
          have hA_sub: "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have hA_arc: "top1_is_arc_on A (subspace_topology Y TY A)"
            using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          from hA_arc[unfolded top1_is_arc_on_def]
          obtain h where hh: "top1_homeomorphism_on I_set I_top A (subspace_topology Y TY A) h"
            by (by100 blast)
          \<comment> \<open>Endpoints a = h(0), b = h(1). Both in T.\<close>
          have hstrict: "is_topology_on_strict Y TY"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          have hhaus: "is_hausdorff_on Y TY"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          from arc_endpoints_are_boundary[OF hstrict hhaus hA_sub hA_arc hh]
          have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {h 0, h 1}" .
          have ha_T: "h 0 \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> hep by (by100 blast)
          have hb_T: "h 1 \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> hep by (by100 blast)
          \<comment> \<open>Tree paths from y0 to endpoints.\<close>
          from hT_pc[unfolded top1_path_connected_on_def] hT_x0 ha_T
          obtain \<gamma>a where h\<gamma>a: "top1_is_path_on T (subspace_topology Y TY T) y0 (h 0) \<gamma>a"
            by (by100 blast)
          from hT_pc[unfolded top1_path_connected_on_def] hT_x0 hb_T
          obtain \<gamma>b where h\<gamma>b: "top1_is_path_on T (subspace_topology Y TY T) y0 (h 1) \<gamma>b"
            by (by100 blast)
          \<comment> \<open>Arc path: h as a path from h(0) to h(1).\<close>
          have hh_path: "top1_is_path_on A (subspace_topology Y TY A) (h 0) (h 1) h"
          proof -
            have hh_cont: "top1_continuous_map_on I_set I_top A (subspace_topology Y TY A) h"
              using hh unfolding top1_homeomorphism_on_def by (by100 blast)
            have "h 0 \<in> A" "h 1 \<in> A"
            proof -
              have "(0::real) \<in> I_set" "(1::real) \<in> I_set"
                unfolding top1_unit_interval_def by (by100 simp)+
              thus "h 0 \<in> A" "h 1 \<in> A"
                using hh_cont unfolding top1_continuous_map_on_def by (by100 blast)+
            qed
            thus ?thesis using hh_cont
              unfolding top1_is_path_on_def by (by100 blast)
          qed
          \<comment> \<open>Lift all paths to Y via inclusion.\<close>
          \<comment> \<open>Lift paths from subspaces to Y. A path in S \\<subseteq> Y lifts to Y
             because the inclusion is continuous (Theorem\\_18\\_2(2)).\<close>
          have h\<gamma>a_Y: "top1_is_path_on Y TY y0 (h 0) \<gamma>a"
          proof -
            have "\<gamma>a ` I_set \<subseteq> T"
              using h\<gamma>a unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            hence "\<gamma>a ` I_set \<subseteq> Y" using hT_sub by (by100 blast)
            have "top1_continuous_map_on I_set I_top T (subspace_topology Y TY T) \<gamma>a"
              using h\<gamma>a unfolding top1_is_path_on_def by (by100 blast)
            have "top1_continuous_map_on I_set I_top Y TY (id \<circ> \<gamma>a)"
              by (rule top1_continuous_map_on_comp[OF \<open>top1_continuous_map_on I_set I_top T _ \<gamma>a\<close>
                  Theorem_18_2(2)[OF hTY_top hTY_top hTY_top, rule_format, OF hT_sub]])
            hence "top1_continuous_map_on I_set I_top Y TY \<gamma>a" by (by100 simp)
            moreover have "\<gamma>a 0 = y0" "\<gamma>a 1 = h 0"
              using h\<gamma>a unfolding top1_is_path_on_def by (by100 blast)+
            ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
          qed
          have h\<gamma>b_Y: "top1_is_path_on Y TY y0 (h 1) \<gamma>b"
          proof -
            have "top1_continuous_map_on I_set I_top T (subspace_topology Y TY T) \<gamma>b"
              using h\<gamma>b unfolding top1_is_path_on_def by (by100 blast)
            have "top1_continuous_map_on I_set I_top Y TY (id \<circ> \<gamma>b)"
              by (rule top1_continuous_map_on_comp[OF \<open>top1_continuous_map_on I_set I_top T _ \<gamma>b\<close>
                  Theorem_18_2(2)[OF hTY_top hTY_top hTY_top, rule_format, OF hT_sub]])
            hence "top1_continuous_map_on I_set I_top Y TY \<gamma>b" by (by100 simp)
            moreover have "\<gamma>b 0 = y0" "\<gamma>b 1 = h 1"
              using h\<gamma>b unfolding top1_is_path_on_def by (by100 blast)+
            ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
          qed
          have hh_Y: "top1_is_path_on Y TY (h 0) (h 1) h"
          proof -
            have "top1_continuous_map_on I_set I_top A (subspace_topology Y TY A) h"
              using hh unfolding top1_homeomorphism_on_def by (by100 blast)
            have "top1_continuous_map_on I_set I_top Y TY (id \<circ> h)"
              by (rule top1_continuous_map_on_comp[OF \<open>top1_continuous_map_on I_set I_top A _ h\<close>
                  Theorem_18_2(2)[OF hTY_top hTY_top hTY_top, rule_format, OF hA_sub]])
            hence "top1_continuous_map_on I_set I_top Y TY h" by (by100 simp)
            moreover have "h 0 \<in> Y" "h 1 \<in> Y" using ha_T hb_T hT_sub by (by100 blast)+
            ultimately show ?thesis
              using hh_path unfolding top1_is_path_on_def by (by100 blast)
          qed
          \<comment> \<open>Generator loop: g\\_A = \\<gamma>\\_a * (h * rev(\\<gamma>\\_b)).\<close>
          let ?rev_\<gamma>b = "top1_path_reverse \<gamma>b"
          have hrev_Y: "top1_is_path_on Y TY (h 1) y0 ?rev_\<gamma>b"
            by (rule top1_path_reverse_is_path[OF h\<gamma>b_Y])
          let ?inner = "top1_path_product h ?rev_\<gamma>b"
          have hinner_Y: "top1_is_path_on Y TY (h 0) y0 ?inner"
            by (rule top1_path_product_is_path[OF hTY_top hh_Y hrev_Y])
          let ?gen_loop = "top1_path_product \<gamma>a ?inner"
          have hgen_Y: "top1_is_path_on Y TY y0 y0 ?gen_loop"
            by (rule top1_path_product_is_path[OF hTY_top h\<gamma>a_Y hinner_Y])
          have hgen_loop: "top1_is_loop_on Y TY y0 ?gen_loop"
            using hgen_Y unfolding top1_is_loop_on_def by (by100 blast)
          \<comment> \<open>Image containment: gen\\_loop maps into T \\<union> A.\<close>
          have himg: "?gen_loop ` top1_unit_interval \<subseteq> T \<union> A"
          proof
            fix x assume "x \<in> ?gen_loop ` top1_unit_interval"
            then obtain t where "t \<in> top1_unit_interval" "x = ?gen_loop t" by (by100 blast)
            have ht_I: "t \<in> I_set" using \<open>t \<in> top1_unit_interval\<close> by (by100 simp)
            show "x \<in> T \<union> A"
            proof (cases "t \<le> 1/2")
              case True \<comment> \<open>First half: \\<gamma>\\_a(2t) \\<in> T.\<close>
              hence "?gen_loop t = \<gamma>a (2 * t)"
                unfolding top1_path_product_def by (by100 simp)
              moreover have "2 * t \<in> I_set"
                using True ht_I unfolding top1_unit_interval_def by (by100 simp)
              hence "\<gamma>a (2 * t) \<in> T"
                using h\<gamma>a unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              ultimately have "x \<in> T" using \<open>x = ?gen_loop t\<close> by (by100 simp)
              thus ?thesis by (by100 blast)
            next
              case False \<comment> \<open>Second half: inner product.\<close>
              hence "?gen_loop t = ?inner (2 * t - 1)"
                unfolding top1_path_product_def by (by100 simp)
              have ht2: "2 * t - 1 \<in> I_set"
                using False ht_I unfolding top1_unit_interval_def by (by100 simp)
              show ?thesis
              proof (cases "2 * t - 1 \<le> 1/2")
                case True \<comment> \<open>h(2(2t-1)) \\<in> A.\<close>
                hence "?inner (2 * t - 1) = h (2 * (2 * t - 1))"
                  unfolding top1_path_product_def by (by100 simp)
                moreover have "2 * (2 * t - 1) \<in> I_set"
                  using True ht2 unfolding top1_unit_interval_def by (by100 simp)
                hence "h (2 * (2 * t - 1)) \<in> A"
                  using hh unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
                  by (by100 blast)
                ultimately have "x \<in> A"
                  using \<open>x = ?gen_loop t\<close> \<open>?gen_loop t = ?inner _\<close> by (by100 simp)
                thus ?thesis by (by100 blast)
              next
                case False \<comment> \<open>rev(\\<gamma>\\_b)(2(2t-1)-1) \\<in> T.\<close>
                hence "?inner (2 * t - 1) = ?rev_\<gamma>b (2 * (2 * t - 1) - 1)"
                  unfolding top1_path_product_def by (by100 simp)
                moreover have "2 * (2 * t - 1) - 1 \<in> I_set"
                  using False ht2 unfolding top1_unit_interval_def by (by100 simp)
                hence "?rev_\<gamma>b (2 * (2 * t - 1) - 1) \<in> T"
                proof -
                  have "?rev_\<gamma>b (2 * (2 * t - 1) - 1) = \<gamma>b (1 - (2 * (2 * t - 1) - 1))"
                    unfolding top1_path_reverse_def by (by100 simp)
                  moreover have "1 - (2 * (2 * t - 1) - 1) \<in> I_set"
                    using \<open>2 * (2 * t - 1) - 1 \<in> I_set\<close> unfolding top1_unit_interval_def
                    by (by100 simp)
                  hence "\<gamma>b (1 - (2 * (2 * t - 1) - 1)) \<in> T"
                    using h\<gamma>b unfolding top1_is_path_on_def top1_continuous_map_on_def
                    by (by100 blast)
                  ultimately show ?thesis by (by100 simp)
                qed
                ultimately have "x \<in> T"
                  using \<open>x = ?gen_loop t\<close> \<open>?gen_loop t = ?inner _\<close> by (by100 simp)
                thus ?thesis by (by100 blast)
              qed
            qed
          qed
          have h\<gamma>a_img: "\<gamma>a ` I_set \<subseteq> T"
            using h\<gamma>a unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          have h\<gamma>b_img: "\<gamma>b ` I_set \<subseteq> T"
            using h\<gamma>b unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          show "\<exists>gloop. top1_is_loop_on Y TY y0 gloop
              \<and> gloop ` top1_unit_interval \<subseteq> T \<union> A
              \<and> (\<exists>h_arc \<gamma>a' \<gamma>b'. gloop = top1_path_product \<gamma>a' (top1_path_product h_arc (top1_path_reverse \<gamma>b'))
                  \<and> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology Y TY A) h_arc
                  \<and> \<gamma>a' ` I_set \<subseteq> T \<and> \<gamma>b' ` I_set \<subseteq> T)"
            using hgen_loop himg hh h\<gamma>a_img h\<gamma>b_img by (by5000 blast)
        qed
        \<comment> \<open>Choose generator loops with structural info.\<close>
        from bchoice[OF hgen_exists_full]
        obtain gen_loop where hgen_loop_all: "\<forall>A \<in> ?NT.
            top1_is_loop_on Y TY y0 (gen_loop A)
            \<and> gen_loop A ` top1_unit_interval \<subseteq> T \<union> A
            \<and> (\<exists>h_arc \<gamma>a' \<gamma>b'. gen_loop A = top1_path_product \<gamma>a' (top1_path_product h_arc (top1_path_reverse \<gamma>b'))
                \<and> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology Y TY A) h_arc
                \<and> \<gamma>a' ` I_set \<subseteq> T \<and> \<gamma>b' ` I_set \<subseteq> T)"
          by - ((erule exE)+, rule that, assumption)
        have hgen_loop_props: "\<forall>A \<in> ?NT.
            top1_is_loop_on Y TY y0 (gen_loop A)
            \<and> gen_loop A ` top1_unit_interval \<subseteq> T \<union> A"
          using hgen_loop_all by (by100 blast)
        have hgen_loop_structure: "\<forall>A \<in> ?NT. \<exists>h_arc \<gamma>a' \<gamma>b'.
            gen_loop A = top1_path_product \<gamma>a' (top1_path_product h_arc (top1_path_reverse \<gamma>b'))
            \<and> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology Y TY A) h_arc
            \<and> \<gamma>a' ` I_set \<subseteq> T \<and> \<gamma>b' ` I_set \<subseteq> T"
          using hgen_loop_all by (by100 blast)
        \<comment> \<open>Define gen: A \\<mapsto> [gen\\_loop A] (homotopy class).\<close>
        define gen where "gen A = {g. top1_loop_equiv_on Y TY y0 (gen_loop A) g}" for A
        have hgen: "\<forall>A \<in> ?NT. gen A \<in> top1_fundamental_group_carrier Y TY y0"
        proof (intro ballI)
          fix A assume "A \<in> ?NT"
          from hgen_loop_props[rule_format, OF this]
          have "top1_is_loop_on Y TY y0 (gen_loop A)" by (by100 blast)
          thus "gen A \<in> top1_fundamental_group_carrier Y TY y0"
            unfolding gen_def top1_fundamental_group_carrier_def by (by100 blast)
        qed
        \<comment> \<open>Key property: gen\\_loop A maps into T \\<union> A.
           This means gen\\_loop A is also a loop in T \\<union> \\<Union>F for any F containing A.\<close>
        \<comment> \<open>KEY SUB-LEMMA (book Step 1): For finite F \\<subseteq> ?NT, the arc-loops
           {gen(A) | A \\<in> F} form a free basis of \\<pi>\\_1(T \\<union> \\<Union>F).
           Proof: by induction on |F| using SvK (book Step 1 + Step 2).
           This is the generator correspondence that connects the abstract free
           group structure from hfinite\\_subgraph\\_free to the concrete arc-loops.\<close>
        have harc_loops_free: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?NT \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
            \<exists>\<iota>F. top1_is_free_group_full_on
                (top1_fundamental_group_carrier (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                (top1_fundamental_group_mul (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                (top1_fundamental_group_id (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                (top1_fundamental_group_invg (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                \<iota>F F
              \<and> (\<forall>A\<in>F. top1_fundamental_group_induced_on (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A)"
        \<comment> \<open>Proof by strong induction on card F (book Steps 1+2).\<close>
        proof -
          \<comment> \<open>Strong induction on card F.\<close>
          define P where "P \<equiv> \<lambda>F. finite F \<longrightarrow> F \<subseteq> ?NT \<longrightarrow> F \<noteq> {} \<longrightarrow>
              (\<exists>\<iota>F. top1_is_free_group_full_on
                  (top1_fundamental_group_carrier (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_mul (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_id (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_invg (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  \<iota>F F
                \<and> (\<forall>A\<in>F. top1_fundamental_group_induced_on (T \<union> \<Union>F)
                      (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A))"
          { fix n
            have "\<And>F. card F = n \<Longrightarrow> P F"
            proof (induction n rule: less_induct)
              case (less n F)
              show "P F" unfolding P_def
              proof (intro impI)
                assume hFfin: "finite F" and hF_NT: "F \<subseteq> ?NT" and hF_ne: "F \<noteq> {}"
                have hcard: "card F = n" by (rule less.prems)
                show "\<exists>\<iota>F. top1_is_free_group_full_on
                    (top1_fundamental_group_carrier (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                    (top1_fundamental_group_mul (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                    (top1_fundamental_group_id (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                    (top1_fundamental_group_invg (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                    \<iota>F F
                  \<and> (\<forall>A\<in>F. top1_fundamental_group_induced_on (T \<union> \<Union>F)
                        (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A)"
                proof (cases "card F = 1")
            case True
            \<comment> \<open>Base case (book Step 2): F = {D}. \\<pi>\\_1(T \\<union> D) is free with generator [g\\_D].
               Proof: quotient map T\\<union>D \\<rightarrow> S1 sends [g\\_D] to \\<pm>1, forcing [g\\_D] to generate.
               Step A: \\<pi>\\_1(T\\<union>D) \\<cong> \\<Z> (graph\\_one\\_edge\\_pi1\\_iso\\_Z).
               Step B: quotient map \\<pi>: T\\<union>D \\<rightarrow> wedge W (1 circle) exists.
               Step C: \\<pi>*([g\\_D]) generates \\<pi>\\_1(W) \\<cong> \\<Z>.
               Step D: algebraic argument: \\<pi>* is hom \\<Z> \\<rightarrow> \\<Z> mapping [g\\_D] to \\<pm>1,
                       so [g\\_D] maps to \\<pm>1 under the iso, hence generates.\<close>
            show ?thesis
            proof -
              from card_1_singletonE[OF True] obtain D where hD: "F = {D}" by (by100 blast)
              hence hD_NT: "D \<in> ?NT" using hF_NT by (by100 blast)
              hence "D \<in> \<A>" by (by100 blast)
              have hTD_eq: "T \<union> \<Union>F = T \<union> D" using hD by (by100 simp)
              let ?TD = "T \<union> D" and ?TTD = "subspace_topology Y TY (T \<union> D)"
              \<comment> \<open>Define \\<iota>F(D) = [gen\\_loop(D)] in \\<pi>\\_1(T\\<union>D).\<close>
              define \<iota>F where "\<iota>F A = {g. top1_loop_equiv_on ?TD ?TTD y0 (gen_loop A) g}" for A
              \<comment> \<open>gen\\_loop(D) is a loop in T\\<union>D (image \\<subseteq> T\\<union>D from hgen\\_loop\\_props).\<close>
              have hgenD_loop_TD: "top1_is_loop_on ?TD ?TTD y0 (gen_loop D)"
              proof -
                from hgen_loop_props[rule_format, OF hD_NT]
                have "gen_loop D ` top1_unit_interval \<subseteq> T \<union> D" by (by100 blast)
                have "top1_is_loop_on Y TY y0 (gen_loop D)"
                  using hgen_loop_props hD_NT by (by100 blast)
                hence "top1_continuous_map_on I_set I_top Y TY (gen_loop D)"
                  unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTY_top hTY_top,
                    rule_format]
                    \<open>top1_continuous_map_on I_set I_top Y TY (gen_loop D)\<close>
                    \<open>gen_loop D ` top1_unit_interval \<subseteq> ?TD\<close> hTD_sub
                have "top1_continuous_map_on I_set I_top ?TD ?TTD (gen_loop D)"
                  by (by100 blast)
                moreover have "gen_loop D 0 = y0" "gen_loop D 1 = y0"
                  using \<open>top1_is_loop_on Y TY y0 (gen_loop D)\<close>
                  unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                  by (by100 blast)
              qed
              \<comment> \<open>\\<iota>F(D) \\<in> carrier(T\\<union>D).\<close>
              have h\<iota>F_carrier: "\<iota>F D \<in> top1_fundamental_group_carrier ?TD ?TTD y0"
                unfolding \<iota>F_def top1_fundamental_group_carrier_def
                using hgenD_loop_TD by (by100 blast)
              \<comment> \<open>incl*(\\<iota>F(D)) = gen(D): the inclusion sends [gen\\_loop(D)]\\_TD to [gen\\_loop(D)]\\_Y = gen(D).\<close>
              have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
              have h_incl_gen: "top1_fundamental_group_induced_on ?TD ?TTD y0 Y TY y0 (\<lambda>x. x)
                  (\<iota>F D) = gen D"
              proof -
                from subspace_inclusion_induced_class[OF hTY_top hTD_sub hgenD_loop_TD]
                have "top1_fundamental_group_induced_on ?TD ?TTD y0 Y TY y0 (\<lambda>x. x)
                    {g. top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) g} =
                    {g. top1_loop_equiv_on Y TY y0 (gen_loop D) g}" .
                thus ?thesis unfolding \<iota>F_def gen_def by (by100 simp)
              qed
              \<comment> \<open>\\<pi>\\_1(T\\<union>D) is free on {D} with generator \\<iota>F(D).
                 This is the KEY claim: [gen\\_loop(D)] generates \\<pi>\\_1(T\\<union>D) and has infinite order.
                 Follows from: \\<pi>\\_1(T\\<union>D) \\<cong> \\<Z> (graph\\_one\\_edge\\_pi1\\_iso\\_Z) and
                 [gen\\_loop(D)] maps to \\<pm>1 under the quotient T\\<union>D \\<rightarrow> S1.\<close>
              \<comment> \<open>Graph structure of T\\<union>D (needed for iso\\_Z and continuity).\<close>
              have hTD_sub_Y: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
              have hTY_top_loc: "is_topology_on Y TY"
                using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
              have hTD_graph_outer: "top1_is_graph_on ?TD ?TTD"
              proof -
                let ?\<A>_TD = "{A \<in> \<A>. A \<subseteq> ?TD}"
                have h\<A>TD_sub: "?\<A>_TD \<subseteq> \<A>" by (by100 blast)
                have hTD_eq_union: "?TD = \<Union>?\<A>_TD"
                proof (rule set_eqI, rule iffI)
                  fix x assume "x \<in> ?TD"
                  show "x \<in> \<Union>?\<A>_TD"
                  proof (cases "x \<in> T")
                    case True
                    hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
                    then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" by (by100 blast)
                    thus ?thesis using \<open>A \<subseteq> T\<close> by (by100 blast)
                  next
                    case False
                    hence "x \<in> D" using \<open>x \<in> ?TD\<close> by (by100 blast)
                    thus ?thesis using \<open>D \<in> \<A>\<close> by (by100 blast)
                  qed
                next
                  fix x assume "x \<in> \<Union>?\<A>_TD" thus "x \<in> ?TD" by (by100 blast)
                qed
                have h\<A>TD_cover_Y: "\<Union>?\<A>_TD \<subseteq> Y" using h\<A> by (by100 blast)
                have h\<A>TD_arcs_Y: "\<forall>A\<in>?\<A>_TD. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
                  using h\<A> by (by100 blast)
                have h\<A>TD_inter_Y: "\<forall>A\<in>?\<A>_TD. \<forall>B\<in>?\<A>_TD. A \<noteq> B \<longrightarrow>
                    A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                  \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                  \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                  using h\<A>_inter by (by100 blast)
                have h\<A>TD_coh_Y: "\<forall>C. C \<subseteq> \<Union>?\<A>_TD \<longrightarrow>
                    (closedin_on (\<Union>?\<A>_TD) (subspace_topology Y TY (\<Union>?\<A>_TD)) C \<longleftrightarrow>
                     (\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
                  using subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                      h\<A>TD_sub hTD_eq_union] hTD_eq_union by (by100 simp)
                show ?thesis using subgraph_union_of_arcs_is_graph[OF assms(1)
                    h\<A>TD_arcs_Y h\<A>TD_cover_Y h\<A>TD_inter_Y h\<A>TD_coh_Y] hTD_eq_union by (by100 simp)
              qed
              \<comment> \<open>Step A: \\<pi>\\_1(T\\<union>D) \\<cong> Z (graph\\_one\\_edge\\_pi1\\_iso\\_Z).\<close>
              have hTD_iso_Z: "top1_groups_isomorphic_on
                  (top1_fundamental_group_carrier ?TD ?TTD y0) (top1_fundamental_group_mul ?TD ?TTD y0)
                  top1_Z_group top1_Z_mul"
              proof -
                \<comment> \<open>T\\<union>D is a graph: subgraph\\_union\\_of\\_arcs\\_is\\_graph.\<close>
                let ?\<A>_TD = "{A \<in> \<A>. A \<subseteq> ?TD}"
                have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                have hTY_top: "is_topology_on Y TY"
                  using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                have hY_strict: "is_topology_on_strict Y TY"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have hY_haus: "is_hausdorff_on Y TY"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have hTD_graph: "top1_is_graph_on ?TD ?TTD"
                proof -
                  let ?\<A>_TD = "{A \<in> \<A>. A \<subseteq> ?TD}"
                  have h\<A>TD_sub: "?\<A>_TD \<subseteq> \<A>" by (by100 blast)
                  have hTD_eq_union: "?TD = \<Union>?\<A>_TD"
                  proof (rule set_eqI, rule iffI)
                    fix x assume "x \<in> ?TD"
                    show "x \<in> \<Union>?\<A>_TD"
                    proof (cases "x \<in> T")
                      case True
                      hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
                      then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" by (by100 blast)
                      thus ?thesis using \<open>A \<subseteq> T\<close> by (by100 blast)
                    next
                      case False
                      hence "x \<in> D" using \<open>x \<in> ?TD\<close> by (by100 blast)
                      thus ?thesis using \<open>D \<in> \<A>\<close> by (by100 blast)
                    qed
                  next
                    fix x assume "x \<in> \<Union>?\<A>_TD" thus "x \<in> ?TD" by (by100 blast)
                  qed
                  have h\<A>TD_cover_Y: "\<Union>?\<A>_TD \<subseteq> Y" using h\<A> by (by100 blast)
                  have h\<A>TD_arcs_Y: "\<forall>A\<in>?\<A>_TD. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
                    using h\<A> by (by100 blast)
                  have h\<A>TD_inter_Y: "\<forall>A\<in>?\<A>_TD. \<forall>B\<in>?\<A>_TD. A \<noteq> B \<longrightarrow>
                      A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                    \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                    \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                    using h\<A>_inter by (by100 blast)
                  have h\<A>TD_coh_Y: "\<forall>C. C \<subseteq> \<Union>?\<A>_TD \<longrightarrow>
                      (closedin_on (\<Union>?\<A>_TD) (subspace_topology Y TY (\<Union>?\<A>_TD)) C \<longleftrightarrow>
                       (\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
                    using subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                        h\<A>TD_sub hTD_eq_union] hTD_eq_union by (by100 simp)
                  show ?thesis using subgraph_union_of_arcs_is_graph[OF assms(1)
                      h\<A>TD_arcs_Y h\<A>TD_cover_Y h\<A>TD_inter_Y h\<A>TD_coh_Y] hTD_eq_union by (by100 simp)
                qed
                have hTD_conn: "top1_connected_on ?TD ?TTD"
                proof -
                  have hD_arc: "top1_is_arc_on D (subspace_topology Y TY D)"
                    using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                  have hD_sub: "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                  have "\<exists>e. e \<in> T \<and> e \<in> D"
                  proof -
                    obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
                        top1_unit_interval_topology D (subspace_topology Y TY D) hj"
                      using hD_arc unfolding top1_is_arc_on_def by (by100 blast)
                    have hbij: "bij_betw hj top1_unit_interval D"
                      using hhj unfolding top1_homeomorphism_on_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF hY_strict hY_haus hD_sub hD_arc hhj]
                    have "top1_arc_endpoints_on D (subspace_topology Y TY D) = {hj 0, hj 1}" .
                    have "hj 0 \<in> T" using hNT_endpoints[rule_format, OF hD_NT] \<open>_ = {hj 0, hj 1}\<close>
                      by (by100 simp)
                    have h0_I: "(0::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have "hj 0 \<in> D" using hbij h0_I
                      unfolding bij_betw_def by (by100 blast)
                    thus ?thesis using \<open>hj 0 \<in> T\<close> by (by100 blast)
                  qed
                  from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub _ _ _ hT_x0, of "{D}"]
                  have "top1_path_connected_on (T \<union> \<Union>{D}) (subspace_topology Y TY (T \<union> \<Union>{D}))"
                    using hD_arc hD_sub \<open>\<exists>e. e \<in> T \<and> e \<in> D\<close> by (by100 simp)
                  hence "top1_path_connected_on ?TD ?TTD" by (by100 simp)
                  thus ?thesis using top1_path_connected_imp_connected by (by100 blast)
                qed
                \<comment> \<open>Apply graph\\_one\\_edge\\_pi1\\_iso\\_Z to subgraph T\\<union>D.\<close>
                let ?\<A>_TD = "{A \<in> \<A>. A \<subseteq> ?TD}"
                have hTD_eq_union: "?TD = \<Union>?\<A>_TD"
                proof (rule set_eqI, rule iffI)
                  fix x assume "x \<in> ?TD"
                  show "x \<in> \<Union>?\<A>_TD"
                  proof (cases "x \<in> T")
                    case True
                    hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
                    then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" by (by100 blast)
                    thus ?thesis using \<open>A \<subseteq> T\<close> by (by100 blast)
                  next
                    case False
                    hence "x \<in> D" using \<open>x \<in> ?TD\<close> by (by100 blast)
                    thus ?thesis using \<open>D \<in> \<A>\<close> by (by100 blast)
                  qed
                next
                  fix x assume "x \<in> \<Union>?\<A>_TD" thus "x \<in> ?TD" by (by100 blast)
                qed
                show ?thesis
                proof (rule graph_one_edge_pi1_iso_Z[where \<A>="?\<A>_TD"])
                  show "top1_is_graph_on ?TD ?TTD" by (rule hTD_graph)
                  show "top1_connected_on ?TD ?TTD" by (rule hTD_conn)
                  show "y0 \<in> ?TD" using hT_x0 by (by100 blast)
                  show "\<forall>A\<in>?\<A>_TD. A \<subseteq> ?TD \<and> top1_is_arc_on A (subspace_topology ?TD ?TTD A)"
                  proof (intro ballI conjI)
                    fix A assume "A \<in> ?\<A>_TD"
                    show "A \<subseteq> ?TD" using \<open>A \<in> ?\<A>_TD\<close> by (by100 blast)
                    have "A \<in> \<A>" using \<open>A \<in> ?\<A>_TD\<close> by (by100 blast)
                    have "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_TD\<close> in blast)
                    thus "top1_is_arc_on A (subspace_topology ?TD ?TTD A)"
                      using h\<A> \<open>A \<in> \<A>\<close> by simp
                  qed
                  show "\<Union>?\<A>_TD = ?TD" by (rule hTD_eq_union[symmetric])
                  show "\<forall>A\<in>?\<A>_TD. \<forall>B\<in>?\<A>_TD. A \<noteq> B \<longrightarrow>
                      A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)
                    \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?TD ?TTD B)
                    \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                  proof (intro ballI impI)
                    fix A B assume "A \<in> ?\<A>_TD" "B \<in> ?\<A>_TD" "A \<noteq> B"
                    from h\<A>_inter[rule_format, OF _ _ \<open>A \<noteq> B\<close>]
                    have h_Y: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                      \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                      \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                      using \<open>A \<in> ?\<A>_TD\<close> \<open>B \<in> ?\<A>_TD\<close> by (by100 blast)
                    have "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_TD\<close> in blast)
                    moreover have "subspace_topology ?TD ?TTD B = subspace_topology Y TY B"
                      by (rule subspace_topology_trans) (use \<open>B \<in> ?\<A>_TD\<close> in blast)
                    ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)
                      \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?TD ?TTD B)
                      \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" using h_Y by simp
                  qed
                  show "\<forall>C. C \<subseteq> ?TD \<longrightarrow>
                      (closedin_on ?TD ?TTD C \<longleftrightarrow>
                       (\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology ?TD ?TTD A) (A \<inter> C)))"
                  proof (intro allI impI iffI ballI)
                    fix C A assume hC: "C \<subseteq> ?TD" and hcl: "closedin_on ?TD ?TTD C" and "A \<in> ?\<A>_TD"
                    have "A \<subseteq> ?TD" using \<open>A \<in> ?\<A>_TD\<close> by (by100 blast)
                    have hsub_eq: "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?TD\<close>])
                    have h\<A>TD_sub: "?\<A>_TD \<subseteq> \<A>" by (by100 blast)
                    from subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                        h\<A>TD_sub hTD_eq_union, rule_format, OF hC, THEN iffD1, OF hcl]
                    have "\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology Y TY A) (A \<inter> C)" .
                    thus "closedin_on A (subspace_topology ?TD ?TTD A) (A \<inter> C)"
                      using \<open>A \<in> ?\<A>_TD\<close> hsub_eq by simp
                  next
                    fix C assume hC: "C \<subseteq> ?TD"
                      and hall: "\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology ?TD ?TTD A) (A \<inter> C)"
                    have h\<A>TD_sub: "?\<A>_TD \<subseteq> \<A>" by (by100 blast)
                    have "\<forall>A\<in>?\<A>_TD. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                    proof (intro ballI)
                      fix A assume "A \<in> ?\<A>_TD"
                      have "A \<subseteq> ?TD" using \<open>A \<in> ?\<A>_TD\<close> by (by100 blast)
                      have "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                        by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?TD\<close>])
                      from hall[rule_format, OF \<open>A \<in> ?\<A>_TD\<close>]
                      show "closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                        using \<open>subspace_topology ?TD ?TTD A = _\<close> by simp
                    qed
                    from subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                        h\<A>TD_sub hTD_eq_union, rule_format, OF hC, THEN iffD2, OF this]
                    show "closedin_on ?TD ?TTD C" .
                  qed
                  show "top1_is_tree_on T (subspace_topology ?TD ?TTD T)"
                  proof -
                    have "subspace_topology ?TD ?TTD T = subspace_topology Y TY T"
                      by (rule subspace_topology_trans) (by100 blast)
                    thus ?thesis using hT_tree by simp
                  qed
                  show "T \<subseteq> ?TD" by (by100 blast)
                  show "\<forall>A\<in>?\<A>_TD. A \<subseteq> T \<or>
                      A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)"
                  proof (intro ballI)
                    fix A assume "A \<in> ?\<A>_TD"
                    have "A \<in> \<A>" using \<open>A \<in> ?\<A>_TD\<close> by (by100 blast)
                    have "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_TD\<close> in blast)
                    from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
                    show "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)"
                      using \<open>subspace_topology ?TD ?TTD A = _\<close> by simp
                  qed
                  show "y0 \<in> T" by (rule hT_x0)
                  show "\<forall>A\<in>{A \<in> ?\<A>_TD. \<not> A \<subseteq> T}.
                      \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A). e \<in> T"
                  proof (intro ballI)
                    fix A e assume "A \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}"
                        and "e \<in> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)"
                    have "A \<in> \<A>" "\<not> A \<subseteq> T" using \<open>A \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}\<close> by (by100 blast)+
                    hence "A \<in> ?NT" by (by100 blast)
                    have "subspace_topology ?TD ?TTD A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans) (use \<open>A \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}\<close> in blast)
                    thus "e \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close>
                      \<open>e \<in> top1_arc_endpoints_on A (subspace_topology ?TD ?TTD A)\<close> by simp
                  qed
                  show "D \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}" using \<open>D \<in> \<A>\<close> hD_NT by (by100 blast)
                  show "{A \<in> ?\<A>_TD. \<not> A \<subseteq> T} = {D}"
                  proof (rule set_eqI, rule iffI)
                    fix A assume "A \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}"
                    hence "A \<in> \<A>" "\<not> A \<subseteq> T" "A \<subseteq> ?TD" by (by100 blast)+
                    hence "A \<in> ?NT" by (by100 blast)
                    show "A \<in> {D}"
                    proof (rule ccontr)
                      assume "A \<notin> {D}" hence "A \<noteq> D" by (by100 blast)
                      obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
                          top1_unit_interval_topology A (subspace_topology Y TY A) hj"
                        using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
                      have hbij: "bij_betw hj top1_unit_interval A"
                        using hhj unfolding top1_homeomorphism_on_def by (by100 blast)
                      have h12_I: "(1/2::real) \<in> top1_unit_interval"
                        unfolding top1_unit_interval_def by (by100 simp)
                      have "hj (1/2) \<in> A" using hbij h12_I unfolding bij_betw_def by (by100 blast)
                      have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                      from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>A \<subseteq> Y\<close> _ hhj]
                      have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {hj 0, hj 1}"
                        using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                      have hinj: "inj_on hj top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
                      have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                      have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                      have "hj (1/2) \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                      proof -
                        have "hj (1/2) \<noteq> hj 0"
                        proof
                          assume "hj (1/2) = hj 0"
                          from inj_onD[OF hinj this h12_I h0_I] show False by (by100 simp)
                        qed
                        have "hj (1/2) \<noteq> hj 1"
                        proof
                          assume "hj (1/2) = hj 1"
                          from inj_onD[OF hinj this h12_I h1_I] show False by (by100 simp)
                        qed
                        thus ?thesis using hep \<open>hj (1/2) \<noteq> hj 0\<close> by (by100 blast)
                      qed
                      have "hj (1/2) \<notin> T"
                        using hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
                          \<open>hj (1/2) \<in> A\<close> \<open>hj (1/2) \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                      have "hj (1/2) \<notin> D"
                      proof
                        assume "hj (1/2) \<in> D"
                        have "D \<in> \<A>" using \<open>D \<in> \<A>\<close> .
                        from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>D \<in> \<A>\<close> \<open>A \<noteq> D\<close>]
                        have "A \<inter> D \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
                        hence "hj (1/2) \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                          using \<open>hj (1/2) \<in> A\<close> \<open>hj (1/2) \<in> D\<close> by (by100 blast)
                        thus False using \<open>hj (1/2) \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                      qed
                      have "hj (1/2) \<notin> ?TD" using \<open>hj (1/2) \<notin> T\<close> \<open>hj (1/2) \<notin> D\<close> by (by100 blast)
                      thus False using \<open>A \<subseteq> ?TD\<close> \<open>hj (1/2) \<in> A\<close> by (by100 blast)
                    qed
                  next
                    fix A assume "A \<in> {D}"
                    hence "A = D" by (by100 blast)
                    have "D \<subseteq> ?TD" by (by100 blast)
                    have "\<not> D \<subseteq> T" using hD_NT by (by100 blast)
                    thus "A \<in> {A \<in> ?\<A>_TD. \<not> A \<subseteq> T}"
                      using \<open>A = D\<close> \<open>D \<in> \<A>\<close> \<open>D \<subseteq> ?TD\<close> \<open>\<not> D \<subseteq> T\<close> by (by100 blast)
                  qed
                qed
              qed
              \<comment> \<open>Step B: [gen\\_loop(D)] generates \\<pi>\\_1(T\\<union>D) (book Step 2).\<close>
              have hTD_grp: "top1_is_group_on
                  (top1_fundamental_group_carrier ?TD ?TTD y0)
                  (top1_fundamental_group_mul ?TD ?TTD y0)
                  (top1_fundamental_group_id ?TD ?TTD y0)
                  (top1_fundamental_group_invg ?TD ?TTD y0)"
              proof -
                have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                have hTY_top: "is_topology_on Y TY"
                  using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                have hTTD_top: "is_topology_on ?TD ?TTD"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hTD_sub])
                have "y0 \<in> ?TD" using hT_x0 by (by100 blast)
                from top1_fundamental_group_is_group[OF hTTD_top this]
                show ?thesis by (by100 blast)
              qed
              have hgen_TD: "top1_fundamental_group_carrier ?TD ?TTD y0 =
                  top1_subgroup_generated_on
                    (top1_fundamental_group_carrier ?TD ?TTD y0) (top1_fundamental_group_mul ?TD ?TTD y0)
                    (top1_fundamental_group_id ?TD ?TTD y0) (top1_fundamental_group_invg ?TD ?TTD y0)
                    {\<iota>F D}"
              proof -
                \<comment> \<open>Quotient map approach: construct \\<pi>: T\\<union>D \\<rightarrow> S1 collapsing T.
                   \\<pi>*(\\<iota>F(D)) = [standard S1 loop] generates \\<pi>\\_1(S1) \\<cong> Z.
                   Since \\<pi>\\_1(T\\<union>D) \\<cong> Z and \\<pi>* surjective \\<Rightarrow> iso \\<Rightarrow> \\<iota>F(D) generates.\<close>
                \<comment> \<open>Step G1: Construct quotient map \\<pi>: T\\<union>D \\<rightarrow> S1.\<close>
                obtain hD where hhD: "top1_homeomorphism_on top1_unit_interval
                    top1_unit_interval_topology D (subspace_topology Y TY D) hD"
                  using h\<A> \<open>D \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
                have hD_bij: "bij_betw hD top1_unit_interval D"
                  using hhD unfolding top1_homeomorphism_on_def by (by100 blast)
                let ?hD_inv = "the_inv_into top1_unit_interval hD"
                define \<pi> where "\<pi> x = (if x \<in> T then (1::real, 0::real)
                    else (cos (2 * pi * ?hD_inv x), sin (2 * pi * ?hD_inv x)))" for x
                \<comment> \<open>Step G2: \\<pi> maps T\\<union>D to S1.\<close>
                have h\<pi>_maps: "\<pi> ` ?TD \<subseteq> top1_S1"
                proof (rule image_subsetI)
                  fix x assume "x \<in> ?TD"
                  show "\<pi> x \<in> top1_S1"
                  proof (cases "x \<in> T")
                    case True
                    thus ?thesis unfolding \<pi>_def top1_S1_def by (by100 simp)
                  next
                    case False
                    hence "x \<in> D" using \<open>x \<in> ?TD\<close> by (by100 blast)
                    have "fst (\<pi> x) ^ 2 + snd (\<pi> x) ^ 2 = 1"
                    proof -
                      let ?\<theta> = "2 * pi * ?hD_inv x"
                      have "(cos ?\<theta>)\<^sup>2 + (sin ?\<theta>)\<^sup>2 = 1" by (by100 simp)
                      moreover have "\<pi> x = (cos ?\<theta>, sin ?\<theta>)" unfolding \<pi>_def using False by (by100 simp)
                      ultimately show ?thesis by (by100 simp)
                    qed
                    thus ?thesis unfolding top1_S1_def by (by100 blast)
                  qed
                qed
                \<comment> \<open>Step G3: \\<pi> is continuous.\<close>
                \<comment> \<open>G3+G4+G5+G6b: \\<pi> continuous AND \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1).
                   Combined proof plan:
                   G3 (\\<pi> continuous): pasting\\_lemma\\_two\\_closed on T\\<union>D = T \\<union> D.
                     T closed (coherent topology), D closed (compact + Hausdorff).
                     \\<pi>|T = constant (continuous), \\<pi>|D = cos/sin \\<circ> hD\\_inv (continuous).
                   G4 (\\<pi>\\<circ>gen\\_loop \\<simeq> \\<pm>std\\_loop):
                     gen\\_loop D = \\<gamma>a' * (h\\_arc * rev(\\<gamma>b')) [hgen\\_loop\\_structure].
                     comp\\_path\\_product: \\<pi>\\<circ>gen\\_loop = (\\<pi>\\<circ>\\<gamma>a') * ((\\<pi>\\<circ>h\\_arc) * (\\<pi>\\<circ>rev(\\<gamma>b'))).
                     \\<pi>\\<circ>\\<gamma>a' = constant, \\<pi>\\<circ>rev(\\<gamma>b') = constant (tree paths).
                     \\<pi>\\<circ>h\\_arc = std\\_loop \\<circ> (hD\\_inv \\<circ> h\\_arc), where hD\\_inv \\<circ> h\\_arc: [0,1]\\<rightarrow>[0,1] homeo.
                     reparam\\_path\\_homotopy: f\\<circ>\\<phi> \\<simeq> f\\<circ>\\<psi> when \\<phi>,\\<psi> same endpoints.
                     Endpoints: hD\\_inv(h\\_arc(0)), hD\\_inv(h\\_arc(1)) \\<in> {0,1}.
                     Case 1: same as id \\<Rightarrow> \\<pi>\\<circ>h\\_arc \\<simeq> std\\_loop.
                     Case 2: reversed \\<Rightarrow> \\<pi>\\<circ>h\\_arc \\<simeq> rev(std\\_loop).
                     Theorem\\_51\\_2 (left/right identity): const*(\\<pm>std*const) \\<simeq> \\<pm>std.
                   G5: induced\\_on definition + loop\\_equiv transitivity.
                   G6b: both [std\\_loop] and [rev(std\\_loop)] generate \\<pi>\\_1(S1).\<close>
                have h\<pi>_cont: "top1_continuous_map_on ?TD ?TTD top1_S1 top1_S1_topology \<pi>"
                proof -
                  have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                  have hTY_top: "is_topology_on Y TY"
                    using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                  have hTTD_top_g: "is_topology_on ?TD ?TTD"
                    by (rule subspace_topology_is_topology_on[OF hTY_top hTD_sub])
                  have hS1_top_g: "is_topology_on top1_S1 top1_S1_topology"
                    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
                  \<comment> \<open>T and D closed in T\\<union>D.\<close>
                  \<comment> \<open>T and D closed in T\\<union>D.\<close>
                  \<comment> \<open>T closed in Y (coherent topology of Y), then closed in subspace T\\<union>D.\<close>
                  have hT_closed_Y: "closedin_on Y TY T"
                  proof -
                    have "T \<subseteq> Y" using hT_sub by (by100 blast)
                    have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> T)"
                      proof (intro ballI)
                        fix A assume "A \<in> \<A>"
                        show "closedin_on A (subspace_topology Y TY A) (A \<inter> T)"
                        proof (cases "A \<subseteq> T")
                          case True
                          hence "A \<inter> T = A" by (by100 blast)
                          have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                          have "is_topology_on A (subspace_topology Y TY A)"
                            by (rule subspace_topology_is_topology_on[OF hTY_top_loc \<open>A \<subseteq> Y\<close>])
                          \<comment> \<open>A \\<inter> T = A \\<Rightarrow> A \\<inter> T closed (whole space closed in itself).\<close>
                          have "closedin_on A (subspace_topology Y TY A) A"
                          proof -
                            have "{} \<in> subspace_topology Y TY A"
                              using \<open>is_topology_on A _\<close>[unfolded is_topology_on_def, THEN conjunct1] .
                            have "A - A = {}" by (by100 blast)
                            hence "A - A \<in> subspace_topology Y TY A"
                              using \<open>{} \<in> _\<close> by simp
                            thus ?thesis unfolding closedin_on_def by (by100 blast)
                          qed
                          thus ?thesis using \<open>A \<inter> T = A\<close> by simp
                        next
                          case False
                          \<comment> \<open>A not in T: A\\<inter>T \\<subseteq> endpoints(A), finite, closed in Hausdorff.\<close>
                          have "A \<in> ?NT" using \<open>A \<in> \<A>\<close> False by (by100 blast)
                          have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                            using hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
                          have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                          have hY_haus_loc: "is_hausdorff_on Y TY"
                            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                          have "is_hausdorff_on A (subspace_topology Y TY A)"
                            using Theorem_17_11 hY_haus_loc \<open>A \<subseteq> Y\<close> by (by100 blast)
                          have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
                          proof -
                            have "top1_is_arc_on A (subspace_topology Y TY A)"
                              using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                            have harc_A: "top1_is_arc_on A (subspace_topology Y TY A)"
                              using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                            obtain h_ep where hh_ep: "top1_homeomorphism_on top1_unit_interval
                                top1_unit_interval_topology A (subspace_topology Y TY A) h_ep"
                              using harc_A unfolding top1_is_arc_on_def by (by100 blast)
                            have hY_strict: "is_topology_on_strict Y TY"
                              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                            from arc_endpoints_are_boundary[OF hY_strict hY_haus_loc \<open>A \<subseteq> Y\<close>
                                harc_A hh_ep]
                            show ?thesis by (by100 simp)
                          qed
                          have hfin_ep: "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
                            using \<open>finite (top1_arc_endpoints_on A _)\<close> .
                          have "finite (A \<inter> T)"
                            using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close> hfin_ep
                            finite_subset by (by100 blast)
                          have "A \<inter> T \<subseteq> A" by (by100 blast)
                          from Theorem_17_8[OF \<open>is_hausdorff_on A _\<close> \<open>finite (A \<inter> T)\<close> \<open>A \<inter> T \<subseteq> A\<close>]
                          show ?thesis .
                        qed
                      qed
                    from h\<A>_coh[rule_format, OF \<open>T \<subseteq> Y\<close>] this
                    show ?thesis by (by100 blast)
                  qed
                  have hT_closed: "closedin_on ?TD ?TTD T"
                    by (rule closedin_subspace_from_ambient[OF hTY_top_loc hT_closed_Y hTD_sub_Y])
                       (by100 blast)
                  \<comment> \<open>D closed in Y (arc = compact in Hausdorff), then in subspace.\<close>
                  have hD_closed_Y: "closedin_on Y TY D"
                  proof -
                    have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                    from h\<A>_coh[rule_format, OF this]
                    show ?thesis
                    proof (rule iffD2)
                      show "\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> D)"
                      proof (intro ballI)
                        fix A assume "A \<in> \<A>"
                        show "closedin_on A (subspace_topology Y TY A) (A \<inter> D)"
                        proof (cases "A = D")
                          case True
                          hence "A \<inter> D = D" by (by100 blast)
                          have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                          have "is_topology_on A (subspace_topology Y TY A)"
                            by (rule subspace_topology_is_topology_on[OF hTY_top_loc \<open>A \<subseteq> Y\<close>])
                          have "closedin_on A (subspace_topology Y TY A) A"
                          proof -
                            have "{} \<in> subspace_topology Y TY A"
                              using \<open>is_topology_on A _\<close>[unfolded is_topology_on_def, THEN conjunct1] .
                            have "A - A = {}" by (by100 blast)
                            hence "A - A \<in> subspace_topology Y TY A" using \<open>{} \<in> _\<close> by simp
                            thus ?thesis unfolding closedin_on_def by (by100 blast)
                          qed
                          thus ?thesis using True \<open>A \<inter> D = D\<close> by simp
                        next
                          case False
                          have "A \<inter> D \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                          proof -
                            from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> _ False]
                            show ?thesis using \<open>D \<in> \<A>\<close> by (by100 blast)
                          qed
                          have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                          have hY_haus_d: "is_hausdorff_on Y TY"
                            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                          have "is_hausdorff_on A (subspace_topology Y TY A)"
                            using Theorem_17_11 hY_haus_d \<open>A \<subseteq> Y\<close> by (by100 blast)
                          have harc_Ad: "top1_is_arc_on A (subspace_topology Y TY A)"
                            using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                          obtain h_d where hh_d: "top1_homeomorphism_on top1_unit_interval
                              top1_unit_interval_topology A (subspace_topology Y TY A) h_d"
                            using harc_Ad unfolding top1_is_arc_on_def by (by100 blast)
                          have hY_strict_d: "is_topology_on_strict Y TY"
                            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                          have hfin_epd: "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
                            using arc_endpoints_are_boundary[OF hY_strict_d hY_haus_d \<open>A \<subseteq> Y\<close> harc_Ad hh_d]
                            by (by100 simp)
                          have hfin_AD: "finite (A \<inter> D)"
                            using \<open>A \<inter> D \<subseteq> _\<close> hfin_epd finite_subset by (by100 blast)
                          have "A \<inter> D \<subseteq> A" by (by100 blast)
                          from Theorem_17_8[OF \<open>is_hausdorff_on A _\<close> hfin_AD \<open>A \<inter> D \<subseteq> A\<close>]
                          show ?thesis .
                        qed
                      qed
                    qed
                  qed
                  have hD_closed: "closedin_on ?TD ?TTD D"
                    by (rule closedin_subspace_from_ambient[OF hTY_top_loc hD_closed_Y hTD_sub_Y])
                       (by100 blast)
                  have hcover: "T \<union> D = ?TD" by (by100 blast)
                  have h\<pi>_maps_fn: "\<forall>x \<in> ?TD. \<pi> x \<in> top1_S1"
                    using h\<pi>_maps by (by100 blast)
                  \<comment> \<open>\\<pi>|T continuous (constant map — same pattern as before).\<close>
                  have h\<pi>_cont_T: "top1_continuous_map_on T (subspace_topology ?TD ?TTD T)
                      top1_S1 top1_S1_topology \<pi>"
                  proof -
                    have hT_sub_TD: "T \<subseteq> ?TD" by (by100 blast)
                    have hTT_top: "is_topology_on T (subspace_topology ?TD ?TTD T)"
                      by (rule subspace_topology_is_topology_on[OF hTTD_top_g hT_sub_TD])
                    show ?thesis unfolding top1_continuous_map_on_def
                    proof (intro conjI ballI)
                      fix x assume "x \<in> T"
                      thus "\<pi> x \<in> top1_S1" using h\<pi>_maps hT_sub by (by100 blast)
                    next
                      fix V assume "V \<in> top1_S1_topology"
                      have h\<pi>T: "\<forall>x \<in> T. \<pi> x = (1::real, 0::real)"
                        unfolding \<pi>_def by (by100 simp)
                      show "{x \<in> T. \<pi> x \<in> V} \<in> subspace_topology ?TD ?TTD T"
                      proof (cases "(1::real, 0::real) \<in> V")
                        case True
                        have "{x \<in> T. \<pi> x \<in> V} = T"
                        proof (rule set_eqI, rule iffI)
                          fix x assume "x \<in> {x \<in> T. \<pi> x \<in> V}" thus "x \<in> T" by (by100 blast)
                        next
                          fix x assume "x \<in> T"
                          thus "x \<in> {x \<in> T. \<pi> x \<in> V}" using h\<pi>T True by (by100 simp)
                        qed
                        moreover have "T \<in> subspace_topology ?TD ?TTD T"
                          using hTT_top[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct1] .
                        ultimately show ?thesis by simp
                      next
                        case False
                        have heq: "{x \<in> T. \<pi> x \<in> V} = {}"
                        proof (rule ccontr)
                          assume "\<not> ?thesis"
                          then obtain x where "x \<in> T" "\<pi> x \<in> V" by (by100 blast)
                          thus False using h\<pi>T False by (by100 simp)
                        qed
                        show ?thesis using hTT_top[unfolded is_topology_on_def, THEN conjunct1,
                            unfolded heq[symmetric]] .
                      qed
                    qed
                  qed
                  \<comment> \<open>\\<pi>|D continuous.\<close>
                  have h\<pi>_cont_D: "top1_continuous_map_on D (subspace_topology ?TD ?TTD D)
                      top1_S1 top1_S1_topology \<pi>"
                  proof -
                    \<comment> \<open>On D, \\<pi>(x) = (cos(2\\<pi>*hD\\_inv(x)), sin(2\\<pi>*hD\\_inv(x))) for x \\<notin> T,
                       and (1,0) for x \\<in> T. Both branches agree on D\\<inter>T (endpoints).\<close>
                    \<comment> \<open>Subspace topology transitivity: subspace T\\<union>D TTD D = subspace Y TY D.\<close>
                    have hD_sub_TD: "D \<subseteq> ?TD" by (by100 blast)
                    have hD_top_eq: "subspace_topology ?TD ?TTD D = subspace_topology Y TY D"
                      by (rule subspace_topology_trans[OF hD_sub_TD])
                    \<comment> \<open>\\<pi>|D = composition of continuous maps. Sorry for now.\<close>
                    \<comment> \<open>Key: \\<pi> agrees with std\\_loop \\<circ> hD\\_inv on ALL of D.
                       At endpoints: both give (1,0). At interior: by definition.\<close>
                    let ?std_loop = "\<lambda>t. (cos (2 * pi * t), sin (2 * pi * t))"
                    have h\<pi>_eq_on_D: "\<forall>x \<in> D. \<pi> x = ?std_loop (?hD_inv x)"
                    proof (intro ballI)
                      fix x assume "x \<in> D"
                      show "\<pi> x = ?std_loop (?hD_inv x)"
                      proof (cases "x \<in> T")
                        case True
                        \<comment> \<open>x is an endpoint of D. hD\\_inv(x) \\<in> {0, 1}.\<close>
                        hence "\<pi> x = (1, 0)" unfolding \<pi>_def by (by100 simp)
                        have "x \<in> D \<inter> T" using \<open>x \<in> D\<close> True by (by100 blast)
                        have "D \<inter> T \<subseteq> top1_arc_endpoints_on D (subspace_topology Y TY D)"
                          using hT_subgraph[rule_format, OF \<open>D \<in> \<A>\<close>] hD_NT by (by100 blast)
                        have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        have hY_strict_d: "is_topology_on_strict Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hY_haus_d: "is_hausdorff_on Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have harc_D: "top1_is_arc_on D (subspace_topology Y TY D)"
                          using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        from arc_endpoints_are_boundary[OF hY_strict_d hY_haus_d \<open>D \<subseteq> Y\<close> harc_D hhD]
                        have hep_eq: "top1_arc_endpoints_on D (subspace_topology Y TY D) = {hD 0, hD 1}" .
                        have "x \<in> {hD 0, hD 1}"
                          using \<open>x \<in> D \<inter> T\<close> \<open>D \<inter> T \<subseteq> _\<close> hep_eq by (by100 blast)
                        have hD_inj: "inj_on hD top1_unit_interval"
                          using hD_bij unfolding bij_betw_def by (by100 blast)
                        have h0I: "(0::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have h1I: "(1::real) \<in> top1_unit_interval"
                          unfolding top1_unit_interval_def by (by100 simp)
                        have "?hD_inv x \<in> {0::real, 1}"
                        proof -
                          from \<open>x \<in> {hD 0, hD 1}\<close>
                          have "x = hD 0 \<or> x = hD 1" by (by100 blast)
                          thus ?thesis
                          proof
                            assume "x = hD 0"
                            hence "?hD_inv x = 0"
                              using the_inv_into_f_f[OF hD_inj h0I] by simp
                            thus ?thesis by (by100 blast)
                          next
                            assume "x = hD 1"
                            hence "?hD_inv x = 1"
                              using the_inv_into_f_f[OF hD_inj h1I] by simp
                            thus ?thesis by (by100 blast)
                          qed
                        qed
                        hence "?std_loop (?hD_inv x) = (1, 0)"
                        proof
                          assume "?hD_inv x = 0"
                          thus ?thesis by (by100 simp)
                        next
                          assume "?hD_inv x \<in> {1}"
                          hence "?hD_inv x = 1" by (by100 blast)
                          thus ?thesis by (by100 simp)
                        qed
                        thus ?thesis using \<open>\<pi> x = (1, 0)\<close> by simp
                      next
                        case False
                        thus ?thesis unfolding \<pi>_def by (by100 simp)
                      qed
                    qed
                    \<comment> \<open>std\\_loop \\<circ> hD\\_inv is continuous on D.\<close>
                    have h_comp_cont: "top1_continuous_map_on D (subspace_topology Y TY D)
                        top1_S1 top1_S1_topology (\<lambda>x. ?std_loop (?hD_inv x))"
                    proof -
                      \<comment> \<open>hD\\_inv continuous D \\<rightarrow> [0,1] (homeomorphism inverse).\<close>
                      have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                      from homeomorphism_inverse[OF hhD]
                      have hhinv: "top1_homeomorphism_on D (subspace_topology Y TY D)
                          top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval hD)" .
                      have hinv_cont: "top1_continuous_map_on D (subspace_topology Y TY D)
                          top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval hD)"
                        using hhinv unfolding top1_homeomorphism_on_def by (by100 blast)
                      \<comment> \<open>std\\_loop continuous [0,1] \\<rightarrow> S1.\<close>
                      have hstd_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                          top1_S1 top1_S1_topology ?std_loop"
                        using standard_S1_loop_is_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                        by (by100 blast)
                      \<comment> \<open>Composition.\<close>
                      from top1_continuous_map_on_comp[OF hinv_cont hstd_cont]
                      have "top1_continuous_map_on D (subspace_topology Y TY D)
                          top1_S1 top1_S1_topology (?std_loop \<circ> inv_into top1_unit_interval hD)" .
                      \<comment> \<open>the\\_inv\\_into = inv\\_into for injective functions.\<close>
                      moreover have "\<forall>x \<in> D. (\<lambda>x. ?std_loop (?hD_inv x)) x =
                          (?std_loop \<circ> inv_into top1_unit_interval hD) x"
                      proof (intro ballI)
                        fix x assume "x \<in> D"
                        hence "x \<in> hD ` top1_unit_interval"
                          using hD_bij unfolding bij_betw_def by (by100 blast)
                        then obtain t where "t \<in> top1_unit_interval" "hD t = x" by (by100 blast)
                        have hD_inj: "inj_on hD top1_unit_interval"
                          using hD_bij unfolding bij_betw_def by (by100 blast)
                        have "?hD_inv x = t"
                          using the_inv_into_f_f[OF hD_inj \<open>t \<in> top1_unit_interval\<close>]
                              \<open>hD t = x\<close> by simp
                        have "inv_into top1_unit_interval hD x = t"
                          using inv_into_f_f[OF hD_inj \<open>t \<in> top1_unit_interval\<close>]
                              \<open>hD t = x\<close> by simp
                        thus "(\<lambda>x. ?std_loop (?hD_inv x)) x =
                            (?std_loop \<circ> inv_into top1_unit_interval hD) x"
                          using \<open>?hD_inv x = t\<close> \<open>inv_into top1_unit_interval hD x = t\<close>
                          unfolding comp_def by simp
                      qed
                      ultimately show ?thesis
                      proof -
                        assume hcont_inv: "top1_continuous_map_on D (subspace_topology Y TY D)
                            top1_S1 top1_S1_topology (?std_loop \<circ> inv_into top1_unit_interval hD)"
                           and heq: "\<forall>x\<in>D. (\<lambda>x. ?std_loop (?hD_inv x)) x =
                            (?std_loop \<circ> inv_into top1_unit_interval hD) x"
                        show ?thesis unfolding top1_continuous_map_on_def
                        proof (intro conjI ballI)
                          fix x assume "x \<in> D"
                          from hcont_inv[unfolded top1_continuous_map_on_def] \<open>x \<in> D\<close>
                          have "(?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> top1_S1"
                            by (by100 blast)
                          thus "?std_loop (?hD_inv x) \<in> top1_S1"
                            using heq \<open>x \<in> D\<close> by simp
                        next
                          fix V assume "V \<in> top1_S1_topology"
                          have "{x \<in> D. ?std_loop (?hD_inv x) \<in> V} =
                              {x \<in> D. (?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V}"
                          proof (rule set_eqI, rule iffI)
                            fix x assume "x \<in> {x \<in> D. ?std_loop (?hD_inv x) \<in> V}"
                            hence "x \<in> D" "?std_loop (?hD_inv x) \<in> V" by (by100 blast)+
                            hence "(?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V"
                              using heq by simp
                            thus "x \<in> {x \<in> D. (?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V}"
                              using \<open>x \<in> D\<close> by (by100 blast)
                          next
                            fix x assume "x \<in> {x \<in> D. (?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V}"
                            hence "x \<in> D" "(?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V"
                              by (by100 blast)+
                            hence "?std_loop (?hD_inv x) \<in> V"
                              using heq by simp
                            thus "x \<in> {x \<in> D. ?std_loop (?hD_inv x) \<in> V}"
                              using \<open>x \<in> D\<close> by (by100 blast)
                          qed
                          from hcont_inv[unfolded top1_continuous_map_on_def]
                          have "{x \<in> D. (?std_loop \<circ> inv_into top1_unit_interval hD) x \<in> V}
                              \<in> subspace_topology Y TY D"
                            using \<open>V \<in> top1_S1_topology\<close> unfolding comp_def by (by100 blast)
                          thus "{x \<in> D. ?std_loop (?hD_inv x) \<in> V}
                              \<in> subspace_topology Y TY D"
                            using \<open>{x \<in> D. ?std_loop (?hD_inv x) \<in> V} = _\<close> by simp
                        qed
                      qed
                    qed
                    \<comment> \<open>Since \\<pi> = std\\_loop \\<circ> hD\\_inv on D, and the composition is continuous:\<close>
                    have "top1_continuous_map_on D (subspace_topology Y TY D)
                        top1_S1 top1_S1_topology \<pi>"
                    proof -
                      have "\<forall>x \<in> D. \<pi> x = (\<lambda>x. ?std_loop (?hD_inv x)) x"
                        using h\<pi>_eq_on_D by (by100 blast)
                      hence heq_fn: "\<And>x. x \<in> D \<Longrightarrow> \<pi> x = (\<lambda>x. ?std_loop (?hD_inv x)) x"
                        by (by100 blast)
                      hence "{x \<in> D. \<pi> x \<in> V} = {x \<in> D. (\<lambda>x. ?std_loop (?hD_inv x)) x \<in> V}" for V
                        by (by100 auto)
                      thus ?thesis using h_comp_cont unfolding top1_continuous_map_on_def
                        by (by100 auto)
                    qed
                    thus ?thesis using hD_top_eq by simp
                  qed
                  from pasting_lemma_two_closed[OF hTTD_top_g hS1_top_g hT_closed hD_closed
                      hcover[symmetric] h\<pi>_maps_fn h\<pi>_cont_T h\<pi>_cont_D]
                  show ?thesis .
                qed
                have h\<pi>_star_gen: "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0) =
                    top1_subgroup_generated_on
                      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                      (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
                      (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))
                      {top1_fundamental_group_induced_on ?TD ?TTD y0 top1_S1 top1_S1_topology (1,0) \<pi> (\<iota>F D)}"
                proof -
                  let ?\<pi>_star = "top1_fundamental_group_induced_on ?TD ?TTD y0
                      top1_S1 top1_S1_topology (1,0) \<pi>"
                  let ?std_loop = "\<lambda>s::real. (cos (2 * pi * s), sin (2 * pi * s))"
                  let ?std_class = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) ?std_loop g}"
                  \<comment> \<open>Step 1: Extract gen\\_loop structure.\<close>
                  from hgen_loop_structure[rule_format, OF hD_NT]
                  obtain h_arc \<gamma>a' \<gamma>b' where
                    hgl_eq: "gen_loop D = top1_path_product \<gamma>a' (top1_path_product h_arc (top1_path_reverse \<gamma>b'))"
                    and hharc: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology D (subspace_topology Y TY D) h_arc"
                    and h\<gamma>a'_T: "\<gamma>a' ` I_set \<subseteq> T"
                    and h\<gamma>b'_T: "\<gamma>b' ` I_set \<subseteq> T"
                    by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
                  \<comment> \<open>Step 2: \\<pi> \\<circ> gen\\_loop D = (\\<pi>\\<circ>\\<gamma>a') * ((\\<pi>\\<circ>h\\_arc) * (\\<pi>\\<circ>rev(\\<gamma>b'))).\<close>
                  have hcomp_eq: "\<pi> \<circ> gen_loop D =
                      top1_path_product (\<pi> \<circ> \<gamma>a')
                        (top1_path_product (\<pi> \<circ> h_arc) (\<pi> \<circ> top1_path_reverse \<gamma>b'))"
                    using hgl_eq comp_path_product[of \<pi> \<gamma>a' "top1_path_product h_arc (top1_path_reverse \<gamma>b')"]
                      comp_path_product[of \<pi> h_arc "top1_path_reverse \<gamma>b'"]
                    by simp
                  \<comment> \<open>Step 3: \\<pi>\\<circ>\\<gamma>a' and \\<pi>\\<circ>rev(\\<gamma>b') are pointwise constant (1,0) on I\\_set.\<close>
                  have h_const_a: "\<forall>s\<in>I_set. (\<pi> \<circ> \<gamma>a') s = (1::real, 0::real)"
                  proof (intro ballI)
                    fix s assume "s \<in> I_set"
                    hence "\<gamma>a' s \<in> T" using h\<gamma>a'_T by (by100 blast)
                    thus "(\<pi> \<circ> \<gamma>a') s = (1, 0)" unfolding \<pi>_def comp_def by (by100 simp)
                  qed
                  have h_const_b: "\<forall>s\<in>I_set. (\<pi> \<circ> top1_path_reverse \<gamma>b') s = (1::real, 0::real)"
                  proof (intro ballI)
                    fix s assume "s \<in> I_set"
                    hence "1 - s \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                    hence "\<gamma>b' (1 - s) \<in> T" using h\<gamma>b'_T by (by100 blast)
                    thus "(\<pi> \<circ> top1_path_reverse \<gamma>b') s = (1, 0)"
                      unfolding \<pi>_def comp_def top1_path_reverse_def by (by100 simp)
                  qed
                  \<comment> \<open>Step 4: \\<pi>\\<circ>h\\_arc agrees with std\\_loop \\<circ> hD\\_inv \\<circ> h\\_arc on I\\_set.\<close>
                  let ?hD_inv = "the_inv_into top1_unit_interval hD"
                  have h_harc_D: "h_arc ` I_set \<subseteq> D"
                    using hharc unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                  have hD_inj: "inj_on hD top1_unit_interval"
                    using hD_bij unfolding bij_betw_def by (by100 blast)
                  \<comment> \<open>For points in D that are also in T (endpoints), \\<pi> = (1,0) = std\\_loop(0 or 1).\<close>
                  have h\<pi>_harc_eq: "\<forall>s\<in>I_set. (\<pi> \<circ> h_arc) s = (?std_loop (?hD_inv (h_arc s)))"
                  proof (intro ballI)
                    fix s assume hs: "s \<in> I_set"
                    hence "h_arc s \<in> D" using h_harc_D by (by100 blast)
                    show "(\<pi> \<circ> h_arc) s = ?std_loop (?hD_inv (h_arc s))"
                    proof (cases "h_arc s \<in> T")
                      case True
                      hence "(\<pi> \<circ> h_arc) s = (1, 0)" unfolding \<pi>_def comp_def by (by100 simp)
                      \<comment> \<open>h\\_arc s \\<in> T \\<inter> D = endpoints of D, so hD\\_inv(h\\_arc s) \\<in> {0,1}.\<close>
                      moreover have "?hD_inv (h_arc s) \<in> {0, 1}"
                      proof -
                        have "h_arc s \<in> T \<inter> D" using True \<open>h_arc s \<in> D\<close> by (by100 blast)
                        have hep: "T \<inter> D \<subseteq> top1_arc_endpoints_on D (subspace_topology Y TY D)"
                          using hT_subgraph[rule_format, OF \<open>D \<in> \<A>\<close>] hD_NT by (by100 blast)
                        have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        have hY_strict_d: "is_topology_on_strict Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hY_haus_d: "is_hausdorff_on Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have harc_D: "top1_is_arc_on D (subspace_topology Y TY D)"
                          using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        from arc_endpoints_are_boundary[OF hY_strict_d hY_haus_d \<open>D \<subseteq> Y\<close> harc_D hhD]
                        have hep_eq: "top1_arc_endpoints_on D (subspace_topology Y TY D) = {hD 0, hD 1}" .
                        hence "h_arc s \<in> {hD 0, hD 1}" using hep \<open>h_arc s \<in> T \<inter> D\<close> by (by100 blast)
                        hence "h_arc s = hD 0 \<or> h_arc s = hD 1" by (by100 blast)
                        thus ?thesis
                        proof
                          assume heq0: "h_arc s = hD 0"
                          have h0I: "0 \<in> top1_unit_interval"
                            unfolding top1_unit_interval_def by (by100 simp)
                          have "?hD_inv (hD 0) = 0"
                            using the_inv_into_f_f[OF hD_inj h0I] by simp
                          hence "?hD_inv (h_arc s) = 0" using heq0 by simp
                          thus ?thesis by (by100 blast)
                        next
                          assume heq1: "h_arc s = hD 1"
                          have h1I: "1 \<in> top1_unit_interval"
                            unfolding top1_unit_interval_def by (by100 simp)
                          have "?hD_inv (hD 1) = 1"
                            using the_inv_into_f_f[OF hD_inj h1I] by simp
                          hence "?hD_inv (h_arc s) = 1" using heq1 by simp
                          thus ?thesis by (by100 simp)
                        qed
                      qed
                      moreover have hstd0: "?std_loop 0 = (1::real, 0)" by (by100 simp)
                      moreover have hstd1: "?std_loop 1 = (1::real, 0)" by (by100 simp)
                      ultimately have h_inv_01: "?hD_inv (h_arc s) = 0 \<or> ?hD_inv (h_arc s) = 1"
                        by (by100 blast)
                      have "?std_loop (?hD_inv (h_arc s)) = (1, 0)"
                        using h_inv_01 hstd0 hstd1 by (by100 auto)
                      moreover have "(\<pi> \<circ> h_arc) s = (1, 0)"
                        using \<open>h_arc s \<in> T\<close> unfolding \<pi>_def comp_def by (by100 simp)
                      ultimately show ?thesis by simp
                    next
                      case False
                      thus ?thesis unfolding \<pi>_def comp_def by (by100 simp)
                    qed
                  qed
                  \<comment> \<open>Step 5: \\<pi> \\<circ> gen\\_loop D is path-homotopic to \\<pm>std\\_loop in S1.\<close>
                  \<comment> \<open>Overall strategy: [\\<pi>\\<circ>gen\\_loop D] = \\<pm>[std\\_loop], hence generates.\<close>
                  have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
                    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def
                    by (by100 blast)
                  have hgenD_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> gen_loop D)"
                  proof -
                    have hgl_cont: "top1_continuous_map_on I_set I_top ?TD ?TTD (gen_loop D)"
                      using hgenD_loop_TD unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)
                    have hcomp_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology
                        (\<pi> \<circ> gen_loop D)"
                      by (rule top1_continuous_map_on_comp[OF hgl_cont h\<pi>_cont])
                    have "gen_loop D 0 = y0"
                      using hgenD_loop_TD unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)
                    hence "(\<pi> \<circ> gen_loop D) 0 = \<pi> y0" unfolding comp_def by simp
                    hence h0: "(\<pi> \<circ> gen_loop D) 0 = (1, 0)"
                      unfolding \<pi>_def using hT_x0 by (by100 simp)
                    have "gen_loop D 1 = y0"
                      using hgenD_loop_TD unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)
                    hence "(\<pi> \<circ> gen_loop D) 1 = \<pi> y0" unfolding comp_def by simp
                    hence h1: "(\<pi> \<circ> gen_loop D) 1 = (1, 0)"
                      unfolding \<pi>_def using hT_x0 by (by100 simp)
                    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                      using hcomp_cont h0 h1 by (by100 blast)
                  qed
                  have h\<pi>_genD_htpy:
                    "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> gen_loop D) ?std_loop
                    \<or> top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> gen_loop D)
                        (top1_path_reverse ?std_loop)"
                  proof -
                    have hS1_top_loc: "is_topology_on top1_S1 top1_S1_topology"
                      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def
                      by (by100 blast)
                    \<comment> \<open>\\<pi>\\<circ>h\\_arc is a path in S1 from (1,0) to (1,0).\<close>
                    have h\<pi>harc_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc)"
                    proof -
                      have harc_cont: "top1_continuous_map_on I_set I_top ?TD ?TTD h_arc"
                      proof -
                        have hD_cont: "top1_continuous_map_on I_set I_top D (subspace_topology Y TY D) h_arc"
                          using hharc unfolding top1_homeomorphism_on_def by (by100 blast)
                        have hD_sub_TD: "D \<subseteq> ?TD" by (by100 blast)
                        have hTD_sub_Y: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        have hTY: "is_topology_on Y TY"
                          using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                        have hTTD_top: "is_topology_on ?TD ?TTD"
                          by (rule subspace_topology_is_topology_on[OF hTY hTD_sub_Y])
                        have hI_top: "is_topology_on I_set I_top"
                          by (rule top1_unit_interval_topology_is_topology_on)
                        have "h_arc ` I_set \<subseteq> ?TD" using h_harc_D hD_sub_TD by (by100 blast)
                        \<comment> \<open>h\\_arc: [0,1] \\<rightarrow> D continuous in (D, sub Y TY D).
                           Since D \\<subseteq> TD, image \\<subseteq> TD.
                           Use restrict\\_range(5) on [0,1] \\<rightarrow> Y (via composition with inclusion)
                           to get [0,1] \\<rightarrow> TD.\<close>
                        \<comment> \<open>Alternative: h\\_arc continuous to Y (via D \\<subseteq> Y) then restrict.\<close>
                        have hD_sub_Y: "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        have harc_cont_Y: "top1_continuous_map_on I_set I_top Y TY h_arc"
                        proof -
                          from Theorem_18_2(6)[OF hI_top
                              subspace_topology_is_topology_on[OF hTY hD_sub_Y] hTY,
                              rule_format]
                          show ?thesis using hD_cont hD_sub_Y by (by100 blast)
                        qed
                        from Theorem_18_2(5)[OF hI_top hTY hTTD_top, rule_format]
                        show ?thesis using harc_cont_Y hTD_sub_Y \<open>h_arc ` I_set \<subseteq> ?TD\<close>
                          by (by100 blast)
                      qed
                      have hcomp: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (\<pi> \<circ> h_arc)"
                        by (rule top1_continuous_map_on_comp[OF harc_cont h\<pi>_cont])
                      have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      \<comment> \<open>h\\_arc(0) and h\\_arc(1) are endpoints of D, hence in T.\<close>
                      have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                      have hY_strict: "is_topology_on_strict Y TY"
                        using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                      have hY_haus: "is_hausdorff_on Y TY"
                        using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                      have harc_D_loc: "top1_is_arc_on D (subspace_topology Y TY D)"
                        using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                      from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>D \<subseteq> Y\<close> harc_D_loc hharc]
                      have hep_eq_loc: "top1_arc_endpoints_on D (subspace_topology Y TY D) = {h_arc 0, h_arc 1}" .
                      have hT_ep: "T \<inter> D \<subseteq> top1_arc_endpoints_on D (subspace_topology Y TY D)"
                        using hT_subgraph[rule_format, OF \<open>D \<in> \<A>\<close>] hD_NT by (by100 blast)
                      have hep_in_T: "h_arc 0 \<in> T \<and> h_arc 1 \<in> T"
                      proof -
                        have "h_arc 0 \<in> D" using h_harc_D h0I by (by100 blast)
                        have "h_arc 1 \<in> D" using h_harc_D h1I by (by100 blast)
                        have "h_arc 0 \<in> top1_arc_endpoints_on D (subspace_topology Y TY D)"
                          using hep_eq_loc by (by100 blast)
                        have "h_arc 1 \<in> top1_arc_endpoints_on D (subspace_topology Y TY D)"
                          using hep_eq_loc by (by100 blast)
                        \<comment> \<open>Endpoints of D are in T (from graph structure: arc endpoints are vertices).\<close>
                        have "top1_arc_endpoints_on D (subspace_topology Y TY D) \<subseteq> T"
                        proof -
                          have "D \<in> {A \<in> \<A>. \<not> A \<subseteq> T}" using \<open>D \<in> \<A>\<close> hD_NT by (by100 blast)
                          from hNT_endpoints[rule_format, OF this]
                          show ?thesis by (by100 blast)
                        qed
                        thus ?thesis using hep_eq_loc by (by100 blast)
                      qed
                      have h0: "(\<pi> \<circ> h_arc) 0 = (1, 0)"
                        using hep_in_T unfolding \<pi>_def comp_def by (by100 simp)
                      have h1: "(\<pi> \<circ> h_arc) 1 = (1, 0)"
                        using hep_in_T unfolding \<pi>_def comp_def by (by100 simp)
                      show ?thesis unfolding top1_is_path_on_def using hcomp h0 h1 by (by100 blast)
                    qed
                    \<comment> \<open>\\<pi>\\<circ>\\<gamma>a' is a constant path at (1,0).\<close>
                    have h\<pi>ga_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> \<gamma>a')"
                    proof -
                      have h10_S1: "(1::real, 0::real) \<in> top1_S1"
                        unfolding top1_S1_def by (by100 simp)
                      have hcont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (\<pi> \<circ> \<gamma>a')"
                        unfolding top1_continuous_map_on_def
                      proof (intro conjI ballI)
                        fix s assume "s \<in> I_set"
                        hence "(\<pi> \<circ> \<gamma>a') s = (1, 0)" using h_const_a by (by100 blast)
                        thus "(\<pi> \<circ> \<gamma>a') s \<in> top1_S1" using h10_S1 by simp
                      next
                        fix V assume "V \<in> top1_S1_topology"
                        show "{s \<in> I_set. (\<pi> \<circ> \<gamma>a') s \<in> V} \<in> I_top"
                        proof (cases "(1::real, 0::real) \<in> V")
                          case True
                          hence "\<And>s. s \<in> I_set \<Longrightarrow> (\<pi> \<circ> \<gamma>a') s \<in> V"
                            using h_const_a by (by100 auto)
                          hence "{s \<in> I_set. (\<pi> \<circ> \<gamma>a') s \<in> V} = I_set" by (by100 blast)
                          moreover have "I_set \<in> I_top"
                            using top1_unit_interval_topology_is_topology_on
                            unfolding is_topology_on_def by (by100 blast)
                          ultimately show ?thesis by simp
                        next
                          case False
                          hence "\<And>s. s \<in> I_set \<Longrightarrow> (\<pi> \<circ> \<gamma>a') s \<notin> V"
                            using h_const_a by (by100 auto)
                          hence "\<And>s. s \<in> I_set \<Longrightarrow> (\<pi> \<circ> \<gamma>a') s \<notin> V"
                            by (by100 blast)
                          hence heq_empty: "{s \<in> I_set. (\<pi> \<circ> \<gamma>a') s \<in> V} = {}" by (by100 blast)
                          have hempty_top: "{} \<in> I_top"
                            using top1_unit_interval_topology_is_topology_on[unfolded is_topology_on_def]
                            by (by5000 auto)
                          show ?thesis by (subst heq_empty, rule hempty_top)
                        qed
                      qed
                      have h0I_g: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      have h1I_g: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      have hep0: "(\<pi> \<circ> \<gamma>a') 0 = (1, 0)"
                        using h_const_a h0I_g by (by100 blast)
                      have hep1: "(\<pi> \<circ> \<gamma>a') 1 = (1, 0)"
                        using h_const_a h1I_g by (by100 blast)
                      show ?thesis unfolding top1_is_path_on_def using hcont hep0 hep1 by (by100 blast)
                    qed
                    \<comment> \<open>\\<pi>\\<circ>rev(\\<gamma>b') is a constant path at (1,0).\<close>
                    have h\<pi>gb_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                        (\<pi> \<circ> top1_path_reverse \<gamma>b')"
                    proof -
                      have h10_S1: "(1::real, 0::real) \<in> top1_S1"
                        unfolding top1_S1_def by (by100 simp)
                      have hcont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology
                          (\<pi> \<circ> top1_path_reverse \<gamma>b')"
                        unfolding top1_continuous_map_on_def
                      proof (intro conjI ballI)
                        fix s assume "s \<in> I_set"
                        hence "(\<pi> \<circ> top1_path_reverse \<gamma>b') s = (1, 0)"
                          using h_const_b by (by100 blast)
                        thus "(\<pi> \<circ> top1_path_reverse \<gamma>b') s \<in> top1_S1" using h10_S1 by simp
                      next
                        fix V assume "V \<in> top1_S1_topology"
                        show "{s \<in> I_set. (\<pi> \<circ> top1_path_reverse \<gamma>b') s \<in> V} \<in> I_top"
                        proof (cases "(1::real, 0::real) \<in> V")
                          case True
                          hence "\<And>s. s \<in> I_set \<Longrightarrow> (\<pi> \<circ> top1_path_reverse \<gamma>b') s \<in> V"
                            using h_const_b by (by100 auto)
                          hence "{s \<in> I_set. (\<pi> \<circ> top1_path_reverse \<gamma>b') s \<in> V} = I_set"
                            by (by100 blast)
                          moreover have "I_set \<in> I_top"
                            using top1_unit_interval_topology_is_topology_on
                            unfolding is_topology_on_def by (by100 blast)
                          ultimately show ?thesis by simp
                        next
                          case False
                          hence "\<And>s. s \<in> I_set \<Longrightarrow> (\<pi> \<circ> top1_path_reverse \<gamma>b') s \<notin> V"
                            using h_const_b by (by100 auto)
                          hence heq_empty_b: "{s \<in> I_set. (\<pi> \<circ> top1_path_reverse \<gamma>b') s \<in> V} = {}"
                            by (by100 blast)
                          have hempty_top_b: "{} \<in> I_top"
                            using top1_unit_interval_topology_is_topology_on[unfolded is_topology_on_def]
                            by (by5000 auto)
                          show ?thesis by (subst heq_empty_b, rule hempty_top_b)
                        qed
                      qed
                      have h0I_h: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      have h1I_h: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                      have hep0: "(\<pi> \<circ> top1_path_reverse \<gamma>b') 0 = (1, 0)"
                        using h_const_b h0I_h by (by100 blast)
                      have hep1: "(\<pi> \<circ> top1_path_reverse \<gamma>b') 1 = (1, 0)"
                        using h_const_b h1I_h by (by100 blast)
                      show ?thesis unfolding top1_is_path_on_def using hcont hep0 hep1 by (by100 blast)
                    qed
                    \<comment> \<open>\\<pi>\\<circ>h\\_arc \\<simeq> \\<pm>std\\_loop via reparametrization.\<close>
                    have h\<pi>harc_htpy:
                      "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc) ?std_loop
                      \<or> top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc)
                          (top1_path_reverse ?std_loop)"
                    proof -
                      let ?reparam = "\<lambda>s. ?hD_inv (h_arc s)"
                      \<comment> \<open>\\<pi>\\<circ>h\\_arc agrees with std\\_loop\\<circ>reparam on I\\_set.\<close>
                      have h_agree_reparam: "\<forall>s\<in>I_set. (\<pi> \<circ> h_arc) s = (?std_loop \<circ> ?reparam) s"
                        using h\<pi>_harc_eq unfolding comp_def by simp
                      \<comment> \<open>reparam: I\\_set \\<rightarrow> I\\_set continuous.\<close>
                      have h_reparam_cont: "top1_continuous_map_on I_set I_top I_set I_top ?reparam"
                      proof -
                        \<comment> \<open>h\\_arc: [0,1] \\<rightarrow> D homeomorphism (hence continuous).\<close>
                        have harc_cont_D: "top1_continuous_map_on I_set I_top D (subspace_topology Y TY D) h_arc"
                          using hharc unfolding top1_homeomorphism_on_def by (by100 blast)
                        \<comment> \<open>hD\\<inverse>: D \\<rightarrow> [0,1] continuous (homeomorphism inverse).\<close>
                        from homeomorphism_inverse[OF hhD]
                        have "top1_homeomorphism_on D (subspace_topology Y TY D) I_set I_top (inv_into I_set hD)" .
                        hence hinv_cont: "top1_continuous_map_on D (subspace_topology Y TY D) I_set I_top
                            (inv_into I_set hD)"
                          unfolding top1_homeomorphism_on_def by (by100 blast)
                        \<comment> \<open>the\\_inv\\_into = inv\\_into for injective.\<close>
                        have h_eq_inv: "\<forall>x\<in>D. ?hD_inv x = inv_into I_set hD x"
                        proof (intro ballI)
                          fix x assume "x \<in> D"
                          hence "x \<in> hD ` I_set"
                            using hD_bij unfolding bij_betw_def by (by100 blast)
                          then obtain t where ht: "t \<in> I_set" "hD t = x" by (by100 blast)
                          have "?hD_inv x = t"
                            using the_inv_into_f_f[OF hD_inj ht(1)] ht(2) by simp
                          moreover have "inv_into I_set hD x = t"
                            using inv_into_f_f[OF hD_inj ht(1)] ht(2) by simp
                          ultimately show "?hD_inv x = inv_into I_set hD x" by simp
                        qed
                        \<comment> \<open>Composition: h\\_arc then hD\\<inverse>.\<close>
                        have h_comp: "top1_continuous_map_on I_set I_top I_set I_top
                            (inv_into I_set hD \<circ> h_arc)"
                          by (rule top1_continuous_map_on_comp[OF harc_cont_D hinv_cont])
                        \<comment> \<open>?reparam agrees with inv\\_into \\<circ> h\\_arc on I\\_set.\<close>
                        have "\<forall>s\<in>I_set. ?reparam s = (inv_into I_set hD \<circ> h_arc) s"
                        proof (intro ballI)
                          fix s assume "s \<in> I_set"
                          hence "h_arc s \<in> D" using h_harc_D by (by100 blast)
                          thus "?reparam s = (inv_into I_set hD \<circ> h_arc) s"
                            using h_eq_inv unfolding comp_def by (by100 blast)
                        qed
                        \<comment> \<open>Same continuity since they agree on I\\_set.\<close>
                        show ?thesis unfolding top1_continuous_map_on_def
                        proof (intro conjI ballI)
                          fix s assume "s \<in> I_set"
                          thus "?reparam s \<in> I_set"
                            using h_comp \<open>\<forall>s\<in>I_set. ?reparam s = (inv_into I_set hD \<circ> h_arc) s\<close>
                            unfolding top1_continuous_map_on_def by (by100 auto)
                        next
                          fix V assume "V \<in> I_top"
                          have "{s \<in> I_set. ?reparam s \<in> V} = {s \<in> I_set. (inv_into I_set hD \<circ> h_arc) s \<in> V}"
                            using \<open>\<forall>s\<in>I_set. ?reparam s = (inv_into I_set hD \<circ> h_arc) s\<close> by (by100 auto)
                          thus "{s \<in> I_set. ?reparam s \<in> V} \<in> I_top"
                            using h_comp \<open>V \<in> I_top\<close> unfolding top1_continuous_map_on_def by (by100 auto)
                        qed
                      qed
                      have h_reparam_range: "\<forall>s\<in>I_set. ?reparam s \<in> I_set"
                        using h_reparam_cont unfolding top1_continuous_map_on_def by (by100 blast)
                      \<comment> \<open>Endpoint analysis.\<close>
                      have h_reparam_endpoints: "(?reparam 0 = 0 \<and> ?reparam 1 = 1)
                          \<or> (?reparam 0 = 1 \<and> ?reparam 1 = 0)"
                      proof -
                        \<comment> \<open>From arc\\_endpoints\\_are\\_boundary for both homeomorphisms:\<close>
                        have "D \<subseteq> Y" using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        have hY_strict_ep: "is_topology_on_strict Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hY_haus_ep: "is_hausdorff_on Y TY"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have harc_D_ep: "top1_is_arc_on D (subspace_topology Y TY D)"
                          using h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                        \<comment> \<open>endpoints(D) = {hD(0), hD(1)} = {h\\_arc(0), h\\_arc(1)}.\<close>
                        from arc_endpoints_are_boundary[OF hY_strict_ep hY_haus_ep \<open>D \<subseteq> Y\<close> harc_D_ep hhD]
                        have "top1_arc_endpoints_on D (subspace_topology Y TY D) = {hD 0, hD 1}" .
                        from arc_endpoints_are_boundary[OF hY_strict_ep hY_haus_ep \<open>D \<subseteq> Y\<close> harc_D_ep hharc]
                        have "top1_arc_endpoints_on D (subspace_topology Y TY D) = {h_arc 0, h_arc 1}" .
                        hence h_ep_eq: "{hD 0, hD 1} = {h_arc 0, h_arc 1}"
                          using \<open>top1_arc_endpoints_on D _ = {hD 0, hD 1}\<close> by simp
                        \<comment> \<open>hD\\_inv maps hD(0)\\<mapsto>0 and hD(1)\\<mapsto>1.\<close>
                        have hrep_harc0: "?reparam 0 = ?hD_inv (h_arc 0)" by simp
                        have hrep_harc1: "?reparam 1 = ?hD_inv (h_arc 1)" by simp
                        have h0I_ep: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        have h1I_ep: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        have hhD0_inv: "?hD_inv (hD 0) = 0"
                          using the_inv_into_f_f[OF hD_inj h0I_ep] by simp
                        have hhD1_inv: "?hD_inv (hD 1) = 1"
                          using the_inv_into_f_f[OF hD_inj h1I_ep] by simp
                        \<comment> \<open>h\\_arc(0) \\<in> {hD(0), hD(1)} and h\\_arc(1) \\<in> {hD(0), hD(1)}.\<close>
                        from h_ep_eq have "h_arc 0 \<in> {hD 0, hD 1} \<and> h_arc 1 \<in> {hD 0, hD 1}"
                          by (by100 blast)
                        hence "(h_arc 0 = hD 0 \<and> h_arc 1 = hD 1) \<or> (h_arc 0 = hD 1 \<and> h_arc 1 = hD 0)"
                        proof -
                          from h_ep_eq have "h_arc 0 = hD 0 \<or> h_arc 0 = hD 1" by (by100 blast)
                          moreover from h_ep_eq have "h_arc 1 = hD 0 \<or> h_arc 1 = hD 1" by (by100 blast)
                          moreover have "h_arc 0 \<noteq> h_arc 1"
                          proof -
                            have "bij_betw h_arc I_set D"
                              using hharc unfolding top1_homeomorphism_on_def by (by100 blast)
                            hence "inj_on h_arc I_set" unfolding bij_betw_def by (by100 blast)
                            moreover have "(0::real) \<noteq> (1::real)" by (by100 simp)
                            ultimately show ?thesis using h0I_ep h1I_ep unfolding inj_on_def by (by100 blast)
                          qed
                          ultimately show ?thesis by (by5000 metis)
                        qed
                        from this show ?thesis
                        proof (elim disjE conjE)
                          assume h0eq: "h_arc 0 = hD 0" and h1eq: "h_arc 1 = hD 1"
                          have "?reparam 0 = 0" using h0eq hhD0_inv by simp
                          moreover have "?reparam 1 = 1" using h1eq hhD1_inv by simp
                          ultimately show ?thesis by (by100 blast)
                        next
                          assume h0eq: "h_arc 0 = hD 1" and h1eq: "h_arc 1 = hD 0"
                          have "?reparam 0 = 1" using h0eq hhD1_inv by simp
                          moreover have "?reparam 1 = 0" using h1eq hhD0_inv by simp
                          ultimately show ?thesis by (by100 blast)
                        qed
                      qed
                      \<comment> \<open>std\\_loop continuous and maps I\\_set to S1.\<close>
                      have hstd_cont_loc: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?std_loop"
                        using standard_S1_loop_is_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                        by (by100 blast)
                      have hstd_range_loc: "\<forall>s\<in>I_set. ?std_loop s \<in> top1_S1"
                        using hstd_cont_loc unfolding top1_continuous_map_on_def by (by100 blast)
                      have hS1_sub_self: "subspace_topology top1_S1 top1_S1_topology top1_S1 = top1_S1_topology"
                      proof -
                        have "\<forall>U\<in>top1_S1_topology. U \<subseteq> top1_S1"
                          using top1_S1_is_topology_on_strict
                          unfolding is_topology_on_strict_def by (by100 blast)
                        from subspace_topology_self[OF this] show ?thesis .
                      qed
                      have hS1_top_S1: "is_topology_on top1_S1 (subspace_topology top1_S1 top1_S1_topology top1_S1)"
                        using hS1_top_loc hS1_sub_self by simp
                      have h0I_loc: "(0::real) \<in> I_set"
                        unfolding top1_unit_interval_def by (by100 simp)
                      have h1I_loc: "(1::real) \<in> I_set"
                        unfolding top1_unit_interval_def by (by100 simp)
                      have hI_top_loc: "is_topology_on I_set I_top"
                        by (rule top1_unit_interval_topology_is_topology_on)
                      have h_id_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. t)"
                        unfolding top1_continuous_map_on_def
                      proof (intro conjI ballI)
                        fix s assume "s \<in> I_set" thus "s \<in> I_set" .
                      next
                        fix V assume hV: "V \<in> I_top"
                        \<comment> \<open>V \\<subseteq> I\\_set since I\\_top = subspace topology.\<close>
                        have "V \<subseteq> I_set"
                          using hV unfolding top1_unit_interval_topology_def subspace_topology_def
                          by (by100 auto)
                        hence "{s \<in> I_set. s \<in> V} = V" by (by100 blast)
                        thus "{s \<in> I_set. s \<in> V} \<in> I_top" using hV by simp
                      qed
                      have h_rev_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t::real. 1 - t)"
                        by (rule op_minus_continuous_on_interval)
                      from h_reparam_endpoints show ?thesis
                      proof
                        assume hep: "?reparam 0 = 0 \<and> ?reparam 1 = 1"
                        \<comment> \<open>reparam\\_path\\_homotopy: std\\<circ>reparam \\<simeq> std\\<circ>id.\<close>
                        have hid0: "(\<lambda>t::real. t) 0 = (0::real)" by (by100 simp)
                        have hid1: "(\<lambda>t::real. t) 1 = (1::real)" by (by100 simp)
                        have hrp0f: "?reparam 0 = (0::real)" using hep by (by100 blast)
                        have hrp1f: "?reparam 1 = (1::real)" using hep by (by100 blast)
                        from reparam_path_homotopy[OF hS1_top_loc hstd_cont_loc hstd_range_loc subset_refl
                            hS1_top_S1 h_reparam_cont h_id_cont hrp0f hrp1f hid0 hid1 h0I_loc h1I_loc]
                        have "top1_path_homotopic_on top1_S1 (subspace_topology top1_S1 top1_S1_topology top1_S1)
                            (?std_loop 0) (?std_loop 1) (?std_loop \<circ> ?reparam) (?std_loop \<circ> (\<lambda>t. t))" .
                        moreover have "?std_loop 0 = (1::real, 0)" by (by100 simp)
                        moreover have "?std_loop 1 = (1::real, 0)" by (by100 simp)
                        moreover have "?std_loop \<circ> (\<lambda>t. t) = ?std_loop" by (rule ext) (simp add: comp_def)
                        moreover have "subspace_topology top1_S1 top1_S1_topology top1_S1 = top1_S1_topology"
                          using hS1_sub_self .
                        ultimately have hreparam_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                            (?std_loop \<circ> ?reparam) ?std_loop"
                          by simp
                        \<comment> \<open>\\<pi>\\<circ>h\\_arc agrees with std\\<circ>reparam on I\\_set.\<close>
                        from paths_agree_on_I_path_homotopic[OF hS1_top_loc h\<pi>harc_path h_agree_reparam]
                        have "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc) (?std_loop \<circ> ?reparam)" .
                        from Lemma_51_1_path_homotopic_trans[OF hS1_top_loc this hreparam_htpy]
                        show ?thesis by (by100 blast)
                      next
                        assume hep: "?reparam 0 = 1 \<and> ?reparam 1 = 0"
                        have hrev0: "(\<lambda>t::real. 1 - t) 0 = (1::real)" by (by100 simp)
                        have hrev1: "(\<lambda>t::real. 1 - t) 1 = (0::real)" by (by100 simp)
                        have hrp0: "?reparam 0 = (1::real)" using hep by (by100 blast)
                        have hrp1: "?reparam 1 = (0::real)" using hep by (by100 blast)
                        from reparam_path_homotopy[OF hS1_top_loc hstd_cont_loc hstd_range_loc subset_refl
                            hS1_top_S1 h_reparam_cont h_rev_cont hrp0 hrp1 hrev0 hrev1 h1I_loc h0I_loc]
                        have "top1_path_homotopic_on top1_S1 (subspace_topology top1_S1 top1_S1_topology top1_S1)
                            (?std_loop 1) (?std_loop 0) (?std_loop \<circ> ?reparam) (?std_loop \<circ> (\<lambda>t::real. 1 - t))" .
                        moreover have "?std_loop 0 = (1::real, 0)" by (by100 simp)
                        moreover have "?std_loop 1 = (1::real, 0)" by (by100 simp)
                        moreover have "?std_loop \<circ> (\<lambda>t::real. 1 - t) = top1_path_reverse ?std_loop"
                          unfolding top1_path_reverse_def by (rule ext) (simp add: comp_def)
                        moreover have "subspace_topology top1_S1 top1_S1_topology top1_S1 = top1_S1_topology"
                          using hS1_sub_self .
                        ultimately have hreparam_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                            (?std_loop \<circ> ?reparam) (top1_path_reverse ?std_loop)"
                          by simp
                        from paths_agree_on_I_path_homotopic[OF hS1_top_loc h\<pi>harc_path h_agree_reparam]
                        have "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc) (?std_loop \<circ> ?reparam)" .
                        from Lemma_51_1_path_homotopic_trans[OF hS1_top_loc this hreparam_htpy]
                        show ?thesis by (by100 blast)
                      qed
                    qed
                    \<comment> \<open>\\<pi> \\<circ> gen\\_loop D = const\\_10 * ((\\<pi>\\<circ>h\\_arc) * const\\_10).
                       By hcomp\\_eq + the constant path facts.\<close>
                    \<comment> \<open>Homotopy chain: const * (h * const) \\<simeq> h (left+right identity).\<close>
                    from h\<pi>harc_htpy show ?thesis
                    proof
                      assume hhtpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc) ?std_loop"
                      \<comment> \<open>const * ((\\<pi>\\<circ>h\\_arc) * const) \\<simeq> const * (std * const)
                         \\<simeq> const * std \\<simeq> std.\<close>
                      have h1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> h_arc) (\<pi> \<circ> top1_path_reverse \<gamma>b'))
                          (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b'))"
                        by (rule path_homotopic_product_left[OF hS1_top_loc hhtpy h\<pi>gb_path])
                      have h2: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (\<pi> \<circ> h_arc) (\<pi> \<circ> top1_path_reverse \<gamma>b')))
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        by (rule path_homotopic_product_right[OF hS1_top_loc h1 h\<pi>ga_path])
                      \<comment> \<open>Now use left/right identity to simplify const*std*const \\<rightarrow> std.\<close>
                      \<comment> \<open>Chain: \\<pi>\\<circ>gen\\_loop D = LHS (hcomp\\_eq), LHS \\<simeq> RHS (h2),
                         RHS agrees on I\\_set with const*(std*const), which \\<simeq> std.\<close>
                      have hstd_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0) ?std_loop"
                        using standard_S1_loop_is_loop unfolding top1_is_loop_on_def by (by100 blast)
                      \<comment> \<open>const(1,0) * (std * const(1,0)) \\<simeq> const(1,0) * std \\<simeq> std.\<close>
                      have h_right_id: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product ?std_loop (top1_constant_path (1,0))) ?std_loop"
                        by (rule Theorem_51_2_right_identity[OF hS1_top_loc hstd_path])
                      have h_left_id: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0)) ?std_loop) ?std_loop"
                        by (rule Theorem_51_2_left_identity[OF hS1_top_loc hstd_path])
                      \<comment> \<open>const * (std * const) \\<simeq> const * std (product\\_left with right\\_id).\<close>
                      have h10_in_S1: "(1::real, 0::real) \<in> top1_S1"
                        unfolding top1_S1_def by (by100 simp)
                      have h_prod_const: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_constant_path (1::real, 0))"
                        by (rule top1_constant_path_is_path[OF hS1_top_loc h10_in_S1])
                      have h_inner: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))))
                          (top1_path_product (top1_constant_path (1,0)) ?std_loop)"
                        by (rule path_homotopic_product_right[OF hS1_top_loc h_right_id h_prod_const])
                      \<comment> \<open>Use transitivity: const*(std*const) \\<simeq> const*std \\<simeq> std.\<close>
                      have h_chain: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))))
                          ?std_loop"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_inner h_left_id])
                      \<comment> \<open>RHS of h2 agrees on I\\_set with const*(std*const).\<close>
                      have h_agree: "\<forall>s\<in>I_set.
                          top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')) s =
                          top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))) s"
                      proof (intro ballI)
                        fix s :: real assume hs: "s \<in> I_set"
                        show "top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')) s =
                            top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))) s"
                        proof (cases "s \<le> 1/2")
                          case True
                          hence h2s: "2 * s \<in> I_set"
                            using hs unfolding top1_unit_interval_def by (by100 simp)
                          have "(\<pi> \<circ> \<gamma>a') (2*s) = (1, 0)" using h_const_a h2s by (by100 blast)
                          moreover have "top1_constant_path (1::real, 0) (2*s) = (1, 0)"
                            unfolding top1_constant_path_def by simp
                          ultimately show ?thesis
                            unfolding top1_path_product_def top1_constant_path_def using True by simp
                        next
                          case False
                          hence hs_gt: "s > 1/2" by simp
                          hence h2sm1: "2 * s - 1 \<in> I_set"
                            using hs unfolding top1_unit_interval_def by (by100 simp)
                          \<comment> \<open>Inner product: same std\\_loop factor, different second factor.\<close>
                          show ?thesis
                          proof (cases "2*s - 1 \<le> 1/2")
                            case True
                            \<comment> \<open>Both evaluate to std\\_loop(2*(2s-1)).\<close>
                            show ?thesis
                              unfolding top1_path_product_def top1_constant_path_def
                              using hs_gt True by simp
                          next
                            case False
                            hence h_inner_gt: "2*s - 1 > 1/2" by simp
                            have h_arg: "2*(2*s - 1) - 1 \<in> I_set"
                              using hs h_inner_gt unfolding top1_unit_interval_def by (by100 simp)
                            have "(\<pi> \<circ> top1_path_reverse \<gamma>b') (2*(2*s-1)-1) = (1, 0)"
                              using h_const_b h_arg by (by100 blast)
                            moreover have "top1_constant_path (1::real, 0) (2*(2*s-1)-1) = (1, 0)"
                              unfolding top1_constant_path_def by simp
                            ultimately show ?thesis
                              unfolding top1_path_product_def top1_constant_path_def
                              using hs_gt h_inner_gt by simp
                          qed
                        qed
                      qed
                      \<comment> \<open>So RHS of h2 is path-homotopic to const*(std*const) \\<simeq> std.\<close>
                      have hstd_gb_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b'))"
                        by (rule top1_path_product_is_path[OF hS1_top_loc hstd_path h\<pi>gb_path])
                      have h_rhs_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        by (rule top1_path_product_is_path[OF hS1_top_loc h\<pi>ga_path hstd_gb_path])
                      from paths_agree_on_I_path_homotopic[OF hS1_top_loc h_rhs_path h_agree]
                      have h_agree_htpy: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')))
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))))" .
                      \<comment> \<open>Full chain: \\<pi>\\<circ>gen\\_loop D = LHS (hcomp\\_eq) \\<simeq> RHS (h2) \\<simeq> const*(std*const) \\<simeq> std.\<close>
                      \<comment> \<open>Transitivity chain.\<close>
                      have h_step1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product ?std_loop (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        using h2 hcomp_eq by simp
                      have h_step2: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D)
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product ?std_loop (top1_constant_path (1,0))))"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_step1 h_agree_htpy])
                      have h3: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D) ?std_loop"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_step2 h_chain])
                      thus ?thesis by (by100 blast)
                    next
                      assume hhtpy_rev: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) (\<pi> \<circ> h_arc)
                          (top1_path_reverse ?std_loop)"
                      \<comment> \<open>Same chain as forward case but with rev(std\\_loop).\<close>
                      have hrev_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_reverse ?std_loop)"
                      proof -
                        have hstd_path_r: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0) ?std_loop"
                          using standard_S1_loop_is_loop unfolding top1_is_loop_on_def by (by100 blast)
                        from top1_path_reverse_is_path[OF this] show ?thesis .
                      qed
                      have h1r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> h_arc) (\<pi> \<circ> top1_path_reverse \<gamma>b'))
                          (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b'))"
                        by (rule path_homotopic_product_left[OF hS1_top_loc hhtpy_rev h\<pi>gb_path])
                      have h2r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (\<pi> \<circ> h_arc) (\<pi> \<circ> top1_path_reverse \<gamma>b')))
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        by (rule path_homotopic_product_right[OF hS1_top_loc h1r h\<pi>ga_path])
                      have h_right_id_r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0)))
                          (top1_path_reverse ?std_loop)"
                        by (rule Theorem_51_2_right_identity[OF hS1_top_loc hrev_path])
                      have h_left_id_r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_reverse ?std_loop))
                          (top1_path_reverse ?std_loop)"
                        by (rule Theorem_51_2_left_identity[OF hS1_top_loc hrev_path])
                      have h10_in_S1_r: "(1::real, 0::real) \<in> top1_S1"
                        unfolding top1_S1_def by (by100 simp)
                      have h_prod_const_r: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_constant_path (1::real, 0))"
                        by (rule top1_constant_path_is_path[OF hS1_top_loc h10_in_S1_r])
                      have h_inner_r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0))
                            (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))))
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_reverse ?std_loop))"
                        by (rule path_homotopic_product_right[OF hS1_top_loc h_right_id_r h_prod_const_r])
                      have h_chain_r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_constant_path (1,0))
                            (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))))
                          (top1_path_reverse ?std_loop)"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_inner_r h_left_id_r])
                      have h_agree_r: "\<forall>s\<in>I_set.
                          top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')) s =
                          top1_path_product (top1_constant_path (1,0)) (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))) s"
                      proof (intro ballI)
                        fix s :: real assume hs: "s \<in> I_set"
                        show "top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')) s =
                            top1_path_product (top1_constant_path (1,0)) (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))) s"
                        proof (cases "s \<le> 1/2")
                          case True
                          hence h2s: "2 * s \<in> I_set"
                            using hs unfolding top1_unit_interval_def by (by100 simp)
                          have "(\<pi> \<circ> \<gamma>a') (2*s) = (1, 0)" using h_const_a h2s by (by100 blast)
                          thus ?thesis
                            unfolding top1_path_product_def top1_constant_path_def using True by simp
                        next
                          case False
                          hence hs_gt: "s > 1/2" by simp
                          hence h2sm1: "2 * s - 1 \<in> I_set"
                            using hs unfolding top1_unit_interval_def by (by100 simp)
                          show ?thesis
                          proof (cases "2*s - 1 \<le> 1/2")
                            case True
                            show ?thesis
                              unfolding top1_path_product_def top1_constant_path_def
                              using hs_gt True by simp
                          next
                            case False
                            hence h_inner_gt: "2*s - 1 > 1/2" by simp
                            have h_arg: "2*(2*s - 1) - 1 \<in> I_set"
                              using hs h_inner_gt unfolding top1_unit_interval_def by (by100 simp)
                            have "(\<pi> \<circ> top1_path_reverse \<gamma>b') (2*(2*s-1)-1) = (1, 0)"
                              using h_const_b h_arg by (by100 blast)
                            thus ?thesis
                              unfolding top1_path_product_def top1_constant_path_def
                              using hs_gt h_inner_gt by simp
                          qed
                        qed
                      qed
                      have hrev_gb_path: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b'))"
                        by (rule top1_path_product_is_path[OF hS1_top_loc hrev_path h\<pi>gb_path])
                      have h_rhs_path_r: "top1_is_path_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        by (rule top1_path_product_is_path[OF hS1_top_loc h\<pi>ga_path hrev_gb_path])
                      from paths_agree_on_I_path_homotopic[OF hS1_top_loc h_rhs_path_r h_agree_r]
                      have h_agree_htpy_r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')))
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))))" .
                      have h_step1r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D)
                          (top1_path_product (\<pi> \<circ> \<gamma>a') (top1_path_product (top1_path_reverse ?std_loop) (\<pi> \<circ> top1_path_reverse \<gamma>b')))"
                        using h2r hcomp_eq by simp
                      have h_step2r: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D)
                          (top1_path_product (top1_constant_path (1,0)) (top1_path_product (top1_path_reverse ?std_loop) (top1_constant_path (1,0))))"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_step1r h_agree_htpy_r])
                      have h3: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D) (top1_path_reverse ?std_loop)"
                        by (rule Lemma_51_1_path_homotopic_trans[OF hS1_top_loc h_step2r h_chain_r])
                      thus ?thesis by (by100 blast)
                    qed
                  qed
                  \<comment> \<open>Step 6: [\\<pi> \\<circ> gen\\_loop D] = [\\<pm>std\\_loop] as homotopy classes.\<close>
                  have hclass_eq: "?\<pi>_star (\<iota>F D) = ?std_class
                      \<or> ?\<pi>_star (\<iota>F D) = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                          (top1_path_reverse ?std_loop) g}"
                  proof -
                    \<comment> \<open>\\<pi>*(\\<iota>F D) = [\\<pi> \\<circ> gen\\_loop D] in \\<pi>\\_1(S1).
                       Then use path\\_homotopic\\_same\\_class to convert homotopy to class eq.\<close>
                    \<comment> \<open>Step 1: \\<pi>*(\\<iota>F D) = {g. loop\\_equiv\\_S1 (\\<pi>\\<circ>gen\\_loop D) g}.\<close>
                    have h_induced_eq: "?\<pi>_star (\<iota>F D) = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                        (\<pi> \<circ> gen_loop D) g}"
                    proof -
                      have "?\<pi>_star (\<iota>F D) = {g. \<exists>f\<in>\<iota>F D. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> f) g}"
                        unfolding top1_fundamental_group_induced_on_def by simp
                      also have "\<dots> = {g. \<exists>f. top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) f \<and>
                          top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> f) g}"
                        unfolding \<iota>F_def by simp
                      also have "\<dots> = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                          (\<pi> \<circ> gen_loop D) g}"
                      proof (rule set_eqI, rule iffI)
                        fix g assume "g \<in> {g. \<exists>f. top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) f \<and>
                            top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> f) g}"
                        then obtain f where hf_eq: "top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) f"
                            and hg_eq: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> f) g"
                          by (by100 blast)
                        \<comment> \<open>gen\\_loop D \\<simeq> f in T\\<union>D \\<Rightarrow> \\<pi>\\<circ>gen\\_loop D \\<simeq> \\<pi>\\<circ>f in S1.\<close>
                        \<comment> \<open>f is a loop at y0 (since loop-equiv to gen\\_loop D).\<close>
                        have hf_loop: "top1_is_loop_on ?TD ?TTD y0 f"
                          using hf_eq unfolding top1_loop_equiv_on_def by (by100 blast)
                        have hTTD_top_loc: "is_topology_on ?TD ?TTD"
                        proof -
                          have "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                          have hTY: "is_topology_on Y TY"
                            using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def
                            by (by100 blast)
                          show ?thesis by (rule subspace_topology_is_topology_on[OF hTY \<open>?TD \<subseteq> Y\<close>])
                        qed
                        have h\<pi>_y0_eq: "\<pi> y0 = (1, 0)"
                          unfolding \<pi>_def using hT_x0 by (by100 simp)
                        have h\<pi>_preserves: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                            (\<pi> \<circ> gen_loop D) (\<pi> \<circ> f)"
                          using top1_induced_preserves_loop_equiv[OF hTTD_top_loc h\<pi>_cont
                              hgenD_loop_TD hf_loop hf_eq]
                          h\<pi>_y0_eq by simp
                        from top1_loop_equiv_on_trans[OF hS1_top h\<pi>_preserves hg_eq]
                        show "g \<in> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                            (\<pi> \<circ> gen_loop D) g}" by (by100 blast)
                      next
                        fix g assume "g \<in> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                            (\<pi> \<circ> gen_loop D) g}"
                        hence hg: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> gen_loop D) g"
                          by (by100 blast)
                        have hrefl: "top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) (gen_loop D)"
                          by (rule top1_loop_equiv_on_refl[OF hgenD_loop_TD])
                        show "g \<in> {g. \<exists>f. top1_loop_equiv_on ?TD ?TTD y0 (gen_loop D) f \<and>
                            top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> f) g}"
                          using hrefl hg by (by100 blast)
                      qed
                      finally show ?thesis .
                    qed
                    \<comment> \<open>Step 2: From h\\<pi>\\_genD\\_htpy, [\\<pi>\\<circ>gen\\_loop D] = [\\<pm>std\\_loop].\<close>
                    from h\<pi>_genD_htpy show ?thesis
                    proof
                      assume hhtpy_std: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D) ?std_loop"
                      from path_homotopic_same_class[OF hS1_top hhtpy_std]
                      have "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> gen_loop D) g} =
                          ?std_class" .
                      thus ?thesis using h_induced_eq by simp
                    next
                      assume hhtpy_rev: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
                          (\<pi> \<circ> gen_loop D) (top1_path_reverse ?std_loop)"
                      from path_homotopic_same_class[OF hS1_top hhtpy_rev]
                      have "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (\<pi> \<circ> gen_loop D) g} =
                          {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_path_reverse ?std_loop) g}" .
                      thus ?thesis using h_induced_eq by simp
                    qed
                  qed
                  \<comment> \<open>Step 7: [std\\_loop] generates \\<pi>\\_1(S1).
                     From Theorem\\_54\\_5\\_iso\\_with\\_generator + generation transfer.\<close>
                  have hstd_generates: "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0) =
                      top1_subgroup_generated_on
                        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))
                        {?std_class}"
                  proof -
                    let ?G = "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
                    let ?mulG = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)"
                    let ?eG = "top1_fundamental_group_id top1_S1 top1_S1_topology (1,0)"
                    let ?invG = "top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0)"
                    \<comment> \<open>Get iso \\<phi> with \\<phi>([std]) = 1.\<close>
                    obtain \<phi> where h\<phi>_iso: "top1_group_iso_on ?G ?mulG top1_Z_group top1_Z_mul \<phi>"
                        and h\<phi>_std: "\<phi> ?std_class = (1::int)"
                      using Theorem_54_5_iso_with_generator by (by100 blast)
                    have hG_grp: "top1_is_group_on ?G ?mulG ?eG ?invG"
                    proof -
                      have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
                      from top1_fundamental_group_is_group[OF hS1_top this]
                      show ?thesis .
                    qed
                    have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
                      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
                      by (by100 blast)
                    \<comment> \<open>\\<phi>\\<inverse> is an iso Z \\<rightarrow> \\<pi>\\_1(S1).\<close>
                    let ?\<phi>_inv = "inv_into ?G \<phi>"
                    have h\<phi>_inv_iso: "top1_group_iso_on top1_Z_group top1_Z_mul ?G ?mulG ?\<phi>_inv"
                      by (rule group_iso_on_inverse[OF h\<phi>_iso hG_grp hZ_grp])
                    have h\<phi>_inv_hom: "top1_group_hom_on top1_Z_group top1_Z_mul ?G ?mulG ?\<phi>_inv"
                      using h\<phi>_inv_iso unfolding top1_group_iso_on_def by (by100 blast)
                    have h\<phi>_bij: "bij_betw \<phi> ?G top1_Z_group"
                      using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
                    have h\<phi>_inj: "inj_on \<phi> ?G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
                    have h\<phi>_inv_surj: "?\<phi>_inv ` top1_Z_group = ?G"
                      using h\<phi>_inv_iso unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
                    \<comment> \<open>Z = \\<langle>{1}\\<rangle>.\<close>
                    have hZ_gen: "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul
                        top1_Z_id top1_Z_invg {(1::int)}"
                    proof -
                      from Z_is_free_on_one_generator
                      have "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul
                          top1_Z_id top1_Z_invg ((\<lambda>(_::nat). (1::int)) ` {0::nat})"
                        unfolding top1_is_free_group_full_on_def by (by100 blast)
                      moreover have "((\<lambda>(_::nat). (1::int)) ` {0::nat}) = {(1::int)}" by (by100 simp)
                      ultimately show ?thesis by simp
                    qed
                    \<comment> \<open>\\<phi>\\<inverse>(1) = [std\\_loop].\<close>
                    have hstd_in_G: "?std_class \<in> ?G"
                      using standard_S1_loop_class_in_carrier .
                    have h\<phi>_inv_1: "?\<phi>_inv (1::int) = ?std_class"
                      using inv_into_f_f[OF h\<phi>_inj hstd_in_G] h\<phi>_std by simp
                    \<comment> \<open>Apply surj\\_hom\\_generated.\<close>
                    have h1_in_Z: "{(1::int)} \<subseteq> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
                    from surj_hom_generated[OF hZ_grp hG_grp h\<phi>_inv_hom h\<phi>_inv_surj h1_in_Z hZ_gen]
                    have "?G = top1_subgroup_generated_on ?G ?mulG ?eG ?invG (?\<phi>_inv ` {(1::int)})" .
                    moreover have "?\<phi>_inv ` {(1::int)} = {?std_class}" using h\<phi>_inv_1 by (by100 simp)
                    ultimately show ?thesis by simp
                  qed
                  have hrev_std_generates: "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0) =
                      top1_subgroup_generated_on
                        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
                        (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))
                        {{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                            (top1_path_reverse ?std_loop) g}}"
                  proof -
                    \<comment> \<open>\\<langle>{invg(g)}\\<rangle> = \\<langle>{g}\\<rangle> in any group, since each contains the other's generator.\<close>
                    let ?G = "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
                    let ?mulG = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)"
                    let ?eG = "top1_fundamental_group_id top1_S1 top1_S1_topology (1,0)"
                    let ?invG = "top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0)"
                    let ?rev_class = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                        (top1_path_reverse ?std_loop) g}"
                    \<comment> \<open>Same approach: \\<phi> iso with \\<phi>([std]) = 1 \\<Rightarrow> \\<phi>([rev std]) = -1.
                       Z = \\<langle>{-1}\\<rangle>, \\<phi>\\<inverse>(-1) = [rev std] \\<Rightarrow> \\<pi>\\_1(S1) = \\<langle>{[rev std]}\\<rangle>.\<close>
                    obtain \<phi> where h\<phi>_iso: "top1_group_iso_on ?G ?mulG top1_Z_group top1_Z_mul \<phi>"
                        and h\<phi>_std: "\<phi> ?std_class = (1::int)"
                      using Theorem_54_5_iso_with_generator by (by100 blast)
                    have hG_grp: "top1_is_group_on ?G ?mulG ?eG ?invG"
                    proof -
                      have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
                      from top1_fundamental_group_is_group[OF hS1_top this] show ?thesis .
                    qed
                    have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
                      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
                    have h\<phi>_bij: "bij_betw \<phi> ?G top1_Z_group"
                      using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
                    have h\<phi>_inj: "inj_on \<phi> ?G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
                    have h\<phi>_hom: "top1_group_hom_on ?G ?mulG top1_Z_group top1_Z_mul \<phi>"
                      using h\<phi>_iso unfolding top1_group_iso_on_def by (by100 blast)
                    \<comment> \<open>\\<phi>([rev std]) = -1.\<close>
                    have hstd_in_G: "?std_class \<in> ?G" using standard_S1_loop_class_in_carrier .
                    have hrev_class_eq: "?rev_class = ?invG ?std_class"
                      using fundamental_group_invg_class[OF hS1_top standard_S1_loop_is_loop]
                      by simp
                    have h\<phi>_rev: "\<phi> ?rev_class = (-1::int)"
                    proof -
                      have "\<phi> (?invG ?std_class) = top1_Z_invg (\<phi> ?std_class)"
                        by (rule hom_preserves_inv[OF hG_grp hZ_grp h\<phi>_hom hstd_in_G])
                      hence "\<phi> (?invG ?std_class) = top1_Z_invg 1" using h\<phi>_std by simp
                      hence "\<phi> (?invG ?std_class) = -1"
                        unfolding top1_Z_invg_def by (by100 simp)
                      thus ?thesis using hrev_class_eq by simp
                    qed
                    \<comment> \<open>\\<phi>\\<inverse> iso and surjective.\<close>
                    let ?\<phi>_inv = "inv_into ?G \<phi>"
                    have h\<phi>_inv_iso: "top1_group_iso_on top1_Z_group top1_Z_mul ?G ?mulG ?\<phi>_inv"
                      by (rule group_iso_on_inverse[OF h\<phi>_iso hG_grp hZ_grp])
                    have h\<phi>_inv_hom: "top1_group_hom_on top1_Z_group top1_Z_mul ?G ?mulG ?\<phi>_inv"
                      using h\<phi>_inv_iso unfolding top1_group_iso_on_def by (by100 blast)
                    have h\<phi>_inv_surj: "?\<phi>_inv ` top1_Z_group = ?G"
                      using h\<phi>_inv_iso unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
                    \<comment> \<open>Z = \\<langle>{-1}\\<rangle>.\<close>
                    have hZ_gen_m1: "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul
                        top1_Z_id top1_Z_invg {(-1::int)}"
                    proof -
                      \<comment> \<open>Z = \\<langle>{1}\\<rangle>. Since -1 = invZ(1), and \\<langle>{g}\\<rangle> = \\<langle>{invg(g)}\\<rangle>:\<close>
                      have hZ_gen_1: "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul
                          top1_Z_id top1_Z_invg {(1::int)}"
                      proof -
                        from Z_is_free_on_one_generator
                        have "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul
                            top1_Z_id top1_Z_invg ((\<lambda>(_::nat). (1::int)) ` {0::nat})"
                          unfolding top1_is_free_group_full_on_def by (by100 blast)
                        moreover have "((\<lambda>(_::nat). (1::int)) ` {0::nat}) = {(1::int)}" by (by100 simp)
                        ultimately show ?thesis by simp
                      qed
                      \<comment> \<open>In Z, -1 = invZ(1). And {invg(g)} generates iff {g} generates.\<close>
                      have hm1_eq: "(-1::int) = top1_Z_invg (1::int)"
                        unfolding top1_Z_invg_def by (by100 simp)
                      \<comment> \<open>Every subgroup containing {-1} contains 1 (as invg(-1) = 1), hence contains \\<langle>{1}\\<rangle>.\<close>
                      \<comment> \<open>And every subgroup containing {1} contains -1 (as invg(1) = -1), hence contains \\<langle>{-1}\\<rangle>.\<close>
                      \<comment> \<open>Use subgroup\\_generated\\_minimal: \\<langle>{1}\\<rangle> \\<subseteq> \\<langle>{-1}\\<rangle> and vice versa.\<close>
                      let ?gen1 = "top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {(1::int)}"
                      let ?genm1 = "top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {(-1::int)}"
                      have hm1_in_Z: "{(-1::int)} \<subseteq> top1_Z_group"
                        unfolding top1_Z_group_def by (by100 simp)
                      have h1_in_Z: "{(1::int)} \<subseteq> top1_Z_group"
                        unfolding top1_Z_group_def by (by100 simp)
                      have hgenm1_sub: "?genm1 \<subseteq> top1_Z_group"
                        by (rule subgroup_generated_subset[OF hZ_grp hm1_in_Z])
                      have hgenm1_grp: "top1_is_group_on ?genm1 top1_Z_mul top1_Z_id top1_Z_invg"
                        by (rule intersection_of_subgroups_is_group[OF hZ_grp hm1_in_Z])
                      \<comment> \<open>-1 \\<in> \\<langle>{-1}\\<rangle>.\<close>
                      have hm1_in_genm1: "(-1::int) \<in> ?genm1"
                        by (rule subgroup_generated_contains[OF hZ_grp hm1_in_Z]) (by100 simp)
                      \<comment> \<open>1 = invZ(-1) \\<in> \\<langle>{-1}\\<rangle>.\<close>
                      have "top1_Z_invg (-1::int) = (1::int)"
                        unfolding top1_Z_invg_def by (by100 simp)
                      hence h1_in_genm1: "(1::int) \<in> ?genm1"
                        using group_inv_closed[OF hgenm1_grp hm1_in_genm1] by simp
                      hence "{(1::int)} \<subseteq> ?genm1" by (by100 blast)
                      from subgroup_generated_minimal[OF this hgenm1_sub hgenm1_grp]
                      have hgen1_sub: "?gen1 \<subseteq> ?genm1" .
                      \<comment> \<open>Z = \\<langle>{1}\\<rangle> \\<subseteq> \\<langle>{-1}\\<rangle> \\<subseteq> Z.\<close>
                      have "top1_Z_group \<subseteq> ?genm1" using hZ_gen_1 hgen1_sub by simp
                      thus ?thesis using hgenm1_sub by (by100 blast)
                    qed
                    \<comment> \<open>\\<phi>\\<inverse>(-1) = [rev std].\<close>
                    have hrev_in_G: "?rev_class \<in> ?G"
                    proof -
                      have "?rev_class = ?invG ?std_class" using hrev_class_eq .
                      moreover have "?invG ?std_class \<in> ?G"
                        by (rule group_inv_closed[OF hG_grp hstd_in_G])
                      ultimately show ?thesis by simp
                    qed
                    have h\<phi>_inv_m1: "?\<phi>_inv (-1::int) = ?rev_class"
                      using inv_into_f_f[OF h\<phi>_inj hrev_in_G] h\<phi>_rev by simp
                    \<comment> \<open>Transfer generation.\<close>
                    have hm1_in_Z: "{(-1::int)} \<subseteq> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
                    from surj_hom_generated[OF hZ_grp hG_grp h\<phi>_inv_hom h\<phi>_inv_surj hm1_in_Z hZ_gen_m1]
                    have "?G = top1_subgroup_generated_on ?G ?mulG ?eG ?invG (?\<phi>_inv ` {(-1::int)})" .
                    moreover have "?\<phi>_inv ` {(-1::int)} = {?rev_class}" using h\<phi>_inv_m1 by (by100 simp)
                    ultimately show ?thesis by simp
                  qed
                  \<comment> \<open>Step 8: Combine.\<close>
                  from hclass_eq show ?thesis
                  proof
                    assume "?\<pi>_star (\<iota>F D) = ?std_class"
                    thus ?thesis using hstd_generates by (by100 simp)
                  next
                    assume "?\<pi>_star (\<iota>F D) = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0)
                        (top1_path_reverse ?std_loop) g}"
                    thus ?thesis using hrev_std_generates by (by100 simp)
                  qed
                qed
                \<comment> \<open>Step G6: [standard S1 loop] generates \\<pi>\\_1(S1).
                   Therefore \\<pi>*(\\<iota>F(D)) generates \\<pi>\\_1(S1).
                   Since \\<pi>\\_1(T\\<union>D) \\<cong> Z and \\<pi>* surjective \\<Rightarrow> \\<iota>F(D) generates.\<close>
                \<comment> \<open>\\<pi>*(\\<iota>F(D)) generates \\<pi>\\_1(S1). Since \\<pi>* is surj hom from Z\\<cong>Z,
                   it is an iso. So \\<iota>F(D) generates \\<pi>\\_1(T\\<union>D).\<close>
                have hTTD_top: "is_topology_on ?TD ?TTD"
                proof -
                  have hTD_sub: "?TD \<subseteq> Y" using hT_sub h\<A> \<open>D \<in> \<A>\<close> by (by100 blast)
                  have hTY_top: "is_topology_on Y TY"
                    using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                  show ?thesis by (rule subspace_topology_is_topology_on[OF hTY_top hTD_sub])
                qed
                have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
                  using top1_S1_is_topology_on_strict
                  unfolding is_topology_on_strict_def by (by100 blast)
                have h\<pi>_y0: "\<pi> y0 = (1, 0)"
                  unfolding \<pi>_def using hT_x0 by (by100 simp)
                have h\<pi>_hom: "top1_group_hom_on
                    (top1_fundamental_group_carrier ?TD ?TTD y0)
                    (top1_fundamental_group_mul ?TD ?TTD y0)
                    (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                    (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                    (top1_fundamental_group_induced_on ?TD ?TTD y0 top1_S1 top1_S1_topology (1,0) \<pi>)"
                proof -
                  have hy0_TD: "y0 \<in> ?TD" using hT_x0 by (by100 blast)
                  have h10_S1: "(1::real, 0::real) \<in> top1_S1"
                    unfolding top1_S1_def by (by100 simp)
                  from top1_fundamental_group_induced_on_is_hom[OF hTTD_top hS1_top hy0_TD h10_S1
                      h\<pi>_cont h\<pi>_y0]
                  show ?thesis .
                qed
                \<comment> \<open>G6b (\\<pi>\\_1(S1) generated by std loop) was PROVED in earlier sessions.
                   Now h\\<pi>\\_star\\_gen gives the combined result directly.\<close>
                \<comment> \<open>Since \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1), \\<pi>* is surjective.\<close>
                \<comment> \<open>surj + both \\<cong> Z \\<Rightarrow> iso \\<Rightarrow> \\<iota>F(D) generates \\<pi>\\_1(T\\<union>D).\<close>
                \<comment> \<open>G6c: \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1) \\<Rightarrow> \\<iota>F D generates \\<pi>\\_1(T\\<union>D).
                   Chain: \\<pi>* surjective (image \\<supseteq> generator) \\<Rightarrow> iso (surj\\_hom\\_infinite\\_cyclic\\_inj)
                   \\<Rightarrow> inverse maps generators to generators.
                   Available: hTD\\_iso\\_Z, Theorem\\_54\\_5\\_iso, h\\<pi>\\_hom, h\\<pi>\\_star\\_gen.\<close>
                \<comment> \<open>G6c: \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1) \\<Rightarrow> \\<iota>F D generates \\<pi>\\_1(T\\<union>D).
                   Proof: \\<pi>* surj (image \\<supseteq> generator) \\<Rightarrow> \\<pi>* iso (surj\\_hom\\_infinite\\_cyclic\\_inj)
                   \\<Rightarrow> \\<pi>*\\<inverse> iso \\<Rightarrow> surj\\_hom\\_generated(\\<pi>*\\<inverse>) transfers generation back.\<close>
                show ?thesis
                proof -
                  let ?\<pi>_star = "top1_fundamental_group_induced_on ?TD ?TTD y0
                      top1_S1 top1_S1_topology (1,0) \<pi>"
                  let ?\<pi>1S1 = "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
                  let ?mulS1 = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)"
                  let ?eS1 = "top1_fundamental_group_id top1_S1 top1_S1_topology (1,0)"
                  let ?invS1 = "top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0)"
                  let ?\<pi>1TD = "top1_fundamental_group_carrier ?TD ?TTD y0"
                  let ?mulTD = "top1_fundamental_group_mul ?TD ?TTD y0"
                  let ?eTD = "top1_fundamental_group_id ?TD ?TTD y0"
                  let ?invTD = "top1_fundamental_group_invg ?TD ?TTD y0"
                  \<comment> \<open>Step 1: \\<pi>* is surjective.\<close>
                  have h\<pi>_surj: "?\<pi>_star ` ?\<pi>1TD = ?\<pi>1S1"
                  proof (rule set_eqI, rule iffI)
                    fix x assume "x \<in> ?\<pi>_star ` ?\<pi>1TD"
                    thus "x \<in> ?\<pi>1S1" using h\<pi>_hom unfolding top1_group_hom_on_def by (by100 blast)
                  next
                    fix x assume "x \<in> ?\<pi>1S1"
                    \<comment> \<open>Image is a subgroup containing \\<pi>*(\\<iota>F D). Since \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1),
                       image \\<supseteq> subgroup\\_generated {\\<pi>*(\\<iota>F D)} = \\<pi>\\_1(S1).\<close>
                    have "?\<pi>_star (\<iota>F D) \<in> ?\<pi>_star ` ?\<pi>1TD"
                      using h\<iota>F_carrier by (by100 blast)
                    \<comment> \<open>Image of hom is a subgroup.\<close>
                    have hS1_grp2: "top1_is_group_on ?\<pi>1S1 ?mulS1 ?eS1 ?invS1"
                    proof -
                      have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
                      from top1_fundamental_group_is_group[OF hS1_top this]
                      show ?thesis by (by100 blast)
                    qed
                    have h_img_grp: "top1_is_group_on (?\<pi>_star ` ?\<pi>1TD) ?mulS1 ?eS1 ?invS1"
                      by (rule hom_image_is_subgroup[OF hTD_grp hS1_grp2 h\<pi>_hom])
                    have h_img_sub: "?\<pi>_star ` ?\<pi>1TD \<subseteq> ?\<pi>1S1"
                      using h\<pi>_hom unfolding top1_group_hom_on_def by (by100 blast)
                    have "{?\<pi>_star (\<iota>F D)} \<subseteq> ?\<pi>_star ` ?\<pi>1TD"
                      using \<open>?\<pi>_star (\<iota>F D) \<in> ?\<pi>_star ` ?\<pi>1TD\<close> by (by100 blast)
                    from subgroup_generated_minimal[OF \<open>{?\<pi>_star (\<iota>F D)} \<subseteq> ?\<pi>_star ` ?\<pi>1TD\<close>
                        h_img_sub h_img_grp]
                    have "top1_subgroup_generated_on ?\<pi>1S1 ?mulS1 ?eS1 ?invS1
                        {?\<pi>_star (\<iota>F D)} \<subseteq> ?\<pi>_star ` ?\<pi>1TD" .
                    hence "?\<pi>1S1 \<subseteq> ?\<pi>_star ` ?\<pi>1TD" using h\<pi>_star_gen by (by100 simp)
                    thus "x \<in> ?\<pi>_star ` ?\<pi>1TD" using \<open>x \<in> ?\<pi>1S1\<close> by (by100 blast)
                  qed
                  \<comment> \<open>Step 2: \\<pi>* is an iso (surj hom between Z-iso groups).\<close>
                  have hS1_iso_Z: "top1_groups_isomorphic_on ?\<pi>1S1 ?mulS1 top1_Z_group top1_Z_mul"
                    by (rule Theorem_54_5_iso)
                  \<comment> \<open>Step 3: \\<pi>*\\<inverse> is also an iso, transferring generation back.\<close>
                  \<comment> \<open>Since \\<pi>* is a surjective hom from Z-iso to Z-iso, it is iso (Hopfian).
                     \\<pi>*\\<inverse> is an iso from \\<pi>\\_1(S1) to \\<pi>\\_1(T\\<union>D).
                     \\<pi>*(\\<iota>F D) generates \\<pi>\\_1(S1) \\<Rightarrow> \\<pi>*\\<inverse>(\\<pi>*(\\<iota>F D)) = \\<iota>F D generates \\<pi>\\_1(T\\<union>D).\<close>
                  have h\<pi>_inj: "inj_on ?\<pi>_star ?\<pi>1TD"
                  proof (rule surj_hom_infinite_cyclic_inj[OF hTD_iso_Z hS1_iso_Z h\<pi>_hom h\<pi>_surj])
                    fix a b assume "a \<in> ?\<pi>1TD" "b \<in> ?\<pi>1TD"
                    from group_mul_closed[OF hTD_grp this]
                    show "?mulTD a b \<in> ?\<pi>1TD" .
                  qed
                  \<comment> \<open>\\<pi>* is group iso.\<close>
                  have h\<pi>_iso: "top1_group_iso_on ?\<pi>1TD ?mulTD ?\<pi>1S1 ?mulS1 ?\<pi>_star"
                    using h\<pi>_hom h\<pi>_inj h\<pi>_surj
                    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
                    by (by100 blast)
                  \<comment> \<open>\\<pi>*\\<inverse> transfers generation.\<close>
                  have hS1_grp2: "top1_is_group_on ?\<pi>1S1 ?mulS1 ?eS1 ?invS1"
                  proof -
                    have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
                    from top1_fundamental_group_is_group[OF hS1_top this]
                    show ?thesis by (by100 blast)
                  qed
                  have h\<pi>_inv_iso: "top1_group_iso_on ?\<pi>1S1 ?mulS1 ?\<pi>1TD ?mulTD
                      (inv_into ?\<pi>1TD ?\<pi>_star)"
                    using group_iso_on_inverse[OF h\<pi>_iso hTD_grp hS1_grp2] .
                  have h\<pi>_inv_hom: "top1_group_hom_on ?\<pi>1S1 ?mulS1 ?\<pi>1TD ?mulTD
                      (inv_into ?\<pi>1TD ?\<pi>_star)"
                    using h\<pi>_inv_iso unfolding top1_group_iso_on_def by (by100 blast)
                  have h\<pi>_inv_surj: "(inv_into ?\<pi>1TD ?\<pi>_star) ` ?\<pi>1S1 = ?\<pi>1TD"
                    using h\<pi>_inv_iso unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
                  have hstar_in: "?\<pi>_star (\<iota>F D) \<in> ?\<pi>1S1"
                    using h\<pi>_hom h\<iota>F_carrier unfolding top1_group_hom_on_def by (by100 blast)
                  have h_inv_star: "inv_into ?\<pi>1TD ?\<pi>_star (?\<pi>_star (\<iota>F D)) = \<iota>F D"
                    using inv_into_f_f[OF h\<pi>_inj h\<iota>F_carrier] .
                  have "{?\<pi>_star (\<iota>F D)} \<subseteq> ?\<pi>1S1" using hstar_in by (by100 blast)
                  have hS1_grp: "top1_is_group_on ?\<pi>1S1 ?mulS1 ?eS1 ?invS1"
                  proof -
                    have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
                    from top1_fundamental_group_is_group[OF hS1_top this]
                    show ?thesis by (by100 blast)
                  qed
                  have hstar_sub: "{?\<pi>_star (\<iota>F D)} \<subseteq> ?\<pi>1S1" using hstar_in by (by100 blast)
                  from surj_hom_generated[OF hS1_grp hTD_grp h\<pi>_inv_hom h\<pi>_inv_surj hstar_sub h\<pi>_star_gen]
                  have "?\<pi>1TD = top1_subgroup_generated_on ?\<pi>1TD ?mulTD ?eTD ?invTD
                      (inv_into ?\<pi>1TD ?\<pi>_star ` {?\<pi>_star (\<iota>F D)})" .
                  hence "?\<pi>1TD = top1_subgroup_generated_on ?\<pi>1TD ?mulTD ?eTD ?invTD {\<iota>F D}"
                    using h_inv_star by (by100 simp)
                  thus ?thesis .
                qed
              qed
              \<comment> \<open>Step C: Apply iso\\_Z\\_generator\\_free\\_single.\<close>
              have hfree_TD: "top1_is_free_group_full_on
                  (top1_fundamental_group_carrier ?TD ?TTD y0)
                  (top1_fundamental_group_mul ?TD ?TTD y0)
                  (top1_fundamental_group_id ?TD ?TTD y0)
                  (top1_fundamental_group_invg ?TD ?TTD y0)
                  \<iota>F {D}"
              proof -
                from iso_Z_generator_free_single[OF hTD_iso_Z hTD_grp h\<iota>F_carrier hgen_TD]
                have "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?TD ?TTD y0) (top1_fundamental_group_mul ?TD ?TTD y0)
                    (top1_fundamental_group_id ?TD ?TTD y0) (top1_fundamental_group_invg ?TD ?TTD y0)
                    (\<lambda>_. \<iota>F D) {()}" .
                \<comment> \<open>Reindex from {()} to {D}: use free\\_group\\_full\\_reindex + free\\_group\\_full\\_on\\_cong.\<close>
                have "bij_betw (\<lambda>_::'a set. ()::unit) {D} {()}"
                  unfolding bij_betw_def inj_on_def by (by100 blast)
                from free_group_full_reindex[OF
                    \<open>top1_is_free_group_full_on _ _ _ _ (\<lambda>_. \<iota>F D) {()}\<close> this]
                have "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?TD ?TTD y0) (top1_fundamental_group_mul ?TD ?TTD y0)
                    (top1_fundamental_group_id ?TD ?TTD y0) (top1_fundamental_group_invg ?TD ?TTD y0)
                    ((\<lambda>_. \<iota>F D) \<circ> (\<lambda>_::'a set. ()::unit)) {D}" .
                moreover have "\<forall>s \<in> {D}. ((\<lambda>_. \<iota>F D) \<circ> (\<lambda>_::'a set. ()::unit)) s = \<iota>F s"
                  by (by100 simp)
                ultimately show ?thesis
                  by (rule free_group_full_on_cong)
              qed
              \<comment> \<open>Package the result.\<close>
              \<comment> \<open>Rewrite T \\<union> \\<Union>F = T \\<union> D.\<close>
              have hfree_F: "top1_is_free_group_full_on
                  (top1_fundamental_group_carrier (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_mul (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_id (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  (top1_fundamental_group_invg (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
                  \<iota>F {D}" using hfree_TD hTD_eq by (by100 simp)
              have h_incl_F: "\<forall>A\<in>F. top1_fundamental_group_induced_on (T \<union> \<Union>F)
                    (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A"
                using h_incl_gen hD hTD_eq by (by100 simp)
              show ?thesis
                using hfree_F h_incl_F hD by (by100 blast)
            qed
              next
                case hcard_gt1: False
                have hcard_ge2: "card F \<ge> 2"
                proof -
                  have "card F \<noteq> 0" using hFfin hF_ne by (by100 auto)
                  moreover have "card F \<noteq> 1" using hcard_gt1 .
                  ultimately show ?thesis by (by100 linarith)
                qed
                then obtain A1 where hA1: "A1 \<in> F" using hF_ne by (by100 blast)
                let ?F' = "F - {A1}"
                have hF'_fin: "finite ?F'" using hFfin by (by100 simp)
                have hF'_NT: "?F' \<subseteq> ?NT" using hF_NT by (by100 blast)
                have hF'_ne: "?F' \<noteq> {}"
                proof -
                  have "card ?F' = card F - 1" using hFfin hA1 by (by100 simp)
                  hence "card ?F' \<ge> 1" using hcard_ge2 by (by100 linarith)
                  hence "card ?F' > 0" by (by100 linarith)
                  thus ?thesis using card_gt_0_iff hF'_fin by (by5000 blast)
                qed
                have hcard_F': "card ?F' < card F" using hFfin hA1 hcard_ge2 by (by100 simp)
                \<comment> \<open>IH for {A1}: harc\\_loops\\_free applied to the singleton set.\<close>
                have hA1_NT: "A1 \<in> ?NT" using hF_NT hA1 by (by100 blast)
                have hIH_base: "\<exists>\<iota>1. top1_is_free_group_full_on
                    (top1_fundamental_group_carrier (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1})) y0)
                    (top1_fundamental_group_mul (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1})) y0)
                    (top1_fundamental_group_id (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1})) y0)
                    (top1_fundamental_group_invg (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1})) y0)
                    \<iota>1 {A1}
                  \<and> (\<forall>A\<in>{A1}. top1_fundamental_group_induced_on (T \<union> \<Union>{A1})
                        (subspace_topology Y TY (T \<union> \<Union>{A1})) y0 Y TY y0 (\<lambda>x. x) (\<iota>1 A) = gen A)"
                proof -
                  have "card {A1} < n"
                  proof -
                    have "card {A1} = 1" by (by100 simp)
                    have "card F \<ge> 2" using hcard_ge2 .
                    thus ?thesis using hcard \<open>card {A1} = 1\<close> by (by100 linarith)
                  qed
                  from less.IH[OF this, of "{A1}", unfolded P_def]
                  show ?thesis using hA1_NT by (by100 simp)
                qed
                \<comment> \<open>IH for F': harc\\_loops\\_free applied recursively.\<close>
                have hIH_step: "\<exists>\<iota>'. top1_is_free_group_full_on
                    (top1_fundamental_group_carrier (T \<union> \<Union>?F') (subspace_topology Y TY (T \<union> \<Union>?F')) y0)
                    (top1_fundamental_group_mul (T \<union> \<Union>?F') (subspace_topology Y TY (T \<union> \<Union>?F')) y0)
                    (top1_fundamental_group_id (T \<union> \<Union>?F') (subspace_topology Y TY (T \<union> \<Union>?F')) y0)
                    (top1_fundamental_group_invg (T \<union> \<Union>?F') (subspace_topology Y TY (T \<union> \<Union>?F')) y0)
                    \<iota>' ?F'
                  \<and> (\<forall>A\<in>?F'. top1_fundamental_group_induced_on (T \<union> \<Union>?F')
                        (subspace_topology Y TY (T \<union> \<Union>?F')) y0 Y TY y0 (\<lambda>x. x) (\<iota>' A) = gen A)"
                proof -
                  have "card ?F' < n" using hcard_F' hcard by (by100 simp)
                  from less.IH[OF this, of "?F'", unfolded P_def]
                  show ?thesis using hF'_fin hF'_NT hF'_ne by (by100 blast)
                qed
                \<comment> \<open>SvK decomposition: pick interior points, define U and V.\<close>
                \<comment> \<open>Step 1: Interior points for each arc in F.\<close>
                have hY_strict: "is_topology_on_strict Y TY"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have hY_haus: "is_hausdorff_on Y TY"
                  using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                have hTY_top: "is_topology_on Y TY"
                  using hY_strict unfolding is_topology_on_strict_def by (by100 blast)
                have hint_pts: "\<forall>A\<in>F. \<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                proof (intro ballI)
                  fix A assume "A \<in> F"
                  hence "A \<in> ?NT" using hF_NT by (by100 blast)
                  hence "A \<in> \<A>" by (by100 blast)
                  have harc: "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      A (subspace_topology Y TY A) h" using harc unfolding top1_is_arc_on_def by (by100 blast)
                  have hbij: "bij_betw h top1_unit_interval A"
                    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hinj: "inj_on h top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
                  have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>A \<subseteq> Y\<close> harc hh]
                  have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {h 0, h 1}" .
                  have h12_I: "(1/2::real) \<in> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 simp)
                  have "h (1/2) \<in> A" using hbij h12_I unfolding bij_betw_def by (by100 blast)
                  moreover have "h (1/2) \<notin> {h 0, h 1}"
                  proof -
                    have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                    have "(1/2::real) \<noteq> 0" by (by100 simp)
                    hence "h (1/2) \<noteq> h 0" using hinj h12_I h0_I unfolding inj_on_def by (by100 blast)
                    have "(1/2::real) \<noteq> 1" by (by100 simp)
                    hence "h (1/2) \<noteq> h 1" using hinj h12_I h1_I unfolding inj_on_def by (by100 blast)
                    thus ?thesis using \<open>h (1/2) \<noteq> h 0\<close> by (by100 blast)
                  qed
                  ultimately show "\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    using hep by (by100 blast)
                qed
                have "\<exists>ps. \<forall>A\<in>F. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                proof -
                  from hint_pts have "\<forall>A. A \<in> F \<longrightarrow> (\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A))"
                    by (by100 blast)
                  hence "\<exists>f. \<forall>A. A \<in> F \<longrightarrow> f A \<in> A \<and> f A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    by (by5000 metis)
                  thus ?thesis by (by100 blast)
                qed
                then obtain ps where hps: "\<forall>A\<in>F. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                  by (by100 blast)
                \<comment> \<open>Step 2: Define X = T \\<union> \\<Union>F, and U, V for SvK.\<close>
                let ?X = "T \<union> \<Union>F"
                let ?TX = "subspace_topology Y TY ?X"
                let ?U = "?X - ps ` ?F'"
                let ?V = "?X - ps ` {A1}"
                \<comment> \<open>Step 3: Basic topology of X.\<close>
                have hX_sub: "?X \<subseteq> Y" using hT_sub h\<A> hF_NT by (by100 blast)
                have hTX_top: "is_topology_on ?X ?TX"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hX_sub])
                have hX_haus: "is_hausdorff_on ?X ?TX"
                  using Theorem_17_11 hY_haus hX_sub by (by100 blast)
                have hX_strict: "is_topology_on_strict ?X ?TX"
                  by (rule subspace_topology_is_strict[OF hY_strict hX_sub])
                have hy0_X: "y0 \<in> ?X" using hT_x0 by (by100 blast)
                \<comment> \<open>Step 4: U, V open in X.\<close>
                have hU_open: "openin_on ?X ?TX ?U"
                proof -
                  have hfin_SU: "finite (ps ` ?F')" using hFfin by (by100 simp)
                  have hsub_SU: "ps ` ?F' \<subseteq> ?X" using hps hF_NT h\<A> by (by100 blast)
                  have "closedin_on ?X ?TX (ps ` ?F')"
                    by (rule Theorem_17_8[OF hX_haus hfin_SU hsub_SU])
                  thus ?thesis using closedin_complement_openin by (by100 simp)
                qed
                have hV_open: "openin_on ?X ?TX ?V"
                proof -
                  have hfin_SV: "finite (ps ` {A1})" by (by100 simp)
                  have hsub_SV: "ps ` {A1} \<subseteq> ?X" using hps hA1 h\<A> hF_NT by (by100 blast)
                  have "closedin_on ?X ?TX (ps ` {A1})"
                    by (rule Theorem_17_8[OF hX_haus hfin_SV hsub_SV])
                  thus ?thesis using closedin_complement_openin by (by100 simp)
                qed
                \<comment> \<open>Step 5: U \\<union> V = X.\<close>
                have hUV_cover: "?U \<union> ?V = ?X"
                proof -
                  have "ps ` ?F' \<inter> ps ` {A1} = {}"
                  proof (rule ccontr)
                    assume "\<not> ?thesis"
                    then obtain B where "B \<in> ?F'" "ps B = ps A1" by (by100 blast)
                    hence "B \<in> F" "B \<noteq> A1" by (by100 blast)+
                    have "ps B \<in> B" using hps \<open>B \<in> F\<close> by (by100 blast)
                    have "ps B \<in> A1" using \<open>ps B = ps A1\<close> hps hA1 by (by100 simp)
                    have "ps B \<in> B \<inter> A1" using \<open>ps B \<in> B\<close> \<open>ps B \<in> A1\<close> by (by100 blast)
                    have "B \<in> \<A>" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                    have "A1 \<in> \<A>" using hF_NT hA1 by (by100 blast)
                    from h\<A>_inter[rule_format, OF \<open>B \<in> \<A>\<close> \<open>A1 \<in> \<A>\<close> \<open>B \<noteq> A1\<close>]
                    have "B \<inter> A1 \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
                    hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>ps B \<in> B \<inter> A1\<close> by (by100 blast)
                    thus False using hps \<open>B \<in> F\<close> by (by100 blast)
                  qed
                  thus ?thesis by (by100 blast)
                qed
                \<comment> \<open>Step 5b: Subgraph infrastructure for X = T \\<union> \\<Union>F.\<close>
                let ?\<A>_X = "{A \<in> \<A>. A \<subseteq> ?X}"
                have h\<A>X_cover: "?\<A>_X \<subseteq> \<A>" by (by100 blast)
                have hX_eq_union: "?X = \<Union>?\<A>_X"
                proof (rule set_eqI, rule iffI)
                  fix x assume "x \<in> ?X"
                  show "x \<in> \<Union>?\<A>_X"
                  proof (cases "x \<in> T")
                    case True
                    hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
                    then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" by (by100 blast)
                    have "A \<subseteq> ?X" using \<open>A \<subseteq> T\<close> by (by100 blast)
                    thus ?thesis using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> by (by100 blast)
                  next
                    case False
                    hence "x \<in> \<Union>F" using \<open>x \<in> ?X\<close> by (by100 blast)
                    then obtain A where "A \<in> F" "x \<in> A" by (by100 blast)
                    have "A \<in> \<A>" using hF_NT \<open>A \<in> F\<close> by (by100 blast)
                    have "A \<subseteq> ?X" using \<open>A \<in> F\<close> by (by100 blast)
                    thus ?thesis using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> by (by100 blast)
                  qed
                next
                  fix x assume "x \<in> \<Union>?\<A>_X"
                  then obtain A where "A \<in> ?\<A>_X" "x \<in> A" by (by100 blast)
                  thus "x \<in> ?X" by (by100 blast)
                qed
                have hNTX_eq_F: "{A \<in> ?\<A>_X. \<not> A \<subseteq> T} = F"
                proof (rule set_eqI, rule iffI)
                  fix A assume "A \<in> {A \<in> ?\<A>_X. \<not> A \<subseteq> T}"
                  hence "A \<in> \<A>" "\<not> A \<subseteq> T" "A \<subseteq> ?X" by (by100 blast)+
                  hence "A \<in> ?NT" by (by100 blast)
                  \<comment> \<open>A \\<subseteq> X and A \\<in> NT implies A \\<in> F (non-F non-tree arcs can't be \\<subseteq> X).\<close>
                  show "A \<in> F"
                  proof (rule ccontr)
                    assume "A \<notin> F"
                    have "A \<in> ?NT" using \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
                    obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                        top1_unit_interval_topology A (subspace_topology Y TY A) h"
                      using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
                    have hbij: "bij_betw h top1_unit_interval A"
                      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                    have hinj: "inj_on h top1_unit_interval"
                      using hbij unfolding bij_betw_def by (by100 blast)
                    have h12_I: "(1/2::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have "h (1/2) \<in> A" using hbij h12_I unfolding bij_betw_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF hY_strict hY_haus _ _ hh]
                    have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {h 0, h 1}"
                      using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    have "h (1/2) \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    proof -
                      have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                      have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
                      have "h (1/2) \<noteq> h 0"
                      proof
                        assume "h (1/2) = h 0"
                        from inj_onD[OF hinj this h12_I h0_I] show False by (by100 simp)
                      qed
                      have "h (1/2) \<noteq> h 1"
                      proof
                        assume "h (1/2) = h 1"
                        from inj_onD[OF hinj this h12_I h1_I] show False by (by100 simp)
                      qed
                      thus ?thesis using hep \<open>h (1/2) \<noteq> h 0\<close> by (by100 blast)
                    qed
                    have "h (1/2) \<notin> T"
                    proof -
                      from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
                      have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
                      thus ?thesis using \<open>h (1/2) \<in> A\<close> \<open>h (1/2) \<notin> top1_arc_endpoints_on A _\<close>
                        by (by100 blast)
                    qed
                    have "h (1/2) \<notin> \<Union>F"
                    proof
                      assume "h (1/2) \<in> \<Union>F"
                      then obtain B where "B \<in> F" "h (1/2) \<in> B" by (by100 blast)
                      have "B \<in> \<A>" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                      have "A \<noteq> B" using \<open>A \<notin> F\<close> \<open>B \<in> F\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
                      have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
                      hence "h (1/2) \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                        using \<open>h (1/2) \<in> A\<close> \<open>h (1/2) \<in> B\<close> by (by100 blast)
                      thus False using \<open>h (1/2) \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                    qed
                    have "h (1/2) \<notin> ?X" using \<open>h (1/2) \<notin> T\<close> \<open>h (1/2) \<notin> \<Union>F\<close> by (by100 blast)
                    thus False using \<open>A \<subseteq> ?X\<close> \<open>h (1/2) \<in> A\<close> by (by100 blast)
                  qed
                next
                  fix A assume "A \<in> F"
                  have "A \<in> \<A>" using hF_NT \<open>A \<in> F\<close> by (by100 blast)
                  have "A \<subseteq> ?X" using \<open>A \<in> F\<close> by (by100 blast)
                  have "\<not> A \<subseteq> T" using hF_NT \<open>A \<in> F\<close> by (by100 blast)
                  thus "A \<in> {A \<in> ?\<A>_X. \<not> A \<subseteq> T}" using \<open>A \<in> \<A>\<close> \<open>A \<subseteq> ?X\<close> by (by100 blast)
                qed
                \<comment> \<open>X is a graph (subgraph\\_union\\_of\\_arcs\\_is\\_graph).\<close>
                have hX_graph: "top1_is_graph_on ?X ?TX"
                proof -
                  have h\<A>X_cover_Y: "\<Union>?\<A>_X \<subseteq> Y" using h\<A> by (by100 blast)
                  have h\<A>X_arcs_Y: "\<forall>A\<in>?\<A>_X. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
                    using h\<A> by (by100 blast)
                  have h\<A>X_inter_Y: "\<forall>A\<in>?\<A>_X. \<forall>B\<in>?\<A>_X. A \<noteq> B \<longrightarrow>
                      A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                    \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                    \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                    using h\<A>_inter by (by100 blast)
                  have h\<A>X_coh_Y: "\<forall>C. C \<subseteq> \<Union>?\<A>_X \<longrightarrow>
                      (closedin_on (\<Union>?\<A>_X) (subspace_topology Y TY (\<Union>?\<A>_X)) C \<longleftrightarrow>
                       (\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
                    using subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                        h\<A>X_cover hX_eq_union] hX_eq_union by (by100 simp)
                  show ?thesis using subgraph_union_of_arcs_is_graph[OF assms(1)
                      h\<A>X_arcs_Y h\<A>X_cover_Y h\<A>X_inter_Y h\<A>X_coh_Y] hX_eq_union by (by100 simp)
                qed
                have hT_tree_X: "top1_is_tree_on T (subspace_topology ?X ?TX T)"
                proof -
                  have "T \<subseteq> ?X" by (by100 blast)
                  hence "subspace_topology ?X ?TX T = subspace_topology Y TY T"
                    by (rule subspace_topology_trans)
                  thus ?thesis using hT_tree by simp
                qed
                have hT_subgraph_X: "\<forall>A\<in>?\<A>_X. A \<subseteq> T \<or>
                    A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                proof (intro ballI)
                  fix A assume "A \<in> ?\<A>_X"
                  hence "A \<in> \<A>" "A \<subseteq> ?X" by (by100 blast)+
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                  from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
                  show "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                    using \<open>subspace_topology ?X ?TX A = _\<close> by simp
                qed
                have hNT_endpts_X: "\<forall>A\<in>F. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?X ?TX A). e \<in> T"
                proof (intro ballI)
                  fix A e assume "A \<in> F" "e \<in> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                  have "A \<in> ?NT" using hF_NT \<open>A \<in> F\<close> by (by100 blast)
                  have "A \<subseteq> ?X" using \<open>A \<in> F\<close> by (by100 blast)
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                  thus "e \<in> T" using hNT_endpoints \<open>A \<in> ?NT\<close> \<open>e \<in> _\<close> by simp
                qed
                have hps_X: "\<forall>A\<in>F. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                proof (intro ballI)
                  fix A assume "A \<in> F"
                  have "A \<subseteq> ?X" using \<open>A \<in> F\<close> by (by100 blast)
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                  thus "ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                    using hps \<open>A \<in> F\<close> by simp
                qed
                have hvertices_T_X: "\<forall>A\<in>?\<A>_X. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?X ?TX A). e \<in> T"
                proof (intro ballI)
                  fix A e assume "A \<in> ?\<A>_X" "e \<in> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                  have "A \<in> \<A>" "A \<subseteq> ?X" using \<open>A \<in> ?\<A>_X\<close> by (by100 blast)+
                  have hsub_eq: "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                  have he_Y: "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
                    using \<open>e \<in> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)\<close> hsub_eq by simp
                  show "e \<in> T"
                  proof (cases "A \<subseteq> T")
                    case True
                    have "e \<in> A" using he_Y
                      unfolding top1_arc_endpoints_on_def by (by100 blast)
                    thus ?thesis using True by (by100 blast)
                  next
                    case False
                    hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
                    thus ?thesis using hNT_endpoints he_Y by (by100 blast)
                  qed
                qed
                have h\<A>X_coh_X: "\<forall>C. C \<subseteq> ?X \<longrightarrow>
                    (closedin_on ?X ?TX C \<longleftrightarrow>
                     (\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)))"
                proof (intro allI impI iffI ballI)
                  fix C A assume hC: "C \<subseteq> ?X" and hcl: "closedin_on ?X ?TX C" and "A \<in> ?\<A>_X"
                  have "A \<subseteq> ?X" using \<open>A \<in> ?\<A>_X\<close> by (by100 blast)
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                  from subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                      h\<A>X_cover hX_eq_union, rule_format, OF hC, THEN iffD1, OF hcl]
                  have "\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology Y TY A) (A \<inter> C)" .
                  thus "closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)"
                    using \<open>A \<in> ?\<A>_X\<close> \<open>subspace_topology ?X ?TX A = _\<close> by simp
                next
                  fix C assume hC: "C \<subseteq> ?X"
                    and hall: "\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)"
                  have "\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                  proof (intro ballI)
                    fix A assume "A \<in> ?\<A>_X"
                    have "A \<subseteq> ?X" using \<open>A \<in> ?\<A>_X\<close> by (by100 blast)
                    have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                      by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?X\<close>])
                    from hall[rule_format, OF \<open>A \<in> ?\<A>_X\<close>]
                    show "closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                      using \<open>subspace_topology ?X ?TX A = _\<close> by simp
                  qed
                  from subgraph_coherent_topology[OF assms(1) h\<A> h\<A>_cover h\<A>_inter h\<A>_coh
                      h\<A>X_cover hX_eq_union, rule_format, OF hC, THEN iffD2, OF this]
                  show "closedin_on ?X ?TX C" .
                qed
                \<comment> \<open>Step 6: U \\<inter> V = X - ps`F is simply connected.\<close>
                have hUV_eq: "?U \<inter> ?V = ?X - ps ` F"
                proof -
                  have "F = ?F' \<union> {A1}" using hA1 by (by100 blast)
                  hence "ps ` F = ps ` ?F' \<union> ps ` {A1}" by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
                have hUV_eq: "?U \<inter> ?V = ?X - ps ` F"
                proof -
                  have "F = ?F' \<union> {A1}" using hA1 by (by100 blast)
                  hence "ps ` F = ps ` ?F' \<union> ps ` {A1}" by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
                \<comment> \<open>Arcs in X-subspace form.\<close>
                have h\<A>X_arcs_X: "\<forall>A\<in>?\<A>_X. A \<subseteq> ?X \<and> top1_is_arc_on A (subspace_topology ?X ?TX A)"
                proof (intro ballI conjI)
                  fix A assume "A \<in> ?\<A>_X"
                  show "A \<subseteq> ?X" using \<open>A \<in> ?\<A>_X\<close> by (by100 blast)
                  have "A \<in> \<A>" using \<open>A \<in> ?\<A>_X\<close> by (by100 blast)
                  have "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_X\<close> in blast)
                  thus "top1_is_arc_on A (subspace_topology ?X ?TX A)"
                    using \<open>top1_is_arc_on A (subspace_topology Y TY A)\<close> by simp
                qed
                have h\<A>X_inter_X: "\<forall>A\<in>?\<A>_X. \<forall>B\<in>?\<A>_X. A \<noteq> B \<longrightarrow>
                    A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                proof (intro ballI impI)
                  fix A B assume "A \<in> ?\<A>_X" "B \<in> ?\<A>_X" "A \<noteq> B"
                  have "A \<in> \<A>" "B \<in> \<A>" using \<open>A \<in> ?\<A>_X\<close> \<open>B \<in> ?\<A>_X\<close> by (by100 blast)+
                  from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
                  have "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
                  have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                    by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_X\<close> in blast)
                  thus "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                    using \<open>A \<inter> B \<subseteq> _\<close> by simp
                qed
                have hUV_sc: "top1_simply_connected_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V))"
                proof -
                  have "T \<subseteq> ?X" by (by100 blast)
                  have h_sc: "top1_simply_connected_on (?X - ps ` F) (subspace_topology ?X ?TX (?X - ps ` F))"
                  proof (rule graph_remove_interior_points_sc)
                    show "top1_is_graph_on ?X ?TX" by (rule hX_graph)
                    show "\<forall>A\<in>?\<A>_X. A \<subseteq> ?X \<and> top1_is_arc_on A (subspace_topology ?X ?TX A)"
                      by (rule h\<A>X_arcs_X)
                    show "\<Union>?\<A>_X = ?X" by (rule hX_eq_union[symmetric])
                    show "\<forall>A\<in>?\<A>_X. \<forall>B\<in>?\<A>_X. A \<noteq> B \<longrightarrow>
                        A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      by (rule h\<A>X_inter_X)
                    show "top1_is_tree_on T (subspace_topology ?X ?TX T)" by (rule hT_tree_X)
                    show "T \<subseteq> ?X" by (by100 blast)
                    show "\<forall>A\<in>?\<A>_X. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      by (rule hT_subgraph_X)
                    show "F = {A \<in> ?\<A>_X. \<not> A \<subseteq> T}" by (rule hNTX_eq_F[symmetric])
                    show "finite F" by (rule hFfin)
                    show "\<forall>A\<in>F. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      by (rule hps_X)
                    show "\<forall>A\<in>?\<A>_X. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?X ?TX A). e \<in> T"
                      by (rule hvertices_T_X)
                    show "y0 \<in> T" by (rule hT_x0)
                    show "\<forall>C. C \<subseteq> ?X \<longrightarrow>
                        (closedin_on ?X ?TX C \<longleftrightarrow>
                         (\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)))"
                      by (rule h\<A>X_coh_X)
                  qed
                  thus ?thesis using hUV_eq by simp
                qed
                \<comment> \<open>Step 7: Define DR targets and U, V path-connectivity.\<close>
                let ?target_U = "T \<union> A1"
                let ?target_V = "T \<union> \<Union>?F'"
                \<comment> \<open>U and V path-connected: proved in Step 9b below (after DRs).\<close>
                \<comment> \<open>Step 8: y0 \\<in> U \\<inter> V.\<close>
                have hy0_UV: "y0 \<in> ?U \<inter> ?V"
                proof -
                  have "y0 \<in> ?X" using hT_x0 by (by100 blast)
                  have "y0 \<notin> ps ` ?F'"
                  proof
                    assume "y0 \<in> ps ` ?F'"
                    then obtain B where "B \<in> ?F'" "ps B = y0" by (by100 blast)
                    hence "B \<in> F" by (by100 blast)
                    have "ps B \<in> B" using hps \<open>B \<in> F\<close> by (by100 blast)
                    have "B \<in> ?NT" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                    hence "\<not> B \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF _] this
                    have "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>B \<in> ?NT\<close> by (by100 blast)
                    have "ps B \<in> T" using \<open>ps B = y0\<close> hT_x0 by simp
                    hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>ps B \<in> B\<close> \<open>B \<inter> T \<subseteq> _\<close> by (by100 blast)
                    thus False using hps \<open>B \<in> F\<close> by (by100 blast)
                  qed
                  have "y0 \<notin> ps ` {A1}"
                  proof
                    assume "y0 \<in> ps ` {A1}"
                    hence "ps A1 = y0" by (by100 simp)
                    have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
                    have "A1 \<in> ?NT" using hF_NT hA1 by (by100 blast)
                    hence "\<not> A1 \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF _] this
                    have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using \<open>A1 \<in> ?NT\<close> by (by100 blast)
                    have "ps A1 \<in> T" using \<open>ps A1 = y0\<close> hT_x0 by simp
                    hence "ps A1 \<in> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using \<open>ps A1 \<in> A1\<close> \<open>A1 \<inter> T \<subseteq> _\<close> by (by100 blast)
                    thus False using hps hA1 by (by100 blast)
                  qed
                  thus ?thesis using \<open>y0 \<in> ?X\<close> \<open>y0 \<notin> ps ` ?F'\<close> \<open>y0 \<notin> ps ` {A1}\<close>
                    by (by100 blast)
                qed
                \<comment> \<open>Step 9: U DRs to T \\<union> A1, V DRs to T \\<union> \\<Union>F'.\<close>
                have hNT_endpoints_all: "\<forall>A\<in>?NT. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
                  using hNT_endpoints by (by100 blast)
                have hU_dr: "top1_deformation_retract_of_on ?U (subspace_topology Y TY ?U) ?target_U"
                proof -
                  \<comment> \<open>Apply graph\\_deformation\\_retract\\_helper to X with S = F'.\<close>
                  have hdr: "top1_deformation_retract_of_on (?X - ps ` ?F')
                      (subspace_topology ?X ?TX (?X - ps ` ?F'))
                      (T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - ?F'))"
                  proof (rule graph_deformation_retract_helper[where \<A>="?\<A>_X"])
                    show "top1_is_graph_on ?X ?TX" by (rule hX_graph)
                    show "\<forall>A\<in>?\<A>_X. A \<subseteq> ?X \<and> top1_is_arc_on A (subspace_topology ?X ?TX A)"
                      by (rule h\<A>X_arcs_X)
                    show "\<Union>?\<A>_X = ?X" by (rule hX_eq_union[symmetric])
                    show "\<forall>A\<in>?\<A>_X. \<forall>B\<in>?\<A>_X. A \<noteq> B \<longrightarrow>
                        A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)
                      \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?X ?TX B)
                      \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                    proof (intro ballI impI)
                      fix A B assume "A \<in> ?\<A>_X" "B \<in> ?\<A>_X" "A \<noteq> B"
                      from h\<A>_inter[rule_format, OF _ _ \<open>A \<noteq> B\<close>]
                      have h_Y: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                        using \<open>A \<in> ?\<A>_X\<close> \<open>B \<in> ?\<A>_X\<close> by (by100 blast)
                      have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                        by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_X\<close> in blast)
                      moreover have "subspace_topology ?X ?TX B = subspace_topology Y TY B"
                        by (rule subspace_topology_trans) (use \<open>B \<in> ?\<A>_X\<close> in blast)
                      ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)
                        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?X ?TX B)
                        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                        using h_Y by simp
                    qed
                    show "\<forall>C. C \<subseteq> ?X \<longrightarrow> (closedin_on ?X ?TX C \<longleftrightarrow>
                        (\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)))"
                      by (rule h\<A>X_coh_X)
                    show "top1_is_tree_on T (subspace_topology ?X ?TX T)" by (rule hT_tree_X)
                    show "T \<subseteq> ?X" by (by100 blast)
                    show "\<forall>A\<in>?\<A>_X. \<not> A \<subseteq> T \<longrightarrow> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      using hT_subgraph_X by (by100 blast)
                    show "\<forall>A\<in>{A \<in> ?\<A>_X. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?X ?TX A). e \<in> T"
                      using hvertices_T_X hNTX_eq_F hNT_endpts_X by (by100 blast)
                    show "finite ?F'" by (rule hF'_fin)
                    show "?F' \<subseteq> {A \<in> ?\<A>_X. \<not> A \<subseteq> T}" using hNTX_eq_F by (by100 blast)
                    show "\<forall>A\<in>?F'. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      using hps_X by (by100 blast)
                  qed
                  have "{A \<in> ?\<A>_X. \<not> A \<subseteq> T} - ?F' = {A1}"
                    using hNTX_eq_F hA1 by (by100 blast)
                  hence "T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - ?F') = ?target_U" by (by100 simp)
                  have "?U = ?X - ps ` ?F'" by (by100 blast)
                  have hsub_U: "subspace_topology ?X ?TX (?X - ps ` ?F') = subspace_topology Y TY (?X - ps ` ?F')"
                    by (rule subspace_topology_trans) (by100 blast)
                  thus ?thesis using hdr
                    \<open>T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - ?F') = ?target_U\<close>
                    \<open>?U = ?X - ps ` ?F'\<close> hsub_U by simp
                qed
                have hV_dr: "top1_deformation_retract_of_on ?V (subspace_topology Y TY ?V) ?target_V"
                proof -
                  have hdr: "top1_deformation_retract_of_on (?X - ps ` {A1})
                      (subspace_topology ?X ?TX (?X - ps ` {A1}))
                      (T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - {A1}))"
                  proof (rule graph_deformation_retract_helper[where \<A>="?\<A>_X"])
                    show "top1_is_graph_on ?X ?TX" by (rule hX_graph)
                    show "\<forall>A\<in>?\<A>_X. A \<subseteq> ?X \<and> top1_is_arc_on A (subspace_topology ?X ?TX A)"
                      by (rule h\<A>X_arcs_X)
                    show "\<Union>?\<A>_X = ?X" by (rule hX_eq_union[symmetric])
                    show "\<forall>A\<in>?\<A>_X. \<forall>B\<in>?\<A>_X. A \<noteq> B \<longrightarrow>
                        A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)
                      \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?X ?TX B)
                      \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                    proof (intro ballI impI)
                      fix A B assume "A \<in> ?\<A>_X" "B \<in> ?\<A>_X" "A \<noteq> B"
                      from h\<A>_inter[rule_format, OF _ _ \<open>A \<noteq> B\<close>]
                      have h_Y: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
                        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
                        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                        using \<open>A \<in> ?\<A>_X\<close> \<open>B \<in> ?\<A>_X\<close> by (by100 blast)
                      have "subspace_topology ?X ?TX A = subspace_topology Y TY A"
                        by (rule subspace_topology_trans) (use \<open>A \<in> ?\<A>_X\<close> in blast)
                      moreover have "subspace_topology ?X ?TX B = subspace_topology Y TY B"
                        by (rule subspace_topology_trans) (use \<open>B \<in> ?\<A>_X\<close> in blast)
                      ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)
                        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?X ?TX B)
                        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
                        using h_Y by simp
                    qed
                    show "\<forall>C. C \<subseteq> ?X \<longrightarrow> (closedin_on ?X ?TX C \<longleftrightarrow>
                        (\<forall>A\<in>?\<A>_X. closedin_on A (subspace_topology ?X ?TX A) (A \<inter> C)))"
                      by (rule h\<A>X_coh_X)
                    show "top1_is_tree_on T (subspace_topology ?X ?TX T)" by (rule hT_tree_X)
                    show "T \<subseteq> ?X" by (by100 blast)
                    show "\<forall>A\<in>?\<A>_X. \<not> A \<subseteq> T \<longrightarrow> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      using hT_subgraph_X by (by100 blast)
                    show "\<forall>A\<in>{A \<in> ?\<A>_X. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?X ?TX A). e \<in> T"
                      using hvertices_T_X hNTX_eq_F hNT_endpts_X by (by100 blast)
                    show "finite {A1}" by (by100 simp)
                    show "{A1} \<subseteq> {A \<in> ?\<A>_X. \<not> A \<subseteq> T}"
                      using hNTX_eq_F hA1 by (by100 blast)
                    show "\<forall>A\<in>{A1}. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology ?X ?TX A)"
                      using hps_X hA1 by (by100 blast)
                  qed
                  have "{A \<in> ?\<A>_X. \<not> A \<subseteq> T} - {A1} = ?F'"
                    using hNTX_eq_F by (by100 blast)
                  hence "T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - {A1}) = ?target_V" by simp
                  have "?V = ?X - ps ` {A1}" by (by100 blast)
                  have hsub_V: "subspace_topology ?X ?TX (?X - ps ` {A1}) = subspace_topology Y TY (?X - ps ` {A1})"
                    by (rule subspace_topology_trans) (by100 blast)
                  thus ?thesis using hdr
                    \<open>T \<union> \<Union>({A \<in> ?\<A>_X. \<not> A \<subseteq> T} - {A1}) = ?target_V\<close>
                    \<open>?V = ?X - ps ` {A1}\<close> hsub_V by simp
                qed
                \<comment> \<open>Step 10: Subspace topology transitivity.\<close>
                have hU_sub: "?U \<subseteq> Y" using hX_sub by (by100 blast)
                have hV_sub: "?V \<subseteq> Y" using hX_sub by (by100 blast)
                have hU_sub_X: "?U \<subseteq> ?X" by (by100 blast)
                have hV_sub_X: "?V \<subseteq> ?X" by (by100 blast)
                have hU_top_eq: "subspace_topology ?X ?TX ?U = subspace_topology Y TY ?U"
                  by (rule subspace_topology_trans[OF hU_sub_X])
                have hV_top_eq: "subspace_topology ?X ?TX ?V = subspace_topology Y TY ?V"
                  by (rule subspace_topology_trans[OF hV_sub_X])
                \<comment> \<open>Step 11: Transfer freeness to U via DR (Theorem\\_58\\_3\\_explicit + free\\_group\\_invariant\\_under\\_iso).\<close>
                have hTU_sub: "?target_U \<subseteq> ?U"
                proof -
                  have "T \<subseteq> ?X" by (by100 blast)
                  have "A1 \<subseteq> ?X" using hA1 by (by100 blast)
                  have "T \<inter> ps ` ?F' = {}"
                  proof (rule ccontr)
                    assume "\<not> ?thesis"
                    then obtain B where "B \<in> ?F'" "ps B \<in> T" by (by100 blast)
                    hence "B \<in> F" by (by100 blast)
                    have "ps B \<in> B" using hps \<open>B \<in> F\<close> by (by100 blast)
                    have "B \<in> ?NT" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                    hence "B \<in> \<A>" "\<not> B \<subseteq> T" by (by100 blast)+
                    from hT_subgraph[rule_format, OF \<open>B \<in> \<A>\<close>] \<open>\<not> B \<subseteq> T\<close>
                    have "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
                    hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>ps B \<in> B\<close> \<open>ps B \<in> T\<close> by (by100 blast)
                    thus False using hps \<open>B \<in> F\<close> by (by100 blast)
                  qed
                  moreover have "A1 \<inter> ps ` ?F' = {}"
                  proof (rule ccontr)
                    assume "\<not> ?thesis"
                    then obtain B where "B \<in> ?F'" "ps B \<in> A1" by (by100 blast)
                    hence "B \<in> F" "B \<noteq> A1" by (by100 blast)+
                    have "ps B \<in> B" using hps \<open>B \<in> F\<close> by (by100 blast)
                    have "ps B \<in> B \<inter> A1" using \<open>ps B \<in> B\<close> \<open>ps B \<in> A1\<close> by (by100 blast)
                    have "B \<in> \<A>" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                    have "A1 \<in> \<A>" using hF_NT hA1 by (by100 blast)
                    from h\<A>_inter[rule_format, OF \<open>B \<in> \<A>\<close> \<open>A1 \<in> \<A>\<close> \<open>B \<noteq> A1\<close>]
                    have "B \<inter> A1 \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
                    hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
                      using \<open>ps B \<in> B \<inter> A1\<close> by (by100 blast)
                    thus False using hps \<open>B \<in> F\<close> by (by100 blast)
                  qed
                  ultimately have "(T \<union> A1) \<inter> ps ` ?F' = {}" by (by100 blast)
                  moreover have "T \<union> A1 \<subseteq> ?X" using hA1 by (by100 blast)
                  ultimately show ?thesis by (by100 blast)
                qed
                have hy0_tU: "y0 \<in> ?target_U" using hT_x0 by (by100 blast)
                have hU_top: "is_topology_on ?U (subspace_topology Y TY ?U)"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hU_sub])
                have htU_top_eq: "subspace_topology ?U (subspace_topology Y TY ?U) ?target_U =
                    subspace_topology Y TY ?target_U"
                  by (rule subspace_topology_trans[OF hTU_sub])
                have hincl_U_iso: "top1_group_iso_on
                    (top1_fundamental_group_carrier ?target_U (subspace_topology Y TY ?target_U) y0)
                    (top1_fundamental_group_mul ?target_U (subspace_topology Y TY ?target_U) y0)
                    (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
                    (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
                    (top1_fundamental_group_induced_on ?target_U (subspace_topology Y TY ?target_U) y0
                        ?U (subspace_topology Y TY ?U) y0 (\<lambda>x. x))"
                proof -
                  note h = Theorem_58_3_explicit[OF hU_dr hU_top hy0_tU]
                  show ?thesis using h[unfolded htU_top_eq] .
                qed
                \<comment> \<open>IH\\_base gives \\<pi>\\_1(T\\<union>A1) free on {A1}. T\\<union>A1 = T\\<union>\\<Union>{A1}.\<close>
                have htU_eq: "?target_U = T \<union> \<Union>{A1}" by (by100 simp)
                have hIH_base': "\<exists>\<iota>1. top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?target_U (subspace_topology Y TY ?target_U) y0)
                    (top1_fundamental_group_mul ?target_U (subspace_topology Y TY ?target_U) y0)
                    (top1_fundamental_group_id ?target_U (subspace_topology Y TY ?target_U) y0)
                    (top1_fundamental_group_invg ?target_U (subspace_topology Y TY ?target_U) y0)
                    \<iota>1 {A1}
                  \<and> (\<forall>A\<in>{A1}. top1_fundamental_group_induced_on ?target_U
                        (subspace_topology Y TY ?target_U) y0 Y TY y0 (\<lambda>x. x) (\<iota>1 A) = gen A)"
                proof -
                  have hU1: "\<Union>{A1} = A1" by (by100 simp)
                  show ?thesis using hIH_base[unfolded hU1] .
                qed
                from hIH_base' obtain \<iota>1 where
                  h\<iota>1_free: "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?target_U (subspace_topology Y TY ?target_U) y0)
                      (top1_fundamental_group_mul ?target_U (subspace_topology Y TY ?target_U) y0)
                      (top1_fundamental_group_id ?target_U (subspace_topology Y TY ?target_U) y0)
                      (top1_fundamental_group_invg ?target_U (subspace_topology Y TY ?target_U) y0)
                      \<iota>1 {A1}"
                  and h\<iota>1_gen: "\<forall>A\<in>{A1}. top1_fundamental_group_induced_on ?target_U
                      (subspace_topology Y TY ?target_U) y0 Y TY y0 (\<lambda>x. x) (\<iota>1 A) = gen A"
                  by (by100 blast)
                \<comment> \<open>Transfer to U: \\<pi>\\_1(U) free on {A1} via incl*(\\<iota>1).\<close>
                have hy0_U: "y0 \<in> ?U" using hy0_UV by (by100 blast)
                have hU_grp: "top1_is_group_on
                    (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
                    (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
                    (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
                    (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)"
                  using top1_fundamental_group_is_group[OF hU_top hy0_U] by (by100 blast)
                from free_group_invariant_under_iso[OF h\<iota>1_free hincl_U_iso hU_grp]
                obtain \<iota>U where
                  h\<iota>U_free: "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
                      (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
                      (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
                      (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)
                      \<iota>U {A1}"
                  and h\<iota>U_track: "\<forall>s\<in>{A1}. \<iota>U s = top1_fundamental_group_induced_on ?target_U
                      (subspace_topology Y TY ?target_U) y0 ?U (subspace_topology Y TY ?U) y0 (\<lambda>x. x)
                      (\<iota>1 s)" by (by100 blast)
                \<comment> \<open>Step 12: Transfer freeness to V via DR.\<close>
                have hTV_sub: "?target_V \<subseteq> ?V"
                proof -
                  have "ps A1 \<notin> T"
                  proof -
                    have "A1 \<in> ?NT" using hF_NT hA1 by (by100 blast)
                    hence "\<not> A1 \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF _] this
                    have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using \<open>A1 \<in> ?NT\<close> by (by100 blast)
                    have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
                    have "ps A1 \<notin> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using hps hA1 by (by100 blast)
                    thus ?thesis using \<open>A1 \<inter> T \<subseteq> _\<close> \<open>ps A1 \<in> A1\<close> by (by100 blast)
                  qed
                  moreover have "ps A1 \<notin> \<Union>?F'"
                  proof
                    assume "ps A1 \<in> \<Union>?F'"
                    then obtain B where "B \<in> ?F'" "ps A1 \<in> B" by (by100 blast)
                    hence "B \<in> F" "B \<noteq> A1" by (by100 blast)+
                    have "B \<in> \<A>" using hF_NT \<open>B \<in> F\<close> by (by100 blast)
                    have "A1 \<in> \<A>" using hF_NT hA1 by (by100 blast)
                    have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
                    have "ps A1 \<in> A1 \<inter> B" using \<open>ps A1 \<in> A1\<close> \<open>ps A1 \<in> B\<close> by (by100 blast)
                    from h\<A>_inter[rule_format, OF \<open>A1 \<in> \<A>\<close> \<open>B \<in> \<A>\<close>]
                    have "A1 \<inter> B \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using \<open>B \<noteq> A1\<close> by (by100 blast)
                    hence "ps A1 \<in> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                      using \<open>ps A1 \<in> A1 \<inter> B\<close> by (by100 blast)
                    thus False using hps hA1 by (by100 blast)
                  qed
                  ultimately show ?thesis by (by100 blast)
                qed
                have hy0_tV: "y0 \<in> ?target_V" using hT_x0 by (by100 blast)
                have hV_top: "is_topology_on ?V (subspace_topology Y TY ?V)"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hV_sub])
                have htV_top_eq: "subspace_topology ?V (subspace_topology Y TY ?V) ?target_V =
                    subspace_topology Y TY ?target_V"
                  by (rule subspace_topology_trans[OF hTV_sub])
                have hincl_V_iso: "top1_group_iso_on
                    (top1_fundamental_group_carrier ?target_V (subspace_topology Y TY ?target_V) y0)
                    (top1_fundamental_group_mul ?target_V (subspace_topology Y TY ?target_V) y0)
                    (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
                    (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
                    (top1_fundamental_group_induced_on ?target_V (subspace_topology Y TY ?target_V) y0
                        ?V (subspace_topology Y TY ?V) y0 (\<lambda>x. x))"
                proof -
                  note h = Theorem_58_3_explicit[OF hV_dr hV_top hy0_tV]
                  show ?thesis using h[unfolded htV_top_eq] .
                qed
                from hIH_step obtain \<iota>' where
                  h\<iota>'_free: "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?target_V (subspace_topology Y TY ?target_V) y0)
                      (top1_fundamental_group_mul ?target_V (subspace_topology Y TY ?target_V) y0)
                      (top1_fundamental_group_id ?target_V (subspace_topology Y TY ?target_V) y0)
                      (top1_fundamental_group_invg ?target_V (subspace_topology Y TY ?target_V) y0)
                      \<iota>' ?F'"
                  and h\<iota>'_gen: "\<forall>A\<in>?F'. top1_fundamental_group_induced_on ?target_V
                      (subspace_topology Y TY ?target_V) y0 Y TY y0 (\<lambda>x. x) (\<iota>' A) = gen A"
                  by (by100 blast)
                have hy0_V: "y0 \<in> ?V" using hy0_UV by (by100 blast)
                have hV_grp: "top1_is_group_on
                    (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
                    (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
                    (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
                    (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)"
                  using top1_fundamental_group_is_group[OF hV_top hy0_V] by (by100 blast)
                from free_group_invariant_under_iso[OF h\<iota>'_free hincl_V_iso hV_grp]
                obtain \<iota>V where
                  h\<iota>V_free: "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
                      (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
                      (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
                      (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)
                      \<iota>V ?F'"
                  and h\<iota>V_track: "\<forall>s\<in>?F'. \<iota>V s = top1_fundamental_group_induced_on ?target_V
                      (subspace_topology Y TY ?target_V) y0 ?V (subspace_topology Y TY ?V) y0 (\<lambda>x. x)
                      (\<iota>' s)" by (by100 blast)
                \<comment> \<open>Step 13: Disjoint index sets.\<close>
                have hS_disj: "{A1} \<inter> ?F' = {}" by (by100 blast)
                \<comment> \<open>Step 14: Apply svk\\_free\\_product\\_free\\_with\\_generators.\<close>
                \<comment> \<open>Rewrite U, V topologies to use X's subspace.\<close>
                have h\<iota>U_free': "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?U (subspace_topology ?X ?TX ?U) y0)
                    (top1_fundamental_group_mul ?U (subspace_topology ?X ?TX ?U) y0)
                    (top1_fundamental_group_id ?U (subspace_topology ?X ?TX ?U) y0)
                    (top1_fundamental_group_invg ?U (subspace_topology ?X ?TX ?U) y0)
                    \<iota>U {A1}"
                  using h\<iota>U_free[unfolded hU_top_eq[symmetric]] .
                have h\<iota>V_free': "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?V (subspace_topology ?X ?TX ?V) y0)
                    (top1_fundamental_group_mul ?V (subspace_topology ?X ?TX ?V) y0)
                    (top1_fundamental_group_id ?V (subspace_topology ?X ?TX ?V) y0)
                    (top1_fundamental_group_invg ?V (subspace_topology ?X ?TX ?V) y0)
                    \<iota>V ?F'"
                  using h\<iota>V_free[unfolded hV_top_eq[symmetric]] .
                \<comment> \<open>Step 9b: U, V path-connected (via DR + target PC).\<close>
                have hU_pc: "top1_path_connected_on ?U (subspace_topology ?X ?TX ?U)"
                proof -
                  have "subspace_topology ?U (subspace_topology Y TY ?U) ?target_U = subspace_topology Y TY ?target_U"
                    by (rule subspace_topology_trans[OF hTU_sub])
                  moreover have "top1_path_connected_on ?target_U (subspace_topology Y TY ?target_U)"
                  proof -
                    have hA1_arc: "top1_is_arc_on A1 (subspace_topology Y TY A1)"
                      using h\<A> hF_NT hA1 by (by100 blast)
                    have hA1_sub: "A1 \<subseteq> Y" using h\<A> hF_NT hA1 by (by100 blast)
                    have "\<exists>e. e \<in> T \<and> e \<in> A1"
                    proof -
                      obtain hj where "top1_homeomorphism_on top1_unit_interval
                          top1_unit_interval_topology A1 (subspace_topology Y TY A1) hj"
                        using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
                      have hbij: "bij_betw hj top1_unit_interval A1"
                        using \<open>top1_homeomorphism_on _ _ A1 _ hj\<close>
                        unfolding top1_homeomorphism_on_def by (by100 blast)
                      from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc
                          \<open>top1_homeomorphism_on _ _ A1 _ hj\<close>]
                      have hep: "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {hj 0, hj 1}" .
                      have "A1 \<in> ?NT" using hF_NT hA1 by (by100 blast)
                      have "hj 0 \<in> T" using hNT_endpoints[rule_format, OF \<open>A1 \<in> ?NT\<close>] hep
                        by (by100 simp)
                      have h0_I: "(0::real) \<in> top1_unit_interval"
                        unfolding top1_unit_interval_def by (by100 simp)
                      have "hj 0 \<in> A1" using hbij h0_I
                        unfolding bij_betw_def by (by100 blast)
                      thus ?thesis using \<open>hj 0 \<in> T\<close> by (by100 blast)
                    qed
                    from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub _ _ _ hT_x0, of "{A1}"]
                    show ?thesis using hA1_arc hA1_sub \<open>\<exists>e. e \<in> T \<and> e \<in> A1\<close> by (by100 simp)
                  qed
                  ultimately have "top1_path_connected_on ?target_U
                      (subspace_topology ?U (subspace_topology Y TY ?U) ?target_U)" by simp
                  hence "top1_path_connected_on ?U (subspace_topology Y TY ?U)"
                    by (rule deformation_retract_path_connected[OF hU_dr hU_top])
                  thus ?thesis using hU_top_eq by simp
                qed
                have hV_pc: "top1_path_connected_on ?V (subspace_topology ?X ?TX ?V)"
                proof -
                  have "subspace_topology ?V (subspace_topology Y TY ?V) ?target_V = subspace_topology Y TY ?target_V"
                    by (rule subspace_topology_trans[OF hTV_sub])
                  moreover have "top1_path_connected_on ?target_V (subspace_topology Y TY ?target_V)"
                  proof -
                    have hF'_arcs: "\<forall>A\<in>?F'. top1_is_arc_on A (subspace_topology Y TY A) \<and> A \<subseteq> Y"
                      using h\<A> hF_NT by (by100 blast)
                    have hF'_endpts: "\<forall>A\<in>?F'. \<exists>e. e \<in> T \<and> e \<in> A"
                    proof (intro ballI)
                      fix A assume "A \<in> ?F'"
                      hence "A \<in> F" "A \<noteq> A1" by (by100 blast)+
                      have "A \<in> ?NT" using hF_NT \<open>A \<in> F\<close> by (by100 blast)
                      have harc: "top1_is_arc_on A (subspace_topology Y TY A)"
                        using h\<A> \<open>A \<in> ?NT\<close> by (by100 blast)
                      obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
                          top1_unit_interval_topology A (subspace_topology Y TY A) hj"
                        using harc unfolding top1_is_arc_on_def by (by100 blast)
                      have "A \<subseteq> Y" using h\<A> \<open>A \<in> ?NT\<close> by (by100 blast)
                      from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>A \<subseteq> Y\<close> harc hhj]
                      have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {hj 0, hj 1}" .
                      have "hj 0 \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] hep
                        by (by100 simp)
                      have hbij: "bij_betw hj top1_unit_interval A"
                        using hhj unfolding top1_homeomorphism_on_def by (by100 blast)
                      have h0_I: "(0::real) \<in> top1_unit_interval"
                        unfolding top1_unit_interval_def by (by100 simp)
                      have "hj 0 \<in> A" using hbij h0_I unfolding bij_betw_def by (by100 blast)
                      thus "\<exists>e. e \<in> T \<and> e \<in> A" using \<open>hj 0 \<in> T\<close> by (by100 blast)
                    qed
                    from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub hF'_fin
                        hF'_arcs hF'_endpts hT_x0]
                    show ?thesis .
                  qed
                  ultimately have "top1_path_connected_on ?target_V
                      (subspace_topology ?V (subspace_topology Y TY ?V) ?target_V)" by simp
                  hence "top1_path_connected_on ?V (subspace_topology Y TY ?V)"
                    by (rule deformation_retract_path_connected[OF hV_dr hV_top])
                  thus ?thesis using hV_top_eq by simp
                qed
                from svk_free_product_free_with_generators[OF hX_strict hU_open hV_open hUV_cover
                    hUV_sc hU_pc hV_pc hy0_UV h\<iota>U_free' h\<iota>V_free' hS_disj]
                obtain \<iota>X where
                  h\<iota>X_free: "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?X ?TX y0) (top1_fundamental_group_mul ?X ?TX y0)
                      (top1_fundamental_group_id ?X ?TX y0) (top1_fundamental_group_invg ?X ?TX y0)
                      \<iota>X ({A1} \<union> ?F')"
                  and h\<iota>X_trackU: "\<forall>s\<in>{A1}. \<iota>X s = top1_fundamental_group_induced_on ?U
                      (subspace_topology ?X ?TX ?U) y0 ?X ?TX y0 (\<lambda>x. x) (\<iota>U s)"
                  and h\<iota>X_trackV: "\<forall>s\<in>?F'. \<iota>X s = top1_fundamental_group_induced_on ?V
                      (subspace_topology ?X ?TX ?V) y0 ?X ?TX y0 (\<lambda>x. x) (\<iota>V s)"
                  by (by100 blast)
                \<comment> \<open>Step 15: {A1} \\<union> F' = F.\<close>
                have hF_eq: "{A1} \<union> ?F' = F" using hA1 by (by100 blast)
                \<comment> \<open>Step 16: Generator tracking: incl\\_{X\\<rightarrow>Y}*(\\<iota>X(A)) = gen(A).\<close>
                have hgen_track: "\<forall>A\<in>F. top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x)
                    (\<iota>X A) = gen A"
                proof (intro ballI)
                  fix A assume "A \<in> F"
                  show "top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x) (\<iota>X A) = gen A"
                  proof (cases "A = A1")
                    case True
                    \<comment> \<open>Chain: incl\\_{X\\<rightarrow>Y}*(\\<iota>X(A1)) = incl\\_{X\\<rightarrow>Y}*(incl\\_{U\\<rightarrow>X}*(\\<iota>U(A1)))
                       = incl\\_{U\\<rightarrow>Y}*(\\<iota>U(A1)) = incl\\_{U\\<rightarrow>Y}*(incl\\_{tU\\<rightarrow>U}*(\\<iota>1(A1)))
                       = incl\\_{tU\\<rightarrow>Y}*(\\<iota>1(A1)) = gen(A1).\<close>
                    \<comment> \<open>Step a: \\<iota>X(A1) = incl\\_{U\\<rightarrow>X}*(\\<iota>U(A1)) (from SvK tracking).\<close>
                    have ha: "\<iota>X A1 = top1_fundamental_group_induced_on ?U
                        (subspace_topology Y TY ?U) y0 ?X ?TX y0 (\<lambda>x. x) (\<iota>U A1)"
                      using h\<iota>X_trackU hU_top_eq by (by100 simp)
                    \<comment> \<open>Step b: \\<iota>U(A1) = incl\\_{tU\\<rightarrow>U}*(\\<iota>1(A1)) (from DR transfer tracking).\<close>
                    have hb: "\<iota>U A1 = top1_fundamental_group_induced_on ?target_U
                        (subspace_topology Y TY ?target_U) y0 ?U (subspace_topology Y TY ?U) y0 (\<lambda>x. x)
                        (\<iota>1 A1)"
                      using h\<iota>U_track by (by100 blast)
                    \<comment> \<open>Step c: \\<iota>1(A1) \\<in> carrier(target\\_U) (from IH\\_base freeness).\<close>
                    have hc: "\<iota>1 A1 \<in> top1_fundamental_group_carrier ?target_U (subspace_topology Y TY ?target_U) y0"
                      using h\<iota>1_free unfolding top1_is_free_group_full_on_def by (by100 blast)
                    \<comment> \<open>Step d: Compose inclusions using inclusion\\_induced\\_comp.\<close>
                    \<comment> \<open>First: incl\\_{U\\<rightarrow>Y}* \\<circ> incl\\_{tU\\<rightarrow>U}* = incl\\_{tU\\<rightarrow>Y}*.\<close>
                    have hcomp1: "top1_fundamental_group_induced_on ?U (subspace_topology Y TY ?U) y0
                        Y TY y0 (\<lambda>x. x)
                        (top1_fundamental_group_induced_on ?target_U (subspace_topology Y TY ?target_U) y0
                            ?U (subspace_topology Y TY ?U) y0 (\<lambda>x. x) (\<iota>1 A1))
                      = top1_fundamental_group_induced_on ?target_U (subspace_topology Y TY ?target_U) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>1 A1)"
                      by (rule inclusion_induced_comp[OF hTY_top hTU_sub hU_sub hy0_tU hc])
                    \<comment> \<open>Second: incl\\_{X\\<rightarrow>Y}* \\<circ> incl\\_{U\\<rightarrow>X}* = incl\\_{U\\<rightarrow>Y}*.\<close>
                    have h\<iota>U_carrier: "\<iota>U A1 \<in> top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0"
                      using h\<iota>U_free unfolding top1_is_free_group_full_on_def by (by100 blast)
                    have hcomp2: "top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x)
                        (top1_fundamental_group_induced_on ?U (subspace_topology Y TY ?U) y0
                            ?X ?TX y0 (\<lambda>x. x) (\<iota>U A1))
                      = top1_fundamental_group_induced_on ?U (subspace_topology Y TY ?U) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>U A1)"
                      by (rule inclusion_induced_comp[OF hTY_top hU_sub_X hX_sub hy0_U h\<iota>U_carrier])
                    \<comment> \<open>Combine: incl\\_{X\\<rightarrow>Y}*(\\<iota>X(A1)) = gen(A1).\<close>
                    have "top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x) (\<iota>X A1)
                      = top1_fundamental_group_induced_on ?target_U (subspace_topology Y TY ?target_U) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>1 A1)"
                      using ha hb hcomp1 hcomp2 by (by100 simp)
                    also have "... = gen A1" using h\<iota>1_gen by (by100 blast)
                    finally show ?thesis using True by simp
                  next
                    case False
                    hence "A \<in> ?F'" using \<open>A \<in> F\<close> by (by100 blast)
                    \<comment> \<open>Same chain via V instead of U.\<close>
                    have ha: "\<iota>X A = top1_fundamental_group_induced_on ?V
                        (subspace_topology Y TY ?V) y0 ?X ?TX y0 (\<lambda>x. x) (\<iota>V A)"
                      using h\<iota>X_trackV \<open>A \<in> ?F'\<close> hV_top_eq by (by100 simp)
                    have hb: "\<iota>V A = top1_fundamental_group_induced_on ?target_V
                        (subspace_topology Y TY ?target_V) y0 ?V (subspace_topology Y TY ?V) y0 (\<lambda>x. x)
                        (\<iota>' A)"
                      using h\<iota>V_track \<open>A \<in> ?F'\<close> by (by100 blast)
                    have hc: "\<iota>' A \<in> top1_fundamental_group_carrier ?target_V (subspace_topology Y TY ?target_V) y0"
                      using h\<iota>'_free \<open>A \<in> ?F'\<close> unfolding top1_is_free_group_full_on_def by (by100 blast)
                    have hcomp1: "top1_fundamental_group_induced_on ?V (subspace_topology Y TY ?V) y0
                        Y TY y0 (\<lambda>x. x)
                        (top1_fundamental_group_induced_on ?target_V (subspace_topology Y TY ?target_V) y0
                            ?V (subspace_topology Y TY ?V) y0 (\<lambda>x. x) (\<iota>' A))
                      = top1_fundamental_group_induced_on ?target_V (subspace_topology Y TY ?target_V) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>' A)"
                      by (rule inclusion_induced_comp[OF hTY_top hTV_sub hV_sub hy0_tV hc])
                    have h\<iota>V_carrier: "\<iota>V A \<in> top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0"
                      using h\<iota>V_free \<open>A \<in> ?F'\<close> unfolding top1_is_free_group_full_on_def by (by100 blast)
                    have hcomp2: "top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x)
                        (top1_fundamental_group_induced_on ?V (subspace_topology Y TY ?V) y0
                            ?X ?TX y0 (\<lambda>x. x) (\<iota>V A))
                      = top1_fundamental_group_induced_on ?V (subspace_topology Y TY ?V) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>V A)"
                      by (rule inclusion_induced_comp[OF hTY_top hV_sub_X hX_sub hy0_V h\<iota>V_carrier])
                    have "top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x) (\<iota>X A)
                      = top1_fundamental_group_induced_on ?target_V (subspace_topology Y TY ?target_V) y0
                            Y TY y0 (\<lambda>x. x) (\<iota>' A)"
                      using ha hb hcomp1 hcomp2 by (by100 simp)
                    also have "... = gen A" using h\<iota>'_gen \<open>A \<in> ?F'\<close> by (by100 blast)
                    finally show ?thesis .
                  qed
                qed
                show ?thesis
                proof (rule exI[of _ \<iota>X], rule conjI)
                  show "top1_is_free_group_full_on
                      (top1_fundamental_group_carrier ?X ?TX y0) (top1_fundamental_group_mul ?X ?TX y0)
                      (top1_fundamental_group_id ?X ?TX y0) (top1_fundamental_group_invg ?X ?TX y0)
                      \<iota>X F" using h\<iota>X_free[unfolded hF_eq] .
                  show "\<forall>A\<in>F. top1_fundamental_group_induced_on ?X ?TX y0 Y TY y0 (\<lambda>x. x) (\<iota>X A) = gen A"
                    using hgen_track by (by100 blast)
                qed
                qed  \<comment> \<open>cases card F = 1\<close>
              qed  \<comment> \<open>P_def intro\<close>
            qed  \<comment> \<open>less.induction case\<close>
          }
          hence hP: "\<And>F. P F"
            by (by5000 blast)
          fix F assume hFfin: "finite F" and hF_NT: "F \<subseteq> ?NT" and hF_ne: "F \<noteq> {}"
          from hP[of F, unfolded P_def] hFfin hF_NT hF_ne
          show "\<exists>\<iota>F. top1_is_free_group_full_on
              (top1_fundamental_group_carrier (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_mul (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_id (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              (top1_fundamental_group_invg (T \<union> \<Union>F) (subspace_topology Y TY (T \<union> \<Union>F)) y0)
              \<iota>F F
            \<and> (\<forall>A\<in>F. top1_fundamental_group_induced_on (T \<union> \<Union>F)
                  (subspace_topology Y TY (T \<union> \<Union>F)) y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A)"
            by (by100 blast)
        qed
        \<comment> \<open>Index ?NT by nat.\<close>
        have "\<exists>(idx :: _ \<Rightarrow> nat) (S :: nat set). bij_betw idx ?NT S"
          sorry \<comment> \<open>Any set can be injected into nat (with appropriate cardinality).
             For finite sets: obvious. For countable: standard. For uncountable: would need larger type.\<close>
        then obtain idx :: "'a set \<Rightarrow> nat" and S :: "nat set"
          where hidx: "bij_betw idx ?NT S" by (by100 blast)
        \<comment> \<open>Define \\<iota>: nat \\<rightarrow> carrier.\<close>
        define \<iota> where "\<iota> n = gen (the_inv_into ?NT idx n)" for n
        \<comment> \<open>Verify 5 conditions of free\\_group\\_full\\_on.\<close>
        have "top1_is_free_group_full_on
            (top1_fundamental_group_carrier Y TY y0)
            (top1_fundamental_group_mul Y TY y0)
            (top1_fundamental_group_id Y TY y0)
            (top1_fundamental_group_invg Y TY y0)
            \<iota> S"
          unfolding top1_is_free_group_full_on_def
        proof (intro conjI)
          \<comment> \<open>1. Group.\<close>
          show "top1_is_group_on
              (top1_fundamental_group_carrier Y TY y0)
              (top1_fundamental_group_mul Y TY y0)
              (top1_fundamental_group_id Y TY y0)
              (top1_fundamental_group_invg Y TY y0)"
            by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
          \<comment> \<open>2. Generators in carrier.\<close>
          show "\<forall>s\<in>S. \<iota> s \<in> top1_fundamental_group_carrier Y TY y0"
          proof (intro ballI)
            fix s assume "s \<in> S"
            from bij_betw_imp_surj_on[OF hidx]
            have "S \<subseteq> idx ` ?NT" by (by100 blast)
            hence "s \<in> idx ` ?NT" using \<open>s \<in> S\<close> by (by100 blast)
            then obtain A where "A \<in> ?NT" "idx A = s" by (by100 blast)
            have "the_inv_into ?NT idx s = A"
              using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                \<open>idx A = s\<close> by (by100 simp)
            hence "\<iota> s = gen A" unfolding \<iota>_def by (by100 simp)
            from hgen[rule_format, OF \<open>A \<in> ?NT\<close>]
            show "\<iota> s \<in> top1_fundamental_group_carrier Y TY y0"
              using \<open>\<iota> s = gen A\<close> by (by100 simp)
          qed
          \<comment> \<open>3. Injective.\<close>
          show "inj_on \<iota> S"
          proof -
            \<comment> \<open>gen is injective on ?NT: different arcs give different classes.
               For A \\<noteq> B in ?NT: gen(A) \\<noteq> gen(B) because they're free generators
               of \\<pi>\\_1(T \\<union> A \\<union> B), which is free of rank 2.\<close>
            have hgen_inj: "inj_on gen ?NT"
            proof (rule inj_onI)
              fix A B assume "A \<in> ?NT" "B \<in> ?NT" "gen A = gen B"
              show "A = B"
              proof (rule ccontr)
                assume "A \<noteq> B"
                let ?F = "{A, B}"
                have "finite ?F" by (by100 simp)
                have "?F \<subseteq> ?NT" using \<open>A \<in> ?NT\<close> \<open>B \<in> ?NT\<close> by (by100 blast)
                have "?F \<noteq> {}" by (by100 blast)
                let ?YAB = "T \<union> \<Union>?F"
                let ?TYAB = "subspace_topology Y TY ?YAB"
                from harc_loops_free[OF \<open>finite ?F\<close> \<open>?F \<subseteq> ?NT\<close> \<open>?F \<noteq> {}\<close>]
                obtain \<iota>F where hfreeF: "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?YAB ?TYAB y0)
                    (top1_fundamental_group_mul ?YAB ?TYAB y0)
                    (top1_fundamental_group_id ?YAB ?TYAB y0)
                    (top1_fundamental_group_invg ?YAB ?TYAB y0) \<iota>F ?F"
                    and hgenF: "\<forall>C\<in>?F. top1_fundamental_group_induced_on
                        ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x) (\<iota>F C) = gen C"
                  by (by100 blast)
                \<comment> \<open>In the free group, \\<iota>\\_F(A) \\<noteq> \\<iota>\\_F(B) since A \\<noteq> B and \\<iota>\\_F injective.\<close>
                have "inj_on \<iota>F ?F"
                proof -
                  from hfreeF[unfolded top1_is_free_group_full_on_def]
                  show ?thesis by (by5000 blast)
                qed
                hence "\<iota>F A \<noteq> \<iota>F B" using \<open>A \<noteq> B\<close> by (by100 blast)
                \<comment> \<open>But incl(\\<iota>\\_F(A)) = gen(A) = gen(B) = incl(\\<iota>\\_F(B)).
                   By hincl\\_inj: inclusion injective. So \\<iota>\\_F(A) = \\<iota>\\_F(B). Contradiction.\<close>
                have hgenFA: "top1_fundamental_group_induced_on ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) = gen A"
                  using hgenF by (by100 blast)
                have hgenFB: "top1_fundamental_group_induced_on ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x) (\<iota>F B) = gen B"
                  using hgenF by (by100 blast)
                have hincl_eq: "top1_fundamental_group_induced_on ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x) (\<iota>F A) =
                    top1_fundamental_group_induced_on ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x) (\<iota>F B)"
                  using hgenFA hgenFB \<open>gen A = gen B\<close> by (by100 simp)
                \<comment> \<open>Both \\<iota>\\_F(A), \\<iota>\\_F(B) \\<in> carrier. hincl\\_inj: incl injective on carrier.\<close>
                \<comment> \<open>By hincl\\_inj: the inclusion \\<pi>\\_1(T \\<union> A \\<union> B) \\<rightarrow> \\<pi>\\_1(Y) is injective.
                   Since incl(\\<iota>\\_F A) = incl(\\<iota>\\_F B), we get \\<iota>\\_F A = \\<iota>\\_F B.\<close>
                have "\<iota>F A = \<iota>F B"
                proof -
                  have "?F \<subseteq> ?NT" using \<open>A \<in> ?NT\<close> \<open>B \<in> ?NT\<close> by (by100 blast)
                  have hinj: "inj_on (top1_fundamental_group_induced_on ?YAB ?TYAB y0 Y TY y0 (\<lambda>x. x))
                      (top1_fundamental_group_carrier ?YAB ?TYAB y0)"
                    using hincl_inj[OF \<open>finite ?F\<close> \<open>?F \<subseteq> ?NT\<close> \<open>?F \<noteq> {}\<close>] by (by100 blast)
                  have hA_c: "\<iota>F A \<in> top1_fundamental_group_carrier ?YAB ?TYAB y0"
                  proof -
                    from hfreeF[unfolded top1_is_free_group_full_on_def]
                    have "A \<in> ?F \<Longrightarrow> \<iota>F A \<in> top1_fundamental_group_carrier ?YAB ?TYAB y0"
                      by (by5000 blast)
                    thus ?thesis by (by100 blast)
                  qed
                  have hB_c: "\<iota>F B \<in> top1_fundamental_group_carrier ?YAB ?TYAB y0"
                  proof -
                    from hfreeF[unfolded top1_is_free_group_full_on_def]
                    have "B \<in> ?F \<Longrightarrow> \<iota>F B \<in> top1_fundamental_group_carrier ?YAB ?TYAB y0"
                      by (by5000 blast)
                    thus ?thesis by (by100 blast)
                  qed
                  show ?thesis using hinj hA_c hB_c hincl_eq
                    unfolding inj_on_def by (by5000 blast)
                qed
                thus False using \<open>\<iota>F A \<noteq> \<iota>F B\<close> by contradiction
              qed
            qed
            \<comment> \<open>\\<iota> = gen \\<circ> the\\_inv\\_into ?NT idx. Injective since gen inj and the\\_inv\\_into bij.\<close>
            show ?thesis
            proof (rule inj_onI)
              fix s1 s2 assume "s1 \<in> S" "s2 \<in> S" "\<iota> s1 = \<iota> s2"
              have hs1_NT: "the_inv_into ?NT idx s1 \<in> ?NT"
              proof -
                from bij_betw_imp_surj_on[OF hidx] \<open>s1 \<in> S\<close>
                have "s1 \<in> idx ` ?NT" by (by100 blast)
                then obtain A where "A \<in> ?NT" "idx A = s1" by (by100 blast)
                have "the_inv_into ?NT idx s1 = A"
                  using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                    \<open>idx A = s1\<close> by (by100 simp)
                thus ?thesis using \<open>A \<in> ?NT\<close> by (by100 simp)
              qed
              have hs2_NT: "the_inv_into ?NT idx s2 \<in> ?NT"
              proof -
                from bij_betw_imp_surj_on[OF hidx] \<open>s2 \<in> S\<close>
                have "s2 \<in> idx ` ?NT" by (by100 blast)
                then obtain A where "A \<in> ?NT" "idx A = s2" by (by100 blast)
                have "the_inv_into ?NT idx s2 = A"
                  using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                    \<open>idx A = s2\<close> by (by100 simp)
                thus ?thesis using \<open>A \<in> ?NT\<close> by (by100 simp)
              qed
              from \<open>\<iota> s1 = \<iota> s2\<close>
              have "gen (the_inv_into ?NT idx s1) = gen (the_inv_into ?NT idx s2)"
                unfolding \<iota>_def by (by100 simp)
              have "the_inv_into ?NT idx s1 = the_inv_into ?NT idx s2"
                using hgen_inj hs1_NT hs2_NT \<open>gen _ = gen _\<close>
                unfolding inj_on_def by (by5000 blast)
              have heq1: "idx (the_inv_into ?NT idx s1) = s1"
                using f_the_inv_into_f[OF bij_betw_imp_inj_on[OF hidx]]
                  bij_betw_imp_surj_on[OF hidx] \<open>s1 \<in> S\<close> by (by100 blast)
              have heq2: "idx (the_inv_into ?NT idx s2) = s2"
                using f_the_inv_into_f[OF bij_betw_imp_inj_on[OF hidx]]
                  bij_betw_imp_surj_on[OF hidx] \<open>s2 \<in> S\<close> by (by100 blast)
              from \<open>the_inv_into ?NT idx s1 = the_inv_into ?NT idx s2\<close>
              have "idx (the_inv_into ?NT idx s1) = idx (the_inv_into ?NT idx s2)"
                by (by100 simp)
              thus "s1 = s2" using heq1 heq2 by (by100 simp)
            qed
          qed
          \<comment> \<open>4. Generated.\<close>
          show "top1_fundamental_group_carrier Y TY y0 =
              top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                  (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                  (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)"
          proof (rule set_eqI, rule iffI)
            fix c assume "c \<in> top1_fundamental_group_carrier Y TY y0"
            \<comment> \<open>c = [\\<alpha>] for some loop \\<alpha>. By hloop\\_in\\_finite: \\<alpha> lies in T \\<union> \\<Union>F for finite F.
               By harc\\_loops\\_free: \\<pi>\\_1(T\\<union>\\<Union>F) free on F with generators matching gen.
               By hom\\_image\\_in\\_subgroup\\_from\\_generators: inclusion maps into subgroup\\_gen({gen(A)}).
               Since {gen(A) | A \\<in> F} \\<subseteq> {\\<iota>(s) | s \\<in> S}: c \\<in> subgroup\\_gen(\\<iota>`S).\<close>
            show "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)"
            proof -
              \<comment> \<open>Extract representative loop from c.\<close>
              from \<open>c \<in> _\<close>[unfolded top1_fundamental_group_carrier_def]
              obtain \<alpha> where h\<alpha>_loop: "top1_is_loop_on Y TY y0 \<alpha>"
                  and hc_eq: "c = {g. top1_loop_equiv_on Y TY y0 \<alpha> g}"
                by (by100 blast)
              \<comment> \<open>By hloop\\_in\\_finite: \\<alpha> lies in T \\<union> \\<Union>F for some finite F.\<close>
              from hloop_in_finite[OF h\<alpha>_loop]
              obtain F0 where hF0_fin: "finite F0" and hF0_NT: "F0 \<subseteq> ?NT"
                  and hF0_img: "\<alpha> ` top1_unit_interval \<subseteq> T \<union> \<Union>F0"
                by (by100 blast)
              \<comment> \<open>Handle F0 = {} case: \\<alpha> lies entirely in T, which is SC \\<Rightarrow> [\\<alpha>] = id.\<close>
              show ?thesis
              proof (cases "F0 = {}")
                case True
                \<comment> \<open>\\<alpha> lies in T, which is SC. So [\\<alpha>] = id \\<in> subgroup\\_generated.\<close>
                \<comment> \<open>\\<alpha> lies in T (since T \\<union> \\<Union>{} = T). T is SC, so [\\<alpha>] = id.\<close>
                show ?thesis
                proof -
                  \<comment> \<open>\\<alpha> maps into T (since T \\<union> \\<Union>{} = T).\<close>
                  have "T \<union> \<Union>F0 = T" using True by (by100 simp)
                  hence h\<alpha>_in_T: "\<alpha> ` top1_unit_interval \<subseteq> T" using hF0_img by (by100 simp)
                  \<comment> \<open>\\<alpha> is a loop in T.\<close>
                  have h\<alpha>_T: "top1_is_loop_on T (subspace_topology Y TY T) y0 \<alpha>"
                  proof -
                    have "top1_continuous_map_on I_set I_top Y TY \<alpha>"
                      using h\<alpha>_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)
                    from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTY_top hTY_top,
                        rule_format] this h\<alpha>_in_T hT_sub
                    have "top1_continuous_map_on I_set I_top T (subspace_topology Y TY T) \<alpha>"
                      by (by100 blast)
                    moreover have "\<alpha> 0 = y0" "\<alpha> 1 = y0"
                      using h\<alpha>_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)+
                    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                      by (by100 blast)
                  qed
                  \<comment> \<open>T is SC: [\\<alpha>] = id in \\<pi>\\_1(T).\<close>
                  have hT_sc: "top1_simply_connected_on T (subspace_topology Y TY T)"
                    using hT_tree unfolding top1_is_tree_on_def by (by100 blast)
                  have h\<alpha>_trivial_T: "top1_path_homotopic_on T (subspace_topology Y TY T) y0 y0
                      \<alpha> (top1_constant_path y0)"
                    using hT_sc h\<alpha>_T hT_x0
                    unfolding top1_simply_connected_on_def by (by100 blast)
                  \<comment> \<open>Lift to Y: [\\<alpha>] = [const] = id in \\<pi>\\_1(Y).\<close>
                  from path_homotopic_subspace_to_ambient[OF hTY_top hT_sub _ h\<alpha>_trivial_T]
                  have "top1_path_homotopic_on Y TY y0 y0 \<alpha> (top1_constant_path y0)"
                    by (by100 blast)
                  hence hc_is_id: "c = top1_fundamental_group_id Y TY y0"
                  proof -
                    \<comment> \<open>loop\\_equiv(\\<alpha>, const) from \\<alpha> \\<simeq> const + both loops.\<close>
                    have hconst_loop: "top1_is_loop_on Y TY y0 (top1_constant_path y0)"
                      by (rule top1_constant_path_is_loop[OF hTY_top assms(3)])
                    have h\<alpha>_const: "top1_loop_equiv_on Y TY y0 \<alpha> (top1_constant_path y0)"
                      unfolding top1_loop_equiv_on_def
                      using h\<alpha>_loop hconst_loop
                          \<open>top1_path_homotopic_on Y TY y0 y0 \<alpha> (top1_constant_path y0)\<close>
                      by (by100 blast)
                    \<comment> \<open>Equivalence classes of \\<alpha> and const coincide.\<close>
                    have "\<forall>g. top1_loop_equiv_on Y TY y0 \<alpha> g \<longleftrightarrow>
                        top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g"
                    proof (intro allI iffI)
                      fix g assume "top1_loop_equiv_on Y TY y0 \<alpha> g"
                      from top1_loop_equiv_on_trans[OF hTY_top
                          top1_loop_equiv_on_sym[OF h\<alpha>_const] this]
                      show "top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g" .
                    next
                      fix g assume "top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g"
                      from top1_loop_equiv_on_trans[OF hTY_top h\<alpha>_const this]
                      show "top1_loop_equiv_on Y TY y0 \<alpha> g" .
                    qed
                    thus ?thesis unfolding hc_eq top1_fundamental_group_id_def by (by100 blast)
                  qed
                  \<comment> \<open>id \\<in> subgroup\\_generated (identity is always in generated subgroup).\<close>
                  have hY_grp: "top1_is_group_on (top1_fundamental_group_carrier Y TY y0)
                      (top1_fundamental_group_mul Y TY y0)
                      (top1_fundamental_group_id Y TY y0)
                      (top1_fundamental_group_invg Y TY y0)"
                    by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
                  have h\<iota>_sub_loc2: "\<iota> ` S \<subseteq> top1_fundamental_group_carrier Y TY y0"
                  proof
                    fix x assume "x \<in> \<iota> ` S"
                    then obtain s where "s \<in> S" "x = \<iota> s" by (by100 blast)
                    from bij_betw_imp_surj_on[OF hidx] \<open>s \<in> S\<close>
                    obtain A where "A \<in> ?NT" "idx A = s" by (by100 blast)
                    have "the_inv_into ?NT idx s = A"
                      using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                        \<open>idx A = s\<close> by (by100 simp)
                    hence "\<iota> s = gen A" unfolding \<iota>_def by (by100 simp)
                    thus "x \<in> top1_fundamental_group_carrier Y TY y0"
                      using \<open>x = \<iota> s\<close> hgen[rule_format, OF \<open>A \<in> ?NT\<close>] by (by100 simp)
                  qed
                  have hSG_grp2: "top1_is_group_on
                      (top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                          (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                          (top1_fundamental_group_invg Y TY y0) (\<iota> ` S))
                      (top1_fundamental_group_mul Y TY y0)
                      (top1_fundamental_group_id Y TY y0)
                      (top1_fundamental_group_invg Y TY y0)"
                    by (rule intersection_of_subgroups_is_group[OF hY_grp h\<iota>_sub_loc2])
                  have "top1_fundamental_group_id Y TY y0 \<in>
                      top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                          (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                          (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)"
                    using hSG_grp2 unfolding top1_is_group_on_def by (by100 blast)
                  thus ?thesis using hc_is_id by (by100 simp)
                qed
              next
                case False
                let ?YF0 = "T \<union> \<Union>F0" and ?TYF0 = "subspace_topology Y TY (T \<union> \<Union>F0)"
                have hYF0_sub: "?YF0 \<subseteq> Y" using hT_sub h\<A> hF0_NT by (by100 blast)
                \<comment> \<open>\\<alpha> is a loop in T \\<union> \\<Union>F0.\<close>
                have h\<alpha>_F0: "top1_is_loop_on ?YF0 ?TYF0 y0 \<alpha>"
                proof -
                  have "\<alpha> ` top1_unit_interval \<subseteq> ?YF0" using hF0_img by (by100 blast)
                  have "top1_continuous_map_on I_set I_top Y TY \<alpha>"
                    using h\<alpha>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTY_top hTY_top,
                      rule_format] this \<open>\<alpha> ` _ \<subseteq> ?YF0\<close> hYF0_sub
                  have "top1_continuous_map_on I_set I_top ?YF0 ?TYF0 \<alpha>" by (by100 blast)
                  moreover have "\<alpha> 0 = y0" "\<alpha> 1 = y0"
                    using h\<alpha>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                  ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                    by (by100 blast)
                qed
                let ?c_F0 = "{g. top1_loop_equiv_on ?YF0 ?TYF0 y0 \<alpha> g}"
                have hc_F0_carrier: "?c_F0 \<in> top1_fundamental_group_carrier ?YF0 ?TYF0 y0"
                  unfolding top1_fundamental_group_carrier_def using h\<alpha>_F0 by (by100 blast)
                let ?incl_F0 = "top1_fundamental_group_induced_on ?YF0 ?TYF0 y0 Y TY y0 (\<lambda>x. x)"
                have hincl_c: "?incl_F0 ?c_F0 = c"
                proof -
                  from subspace_inclusion_induced_class[OF hTY_top hYF0_sub h\<alpha>_F0]
                  have "?incl_F0 ?c_F0 = {k. top1_loop_equiv_on Y TY y0 \<alpha> k}" .
                  thus ?thesis using hc_eq by (by100 simp)
                qed
                \<comment> \<open>By harc\\_loops\\_free: \\<pi>\\_1(T\\<union>\\<Union>F0) is free on F0 with gen correspondence.\<close>
                from harc_loops_free[OF hF0_fin hF0_NT False]
                obtain \<iota>F0 where hfreeF0: "top1_is_free_group_full_on
                    (top1_fundamental_group_carrier ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_mul ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_id ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_invg ?YF0 ?TYF0 y0)
                    \<iota>F0 F0"
                    and hgenF0: "\<forall>A\<in>F0. ?incl_F0 (\<iota>F0 A) = gen A"
                  by (by100 blast)
                \<comment> \<open>\\<pi>\\_1(T\\<union>\\<Union>F0) = subgroup\\_generated({\\<iota>\\_F0(A) | A \\<in> F0}).\<close>
                have hF0_gen: "top1_fundamental_group_carrier ?YF0 ?TYF0 y0 =
                    top1_subgroup_generated_on
                        (top1_fundamental_group_carrier ?YF0 ?TYF0 y0)
                        (top1_fundamental_group_mul ?YF0 ?TYF0 y0)
                        (top1_fundamental_group_id ?YF0 ?TYF0 y0)
                        (top1_fundamental_group_invg ?YF0 ?TYF0 y0)
                        (\<iota>F0 ` F0)"
                proof -
                  from hfreeF0[unfolded top1_is_free_group_full_on_def]
                  show ?thesis by (by5000 blast)
                qed
                \<comment> \<open>incl* maps {\\<iota>\\_F0(A)} to {gen(A)} \\<subseteq> {\\<iota>(s)} = \\<iota>`S.\<close>
                have hincl_gens: "?incl_F0 ` (\<iota>F0 ` F0) \<subseteq> \<iota> ` S"
                proof
                  fix x assume "x \<in> ?incl_F0 ` (\<iota>F0 ` F0)"
                  then obtain A where "A \<in> F0" "x = ?incl_F0 (\<iota>F0 A)" by (by100 blast)
                  have "?incl_F0 (\<iota>F0 A) = gen A" using hgenF0 \<open>A \<in> F0\<close> by (by100 blast)
                  have "A \<in> ?NT" using hF0_NT \<open>A \<in> F0\<close> by (by100 blast)
                  have "idx A \<in> S" using bij_betw_imp_surj_on[OF hidx] \<open>A \<in> ?NT\<close>
                    using hidx unfolding bij_betw_def by (by100 blast)
                  have "the_inv_into ?NT idx (idx A) = A"
                    using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>] by (by100 simp)
                  hence "\<iota> (idx A) = gen A" unfolding \<iota>_def gen_def by (by100 simp)
                  hence "x = \<iota> (idx A)" using \<open>x = ?incl_F0 (\<iota>F0 A)\<close> \<open>?incl_F0 (\<iota>F0 A) = gen A\<close>
                    by (by100 simp)
                  thus "x \<in> \<iota> ` S" using \<open>idx A \<in> S\<close> by (by100 blast)
                qed
                \<comment> \<open>By hom\\_image\\_in\\_subgroup\\_from\\_generators:
                   incl*(\\<pi>\\_1(T\\<union>\\<Union>F0)) \\<subseteq> subgroup\\_generated(\\<iota>`S).\<close>
                \<comment> \<open>c = incl*(?c\\_F0) \\<in> incl*(\\<pi>\\_1(T\\<union>\\<Union>F0)) \\<subseteq> subgroup\\_gen(\\<iota>`S).\<close>
                \<comment> \<open>incl* is a hom from \\<pi>\\_1(T\\<union>\\<Union>F0) to \\<pi>\\_1(Y).\<close>
                have hincl_hom: "top1_group_hom_on
                    (top1_fundamental_group_carrier ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_mul ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_carrier Y TY y0)
                    (top1_fundamental_group_mul Y TY y0)
                    ?incl_F0"
                  using subspace_inclusion_induced_hom[OF hTY_top hYF0_sub]
                    hT_x0 by (by100 blast)
                have hF0_grp: "top1_is_group_on
                    (top1_fundamental_group_carrier ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_mul ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_id ?YF0 ?TYF0 y0)
                    (top1_fundamental_group_invg ?YF0 ?TYF0 y0)"
                  using hfreeF0 unfolding top1_is_free_group_full_on_def by (by100 blast)
                have hY_grp: "top1_is_group_on
                    (top1_fundamental_group_carrier Y TY y0)
                    (top1_fundamental_group_mul Y TY y0)
                    (top1_fundamental_group_id Y TY y0)
                    (top1_fundamental_group_invg Y TY y0)"
                  by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
                \<comment> \<open>subgroup\\_generated(\\<iota>`S) is a subgroup of \\<pi>\\_1(Y) containing incl*(\\<iota>\\_F0`F0).\<close>
                let ?SG = "top1_subgroup_generated_on
                    (top1_fundamental_group_carrier Y TY y0)
                    (top1_fundamental_group_mul Y TY y0)
                    (top1_fundamental_group_id Y TY y0)
                    (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)"
                have h\<iota>F0_sub: "\<iota>F0 ` F0 \<subseteq> top1_fundamental_group_carrier ?YF0 ?TYF0 y0"
                proof -
                  from hfreeF0[unfolded top1_is_free_group_full_on_def]
                  show ?thesis by (by5000 blast)
                qed
                have h\<iota>_sub_loc: "\<iota> ` S \<subseteq> top1_fundamental_group_carrier Y TY y0"
                proof
                  fix x assume "x \<in> \<iota> ` S"
                  then obtain s where "s \<in> S" "x = \<iota> s" by (by100 blast)
                  from bij_betw_imp_surj_on[OF hidx] \<open>s \<in> S\<close>
                  obtain A where "A \<in> ?NT" "idx A = s" by (by100 blast)
                  have "the_inv_into ?NT idx s = A"
                    using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                      \<open>idx A = s\<close> by (by100 simp)
                  hence "\<iota> s = gen A" unfolding \<iota>_def by (by100 simp)
                  thus "x \<in> top1_fundamental_group_carrier Y TY y0"
                    using \<open>x = \<iota> s\<close> hgen[rule_format, OF \<open>A \<in> ?NT\<close>] by (by100 simp)
                qed
                have hSG_sub: "?SG \<subseteq> top1_fundamental_group_carrier Y TY y0"
                  using subgroup_generated_subset[OF hY_grp h\<iota>_sub_loc] by (by100 blast)
                have hSG_grp: "top1_is_group_on ?SG
                    (top1_fundamental_group_mul Y TY y0)
                    (top1_fundamental_group_id Y TY y0)
                    (top1_fundamental_group_invg Y TY y0)"
                  by (rule intersection_of_subgroups_is_group[OF hY_grp h\<iota>_sub_loc])
                have "?incl_F0 ` (\<iota>F0 ` F0) \<subseteq> ?SG"
                proof
                  fix x assume "x \<in> ?incl_F0 ` (\<iota>F0 ` F0)"
                  hence "x \<in> \<iota> ` S" using hincl_gens by (by100 blast)
                  thus "x \<in> ?SG" using subgroup_generated_contains[OF hY_grp h\<iota>_sub_loc]
                    by (by100 blast)
                qed
                from hom_image_in_subgroup_from_generators[OF hF0_grp hY_grp
                    hincl_hom hF0_gen h\<iota>F0_sub hSG_grp hSG_sub this]
                have himage_sub: "?incl_F0 ` (top1_fundamental_group_carrier ?YF0 ?TYF0 y0) \<subseteq> ?SG" .
                have "c \<in> ?incl_F0 ` (top1_fundamental_group_carrier ?YF0 ?TYF0 y0)"
                  using hincl_c hc_F0_carrier by (by100 blast)
                thus "c \<in> ?SG" using himage_sub by (by100 blast)
              qed
            qed
          next
            fix c assume "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)"
            show "c \<in> top1_fundamental_group_carrier Y TY y0"
            proof -
              have "top1_is_group_on (top1_fundamental_group_carrier Y TY y0)
                  (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0)
                  (top1_fundamental_group_invg Y TY y0)"
                by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
              have h\<iota>_sub: "\<iota> ` S \<subseteq> top1_fundamental_group_carrier Y TY y0"
              proof
                fix x assume "x \<in> \<iota> ` S"
                then obtain s where "s \<in> S" "x = \<iota> s" by (by100 blast)
                from bij_betw_imp_surj_on[OF hidx] \<open>s \<in> S\<close>
                obtain A where "A \<in> ?NT" "idx A = s" by (by100 blast)
                have "the_inv_into ?NT idx s = A"
                  using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>A \<in> ?NT\<close>]
                    \<open>idx A = s\<close> by (by100 simp)
                hence "\<iota> s = gen A" unfolding \<iota>_def by (by100 simp)
                thus "x \<in> top1_fundamental_group_carrier Y TY y0"
                  using \<open>x = \<iota> s\<close> hgen[rule_format, OF \<open>A \<in> ?NT\<close>] by (by100 simp)
              qed
              from subgroup_generated_subset[OF \<open>top1_is_group_on _ _ _ _\<close> h\<iota>_sub]
              have "top1_subgroup_generated_on (top1_fundamental_group_carrier Y TY y0)
                  (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                  (top1_fundamental_group_invg Y TY y0) (\<iota> ` S)
                  \<subseteq> top1_fundamental_group_carrier Y TY y0" .
              thus ?thesis using \<open>c \<in> _\<close> by (by100 blast)
            qed
          qed
          \<comment> \<open>5. No non-trivial reduced word = identity.\<close>
          show "\<forall>ws. ws \<noteq> [] \<longrightarrow>
              top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
              (\<forall>i<length ws. fst (ws ! i) \<in> S) \<longrightarrow>
              top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                  (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id Y TY y0"
          proof (intro allI impI)
            fix ws :: "(nat \<times> bool) list"
            assume hws_ne: "ws \<noteq> []"
              and hws_red: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
              and hws_in: "\<forall>i<length ws. fst (ws ! i) \<in> S"
            \<comment> \<open>Step 1: Extract the arcs F = {inv\\_into(idx, s) | s in ws}.\<close>
            let ?arcs = "(\<lambda>s. the_inv_into ?NT idx s) ` (fst ` set ws)"
            have hF_fin: "finite ?arcs" by (by100 simp)
            have hF_NT: "?arcs \<subseteq> ?NT"
            proof
              fix A assume "A \<in> ?arcs"
              then obtain s where "s \<in> fst ` set ws" "A = the_inv_into ?NT idx s"
                by (by100 blast)
              then obtain i where "i < length ws" "fst (ws ! i) = s"
              proof -
                from \<open>s \<in> fst ` set ws\<close> obtain sb where "sb \<in> set ws" "fst sb = s"
                  by (by100 blast)
                from \<open>sb \<in> set ws\<close> have "\<exists>i. i < length ws \<and> ws ! i = sb"
                  using in_set_conv_nth by (by5000 metis)
                then obtain i where "i < length ws" "ws ! i = sb" by (by100 blast)
                hence "fst (ws ! i) = s" using \<open>fst sb = s\<close> by (by100 simp)
                thus ?thesis using \<open>i < length ws\<close> that by (by100 blast)
              qed
              hence "s \<in> S" using hws_in by (by100 blast)
              from bij_betw_imp_surj_on[OF hidx] this
              obtain B where "B \<in> ?NT" "idx B = s" by (by100 blast)
              have "the_inv_into ?NT idx s = B"
                using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF hidx] \<open>B \<in> ?NT\<close>]
                  \<open>idx B = s\<close> by (by100 simp)
              thus "A \<in> ?NT" using \<open>A = the_inv_into ?NT idx s\<close> \<open>B \<in> ?NT\<close> by (by100 simp)
            qed
            have hF_ne: "?arcs \<noteq> {}" using hws_ne by (by100 simp)
            let ?YF = "T \<union> \<Union>?arcs" and ?TYF = "subspace_topology Y TY (T \<union> \<Union>?arcs)"
            \<comment> \<open>Step 2: By harc\\_loops\\_free: \\<pi>\\_1(?YF) free on ?arcs with \\<iota>F.\<close>
            from harc_loops_free[OF hF_fin hF_NT hF_ne]
            obtain \<iota>F where hfreeF: "top1_is_free_group_full_on
                (top1_fundamental_group_carrier ?YF ?TYF y0) (top1_fundamental_group_mul ?YF ?TYF y0)
                (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                \<iota>F ?arcs"
                and hgenF: "\<forall>A\<in>?arcs. top1_fundamental_group_induced_on ?YF ?TYF y0 Y TY y0 (\<lambda>x. x)
                    (\<iota>F A) = gen A"
              by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
            let ?incl = "top1_fundamental_group_induced_on ?YF ?TYF y0 Y TY y0 (\<lambda>x. x)"
            \<comment> \<open>Step 3: The word product in \\<pi>\\_1(Y) equals incl*(word product in \\<pi>\\_1(?YF)).
               This uses: \\<iota>(s) = gen(inv(idx,s)) = incl*(\\<iota>F(inv(idx,s))).
               So map((s,b) \\<mapsto> (\\<iota>(s),b), ws) = map((s,b) \\<mapsto> (incl*(\\<iota>F(inv(idx,s))),b), ws).
               By hom\\_word\\_product: word\\_product(Y, ...) = incl*(word\\_product(?YF, ...)).\<close>
            \<comment> \<open>Step 4-7: The inner word is non-trivial by freeness.
               By hincl\\_inj: incl* injective. So outer \\<noteq> id.\<close>
            \<comment> \<open>Step 3: Relate \\<iota>(s) to incl*(\\<iota>F(inv(idx,s))).\<close>
            have h\<iota>_eq_incl: "\<forall>i<length ws. \<iota> (fst (ws ! i)) =
                ?incl (\<iota>F (the_inv_into ?NT idx (fst (ws ! i))))"
            proof (intro allI impI)
              fix i assume "i < length ws"
              let ?s = "fst (ws ! i)" and ?A = "the_inv_into ?NT idx (fst (ws ! i))"
              \<comment> \<open>\\<iota>(s) = gen(inv(idx,s)) by \\<iota>\\_def.\<close>
              have "\<iota> ?s = gen ?A" unfolding \<iota>_def by (by100 simp)
              \<comment> \<open>gen(A) = incl*(\\<iota>F(A)) by hgenF (reversed).\<close>
              moreover have "?A \<in> ?arcs"
              proof -
                have "?s \<in> fst ` set ws" using \<open>i < length ws\<close> by (by100 force)
                thus ?thesis by (by100 blast)
              qed
              hence "?incl (\<iota>F ?A) = gen ?A" using hgenF by (by100 blast)
              ultimately show "\<iota> ?s = ?incl (\<iota>F ?A)" by (by100 simp)
            qed
            \<comment> \<open>Step 4: word\\_product(Y, ws) = incl*(word\\_product(?YF, ws\\_F)) by hom\\_word\\_product.\<close>
            let ?ws_F = "map (\<lambda>(s, b). (\<iota>F (the_inv_into ?NT idx s), b)) ws"
            \<comment> \<open>Key map equality: map((s,b) \\<mapsto> (\\<iota>(s),b), ws) = map((x,b) \\<mapsto> (incl*(x),b), ?ws\\_F).\<close>
            have hmap_incl_eq: "map (\<lambda>(s, b). (\<iota> s, b)) ws =
                map (\<lambda>(x, b). (?incl x, b)) ?ws_F"
            proof -
              \<comment> \<open>map((x,b) \\<mapsto> (incl*(x),b), ?ws\\_F) = map((s,b) \\<mapsto> (incl*(\\<iota>F(inv(s))),b), ws) by map\\_map.\<close>
              have "map (\<lambda>(x, b). (?incl x, b)) ?ws_F =
                  map (\<lambda>(s, b). (?incl (\<iota>F (the_inv_into ?NT idx s)), b)) ws"
                by (induction ws) (by100 auto)+
              \<comment> \<open>= map((s,b) \\<mapsto> (\\<iota>(s),b), ws) by h\\<iota>\\_eq\\_incl applied elementwise.\<close>
              also have "\<dots> = map (\<lambda>(s, b). (\<iota> s, b)) ws"
              proof (rule nth_equalityI)
                show "length (map (\<lambda>(s, b). (?incl (\<iota>F (the_inv_into ?NT idx s)), b)) ws) =
                    length (map (\<lambda>(s, b). (\<iota> s, b)) ws)" by (by100 simp)
              next
                fix i assume "i < length (map (\<lambda>(s, b). (?incl (\<iota>F (the_inv_into ?NT idx s)), b)) ws)"
                hence hi: "i < length ws" by (by100 simp)
                from h\<iota>_eq_incl[rule_format, OF hi]
                show "map (\<lambda>(s, b). (?incl (\<iota>F (the_inv_into ?NT idx s)), b)) ws ! i =
                    map (\<lambda>(s, b). (\<iota> s, b)) ws ! i"
                  by (cases "ws ! i") (use hi in \<open>by100 simp\<close>)
              qed
              finally show ?thesis by (by100 simp)
            qed
            \<comment> \<open>By hom\\_word\\_product: incl*(word\\_product(?YF, ?ws\\_F)) = word\\_product(Y, map(incl, ?ws\\_F)).\<close>
            have hword_eq: "top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                (map (\<lambda>(s, b). (\<iota> s, b)) ws) =
                ?incl (top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                    (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                    ?ws_F)"
            proof -
              \<comment> \<open>Rewrite LHS using hmap\\_incl\\_eq.\<close>
              from arg_cong[OF hmap_incl_eq, of "top1_group_word_product
                  (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)"]
              have "top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                  (map (\<lambda>(s, b). (\<iota> s, b)) ws) =
                  top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                  (map (\<lambda>(x, b). (?incl x, b)) ?ws_F)" by (by100 simp)
              \<comment> \<open>By hom\\_word\\_product (reversed): = incl*(word\\_product(?YF, ?ws\\_F)).\<close>
              also have "\<dots> = ?incl (top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  ?ws_F)"
              proof -
                have hYF_sub': "?YF \<subseteq> Y" using hT_sub h\<A> hF_NT by (by100 blast)
                have hTYF_top: "is_topology_on ?YF ?TYF"
                  by (rule subspace_topology_is_topology_on[OF hTY_top hYF_sub'])
                have hF_grp: "top1_is_group_on (top1_fundamental_group_carrier ?YF ?TYF y0)
                    (top1_fundamental_group_mul ?YF ?TYF y0) (top1_fundamental_group_id ?YF ?TYF y0)
                    (top1_fundamental_group_invg ?YF ?TYF y0)"
                  using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
                have hY_grp: "top1_is_group_on (top1_fundamental_group_carrier Y TY y0)
                    (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                    (top1_fundamental_group_invg Y TY y0)"
                  by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
                have hincl_hom': "top1_group_hom_on
                    (top1_fundamental_group_carrier ?YF ?TYF y0)
                    (top1_fundamental_group_mul ?YF ?TYF y0)
                    (top1_fundamental_group_carrier Y TY y0)
                    (top1_fundamental_group_mul Y TY y0) ?incl"
                  using subspace_inclusion_induced_hom[OF hTY_top hYF_sub'] hT_x0
                  by (by100 blast)
                have hgens_in: "\<forall>i<length ?ws_F. fst (?ws_F ! i) \<in>
                    top1_fundamental_group_carrier ?YF ?TYF y0"
                proof (intro allI impI)
                  fix i assume "i < length ?ws_F"
                  hence "i < length ws" by (by100 simp)
                  have "fst (?ws_F ! i) = \<iota>F (the_inv_into ?NT idx (fst (ws ! i)))"
                    by (cases "ws ! i") (use \<open>i < length ws\<close> in \<open>by100 simp\<close>)
                  moreover have "\<iota>F (the_inv_into ?NT idx (fst (ws ! i))) \<in>
                      top1_fundamental_group_carrier ?YF ?TYF y0"
                  proof -
                    have "fst (ws ! i) \<in> fst ` set ws" using \<open>i < length ws\<close> by (by100 force)
                    hence "the_inv_into ?NT idx (fst (ws ! i)) \<in> ?arcs" by (by100 blast)
                    from hfreeF[unfolded top1_is_free_group_full_on_def]
                    have "\<forall>s\<in>?arcs. \<iota>F s \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                      by (by5000 blast)
                    thus ?thesis using \<open>the_inv_into ?NT idx _ \<in> ?arcs\<close> by (by100 blast)
                  qed
                  ultimately show "fst (?ws_F ! i) \<in>
                      top1_fundamental_group_carrier ?YF ?TYF y0" by (by100 simp)
                qed
                from hom_word_product[OF hF_grp hY_grp hincl_hom' hgens_in]
                show ?thesis by (by100 simp)
              qed
              finally show ?thesis .
            qed
            \<comment> \<open>Step 5: ?ws\\_F is a non-trivial reduced word in \\<pi>\\_1(?YF).\<close>
            have hws_F_red: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>F (the_inv_into ?NT idx s), b)) ws)"
            proof -
              \<comment> \<open>Use reduced\\_word\\_transfer with h = \\<iota>, g = \\<iota>F \\<circ> inv(idx).
                 Need: \\<iota>(s) = \\<iota>(t) \\<Longrightarrow> (\\<iota>F\\<circ>inv(idx))(s) = (\\<iota>F\\<circ>inv(idx))(t) for s,t \\<in> fst`set ws.\<close>
              have hS_sub: "\<forall>i<length ws. fst (ws ! i) \<in> S"
                using hws_in by (by100 blast)
              show ?thesis
              proof (rule reduced_word_transfer[where S="fst ` set ws"
                  and h="\<iota>" and g="\<lambda>s. \<iota>F (the_inv_into ?NT idx s)"
                  and ws=ws])
                \<comment> \<open>Condition: g(s) = g(t) \\<Longrightarrow> h(s) = h(t).\<close>
                fix s t assume "s \<in> fst ` set ws" "t \<in> fst ` set ws"
                  and heq: "\<iota>F (the_inv_into ?NT idx s) = \<iota>F (the_inv_into ?NT idx t)"
                \<comment> \<open>\\<iota>(s) = incl*(\\<iota>F(inv(idx,s))) from h\\<iota>\\_eq\\_incl.\<close>
                show "\<iota> s = \<iota> t"
                proof -
                  from \<open>s \<in> fst ` set ws\<close> obtain sb_s where "sb_s \<in> set ws" "fst sb_s = s"
                    by (by100 blast)
                  from \<open>sb_s \<in> set ws\<close> obtain i where "i < length ws" "ws ! i = sb_s"
                    by (rule in_set_conv_nth[THEN iffD1, elim_format]) (by100 blast)
                  hence "fst (ws ! i) = s" using \<open>fst sb_s = s\<close> by (by100 simp)
                  from \<open>t \<in> fst ` set ws\<close> obtain sb_t where "sb_t \<in> set ws" "fst sb_t = t"
                    by (by100 blast)
                  from \<open>sb_t \<in> set ws\<close> obtain j where "j < length ws" "ws ! j = sb_t"
                    by (rule in_set_conv_nth[THEN iffD1, elim_format]) (by100 blast)
                  hence "fst (ws ! j) = t" using \<open>fst sb_t = t\<close> by (by100 simp)
                  from h\<iota>_eq_incl[rule_format, OF \<open>i < length ws\<close>]
                  have "\<iota> s = ?incl (\<iota>F (the_inv_into ?NT idx s))"
                    using \<open>fst (ws ! i) = s\<close> by (by100 simp)
                  from h\<iota>_eq_incl[rule_format, OF \<open>j < length ws\<close>]
                  have "\<iota> t = ?incl (\<iota>F (the_inv_into ?NT idx t))"
                    using \<open>fst (ws ! j) = t\<close> by (by100 simp)
                  from heq have "?incl (\<iota>F (the_inv_into ?NT idx s)) =
                      ?incl (\<iota>F (the_inv_into ?NT idx t))" by (by100 simp)
                  thus "\<iota> s = \<iota> t"
                    using \<open>\<iota> s = ?incl _\<close> \<open>\<iota> t = ?incl _\<close> by (by100 simp)
                qed
              next
                show "\<forall>i<length ws. fst (ws ! i) \<in> fst ` set ws"
                  by (by100 force)
              next
                show "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
                  by (rule hws_red)
              qed
            qed
            have hws_F_ne: "?ws_F \<noteq> []" using hws_ne by (by100 simp)
            \<comment> \<open>The generators in the word map to ?arcs.\<close>
            have hws_inv_in: "\<forall>i<length ws. the_inv_into ?NT idx (fst (ws ! i)) \<in> ?arcs"
            proof (intro allI impI)
              fix i assume "i < length ws"
              have "fst (ws ! i) \<in> fst ` set ws"
                using \<open>i < length ws\<close> by (by100 force)
              thus "the_inv_into ?NT idx (fst (ws ! i)) \<in> ?arcs" by (by100 blast)
            qed
            \<comment> \<open>Step 6: By freeness of \\<pi>\\_1(?YF): word\\_product(?YF, ?ws\\_F) \\<noteq> id.\<close>
            have hword_F_ne: "top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                ?ws_F \<noteq> top1_fundamental_group_id ?YF ?TYF y0"
            proof -
              \<comment> \<open>ws\\_arcs: the word re-indexed by ?arcs.\<close>
              let ?ws_arcs = "map (\<lambda>(s, b). (the_inv_into ?NT idx s, b)) ws"
              \<comment> \<open>map(\\<iota>F, ws\\_arcs) = ?ws\\_F by map fusion (induction on ws).\<close>
              have hmap_eq: "map (\<lambda>(s, b). (\<iota>F s, b)) ?ws_arcs = ?ws_F"
                by (induction ws) (by100 auto)+
              \<comment> \<open>ws\\_arcs is non-empty and indexed by ?arcs.\<close>
              have "?ws_arcs \<noteq> []" using hws_ne by (by100 simp)
              have hws_arcs_in: "\<forall>i<length ?ws_arcs. fst (?ws_arcs ! i) \<in> ?arcs"
              proof (intro allI impI)
                fix i assume "i < length ?ws_arcs"
                hence "i < length ws" by (by100 simp)
                have "fst (?ws_arcs ! i) = the_inv_into ?NT idx (fst (ws ! i))"
                  by (cases "ws ! i") (use \<open>i < length ws\<close> in \<open>by100 simp\<close>)
                moreover have "fst (ws ! i) \<in> fst ` set ws" using \<open>i < length ws\<close> by (by100 force)
                ultimately show "fst (?ws_arcs ! i) \<in> ?arcs" by (by100 blast)
              qed
              \<comment> \<open>reduced(map(\\<iota>F, ws\\_arcs)) from hws\\_F\\_red + hmap\\_eq.\<close>
              have hred_arcs: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>F s, b)) ?ws_arcs)"
              proof -
                from arg_cong[OF hmap_eq, of top1_is_reduced_word]
                have "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>F s, b)) ?ws_arcs) =
                    top1_is_reduced_word ?ws_F" .
                thus ?thesis using hws_F_red by (by100 simp)
              qed
              \<comment> \<open>Extract freeness condition and apply to ws\\_arcs.\<close>
              from hfreeF[unfolded top1_is_free_group_full_on_def]
              have "\<forall>ws'. ws' \<noteq> [] \<longrightarrow>
                  top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>F s, b)) ws') \<longrightarrow>
                  (\<forall>i<length ws'. fst (ws' ! i) \<in> ?arcs) \<longrightarrow>
                  top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                      (top1_fundamental_group_id ?YF ?TYF y0)
                      (top1_fundamental_group_invg ?YF ?TYF y0)
                      (map (\<lambda>(s, b). (\<iota>F s, b)) ws') \<noteq>
                  top1_fundamental_group_id ?YF ?TYF y0"
                by (by5000 blast)
              note hfree_cond = this
              have hne_arcs: "top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  (map (\<lambda>(s, b). (\<iota>F s, b)) ?ws_arcs) \<noteq>
                  top1_fundamental_group_id ?YF ?TYF y0"
                using hfree_cond \<open>?ws_arcs \<noteq> []\<close> hred_arcs hws_arcs_in
                by (by5000 blast)
              \<comment> \<open>Transfer via arg\\_cong: word\\_product(map(\\<iota>F, ws\\_arcs)) = word\\_product(?ws\\_F).\<close>
              moreover from arg_cong[OF hmap_eq, of "top1_group_word_product
                  (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0)
                  (top1_fundamental_group_invg ?YF ?TYF y0)"]
              have "top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  (map (\<lambda>(s, b). (\<iota>F s, b)) ?ws_arcs) =
                  top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  ?ws_F" .
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>Step 7: By hincl\\_inj: incl* injective. So incl*(word\\_product) \\<noteq> id\\_Y.\<close>
            show "top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id Y TY y0"
            proof (rule notI)
              assume hcontra: "top1_group_word_product (top1_fundamental_group_mul Y TY y0)
                  (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)
                  (map (\<lambda>(s, b). (\<iota> s, b)) ws) = top1_fundamental_group_id Y TY y0"
              \<comment> \<open>By hword\\_eq: incl*(word\\_product(?YF, ws\\_F)) = id\\_Y.\<close>
              have "?incl (top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  ?ws_F) = top1_fundamental_group_id Y TY y0"
                using hword_eq hcontra by (by100 simp)
              \<comment> \<open>word\\_product(?YF, ws\\_F) \\<in> carrier(?YF).\<close>
              have hYF_sub': "?YF \<subseteq> Y" using hT_sub h\<A> hF_NT by (by100 blast)
              have hTYF_top: "is_topology_on ?YF ?TYF"
                by (rule subspace_topology_is_topology_on[OF hTY_top hYF_sub'])
              have hF_grp: "top1_is_group_on (top1_fundamental_group_carrier ?YF ?TYF y0)
                  (top1_fundamental_group_mul ?YF ?TYF y0) (top1_fundamental_group_id ?YF ?TYF y0)
                  (top1_fundamental_group_invg ?YF ?TYF y0)"
                using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
              have hword_F_carrier: "top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0)
                  ?ws_F \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
              proof (rule word_product_in_group[OF hF_grp])
                show "\<forall>i<length ?ws_F. fst (?ws_F ! i) \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                proof (intro allI impI)
                  fix i assume "i < length ?ws_F"
                  hence "i < length ws" by (by100 simp)
                  have "fst (?ws_F ! i) = \<iota>F (the_inv_into ?NT idx (fst (ws ! i)))"
                  proof -
                    have "?ws_F ! i = (case ws ! i of (s, b) \<Rightarrow>
                        (\<iota>F (the_inv_into ?NT idx s), b))"
                      using \<open>i < length ws\<close> by (by100 simp)
                    thus ?thesis by (cases "ws ! i") (by100 simp)
                  qed
                  moreover have "\<iota>F (the_inv_into ?NT idx (fst (ws ! i)))
                      \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                  proof -
                    have "the_inv_into ?NT idx (fst (ws ! i)) \<in> ?arcs"
                      using hws_inv_in \<open>i < length ws\<close> by (by100 blast)
                    from hfreeF[unfolded top1_is_free_group_full_on_def]
                    have "\<forall>s\<in>?arcs. \<iota>F s \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                      by (by5000 blast)
                    thus ?thesis using \<open>the_inv_into ?NT idx _ \<in> ?arcs\<close> by (by100 blast)
                  qed
                  ultimately show "fst (?ws_F ! i) \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                    by (by100 simp)
                qed
              qed
              have hid_F_carrier: "top1_fundamental_group_id ?YF ?TYF y0
                  \<in> top1_fundamental_group_carrier ?YF ?TYF y0"
                using hF_grp unfolding top1_is_group_on_def by (by100 blast)
              have hincl_hom: "top1_group_hom_on
                  (top1_fundamental_group_carrier ?YF ?TYF y0)
                  (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_carrier Y TY y0)
                  (top1_fundamental_group_mul Y TY y0) ?incl"
                using subspace_inclusion_induced_hom[OF hTY_top hYF_sub'] hT_x0 by (by100 blast)
              have hY_grp: "top1_is_group_on (top1_fundamental_group_carrier Y TY y0)
                  (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
                  (top1_fundamental_group_invg Y TY y0)"
                by (rule top1_fundamental_group_is_group[OF hTY_top assms(3)])
              have hincl_id: "?incl (top1_fundamental_group_id ?YF ?TYF y0) =
                  top1_fundamental_group_id Y TY y0"
                by (rule hom_preserves_id[OF hF_grp hY_grp hincl_hom])
              \<comment> \<open>By hincl\\_inj: incl* injective on carrier(?YF).\<close>
              have hYF_sub: "?YF \<subseteq> Y" using hT_sub h\<A> hF_NT by (by100 blast)
              from hincl_inj[OF hF_fin hF_NT hF_ne]
              have hinj: "inj_on ?incl (top1_fundamental_group_carrier ?YF ?TYF y0)" .
              \<comment> \<open>incl*(word\\_product) = incl*(id\\_F). By injectivity: word\\_product = id\\_F.\<close>
              let ?wp_F = "top1_group_word_product (top1_fundamental_group_mul ?YF ?TYF y0)
                  (top1_fundamental_group_id ?YF ?TYF y0) (top1_fundamental_group_invg ?YF ?TYF y0) ?ws_F"
              have "?incl ?wp_F = ?incl (top1_fundamental_group_id ?YF ?TYF y0)"
                using \<open>?incl ?wp_F = _\<close> hincl_id by (by100 simp)
              have "?wp_F = top1_fundamental_group_id ?YF ?TYF y0"
                using hinj hword_F_carrier hid_F_carrier \<open>?incl ?wp_F = ?incl _\<close>
                unfolding inj_on_def by (by5000 blast)
              thus False using hword_F_ne by contradiction
            qed
          qed
        qed
        thus ?thesis by (by100 blast)
      qed
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
  shows "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set).
           top1_is_free_group_full_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<iota> S"
  by (rule graph_pi1_free_weak[OF assms])

\<comment> \<open>The full SvK proof of Theorem 84.7 with int-set packaging was previously
   here (~1700 lines). It has been replaced by a direct application of
   graph\\_pi1\\_free\\_weak, which proves the same result without requiring
   the int-set group construction. The original proof is preserved in backups.\<close>

\<comment> \<open>Original proof structure (preserved for reference):
   Step 1: Extract arcs, maximal tree, non-tree arcs NT.
   Step 2: Case split: tree (trivial π₁) vs non-tree.
   Step 3: Finite case: SvK induction on card(NT).
     Base case (card=1): Lemma 84.6 + base-point change.
     Induction step: SvK with U = X-p₂-...-pₙ, V = X-p₁.
     DR: U to T∪A₁, V to T∪A₂∪...∪Aₙ.
     SC: U∩V DR to T (simply connected).
     svk\\_free\\_product\\_free combines π₁(U), π₁(V).
   Step 4: Infinite case: graph\\_pi1\\_free\\_weak directly.
   The full proof used ~1700 lines of SvK infrastructure.\<close>



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
  shows "\<exists>(\<iota>H::nat \<Rightarrow> 'g) (SH::nat set).
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
  \<comment> \<open>Step 2: Covering existence (Theorem 82.1) + H-correspondence.
     The covering E' is constructed so that p'*(\\<pi>\\_1(E', e0')) corresponds to H.\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a" and e0' :: 'b
      and f_iso :: "'g \<Rightarrow> _"
    where "top1_covering_map_on E' TE' X TX p'" "top1_connected_on E' TE'"
      and "e0' \<in> E'" and hE'_strict: "is_topology_on_strict E' TE'"
      and "p' e0' = x0"
      and hH_corr: "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'
          ` top1_fundamental_group_carrier E' TE' e0' = f_iso ` H"
      and hf_iso: "top1_group_iso_on G mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f_iso"
    sorry \<comment> \<open>Covering existence (Theorem 82.1): for the subgroup f\\_iso(H) \\<le> \\<pi>\\_1(X),
       construct covering E' with p'*(\\<pi>\\_1(E')) = f\\_iso(H).
       f\\_iso comes from the isomorphism G \\<cong> \\<pi>\\_1(X).\<close>
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
  \<comment> \<open>Step 3c: H is free.
     Chain: p'* injective \\<Rightarrow> \\<pi>\\_1(E') \\<cong> p'*(\\<pi>\\_1(E')) = f\\_iso(H) \\<cong> H.
     \\<pi>\\_1(E') is free \\<Rightarrow> H is free (freeness transfers across iso).\<close>
  show ?thesis
  proof -
    \<comment> \<open>p'* is injective (covering maps induce injections on \\<pi>\\_1).\<close>
    have hX_strict: "is_topology_on_strict X TX"
      using \<open>top1_is_graph_on X TX\<close> unfolding top1_is_graph_on_def by (by100 blast)
    have hp_inj: "inj_on (top1_fundamental_group_induced_on E' TE' e0' X TX x0 p')
        (top1_fundamental_group_carrier E' TE' e0')"
      by (rule covering_induced_injective[OF \<open>top1_covering_map_on E' TE' X TX p'\<close>
          hE'_strict hX_strict \<open>e0' \<in> E'\<close> \<open>p' e0' = x0\<close>])
    \<comment> \<open>p'*(\\<pi>\\_1(E')) = f\\_iso(H). And f\\_iso: G \\<rightarrow> \\<pi>\\_1(X) is iso, so f\\_iso(H) \\<cong> H.\<close>
    \<comment> \<open>p'* injective: \\<pi>\\_1(E') \\<cong> p'*(\\<pi>\\_1(E')) = f\\_iso(H) \\<cong> H.\<close>
    \<comment> \<open>\\<pi>\\_1(E') is free (hfree\\_E). Transfer across iso: H is free.\<close>
    \<comment> \<open>p'* restricted to \\<pi>\\_1(E') is a bijection onto its image f\\_iso(H).\<close>
    let ?p_star = "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'"
    have hp_bij: "bij_betw ?p_star (top1_fundamental_group_carrier E' TE' e0') (f_iso ` H)"
      unfolding bij_betw_def using hp_inj hH_corr by (by100 blast)
    \<comment> \<open>f\\_iso restricted to H is a bijection onto f\\_iso(H).\<close>
    have hf_bij_H: "bij_betw f_iso H (f_iso ` H)"
    proof -
      from hf_iso have "bij_betw f_iso G (top1_fundamental_group_carrier X TX x0)"
        unfolding top1_group_iso_on_def by (by100 blast)
      hence "inj_on f_iso G" unfolding bij_betw_def by (by100 blast)
      from inj_on_subset[OF this assms(3)]
      have "inj_on f_iso H" .
      thus ?thesis unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>Compose: \\<pi>\\_1(E') \\<rightarrow> f\\_iso(H) \\<rightarrow> H. Both bijections.\<close>
    \<comment> \<open>The composed map (f\\_iso\\<inverse>) \\<circ> p'*: \\<pi>\\_1(E') \\<rightarrow> H is a group iso.\<close>
    have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0')
        H mul"
    proof -
      \<comment> \<open>The composed map (f\\_iso\\<inverse>) \\<circ> p'*: \\<pi>\\_1(E') \\<rightarrow> H is a group iso.\<close>
      let ?p_star = "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'"
      let ?f_inv = "inv_into G f_iso"
      let ?\<phi> = "?f_inv \<circ> ?p_star"
      \<comment> \<open>\\<phi> is a group hom (composition of two homs).\<close>
      have hp_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0')
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0)
          ?p_star"
      proof -
        have hE_top: "is_topology_on E' TE'"
          using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hX_top: "is_topology_on X TX"
          using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hp_cont: "top1_continuous_map_on E' TE' X TX p'"
          using \<open>top1_covering_map_on E' TE' X TX p'\<close>
          unfolding top1_covering_map_on_def by (by100 blast)
        from top1_fundamental_group_induced_on_is_hom[OF hE_top hX_top \<open>e0' \<in> E'\<close>
            \<open>x0 \<in> X\<close> hp_cont \<open>p' e0' = x0\<close>]
        show ?thesis .
      qed
      have hf_inv_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
          G mul ?f_inv"
      proof -
        have hG_grp: "top1_is_group_on G mul e invg"
          using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
        have hX_top: "is_topology_on X TX"
          using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hpiX_grp: "top1_is_group_on (top1_fundamental_group_carrier X TX x0)
            (top1_fundamental_group_mul X TX x0)
            (top1_fundamental_group_id X TX x0)
            (top1_fundamental_group_invg X TX x0)"
          by (rule top1_fundamental_group_is_group[OF hX_top \<open>x0 \<in> X\<close>])
        note hf_inv_iso = group_iso_on_inverse[OF hf_iso hG_grp hpiX_grp]
        from hf_inv_iso[unfolded top1_group_iso_on_def, THEN conjunct1]
        show ?thesis .
      qed
      \<comment> \<open>\\<phi> maps \\<pi>\\_1(E') into H.\<close>
      have h\<phi>_maps: "\<forall>c \<in> top1_fundamental_group_carrier E' TE' e0'. ?\<phi> c \<in> H"
      proof (intro ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        hence "?p_star c \<in> f_iso ` H" using hH_corr by (by100 blast)
        then obtain h where "h \<in> H" "f_iso h = ?p_star c" by (by100 blast)
        have "h \<in> G" using \<open>h \<in> H\<close> assms(3) by (by100 blast)
        have "?f_inv (?p_star c) = ?f_inv (f_iso h)" using \<open>f_iso h = ?p_star c\<close> by (by100 simp)
        also have "\<dots> = h"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF
              hf_iso[unfolded top1_group_iso_on_def, THEN conjunct2]] \<open>h \<in> G\<close>]
          by (by100 simp)
        finally have "?\<phi> c = h" unfolding comp_def by (by100 simp)
        thus "?\<phi> c \<in> H" using \<open>h \<in> H\<close> by (by100 simp)
      qed
      \<comment> \<open>\\<phi> is bijective.\<close>
      have h\<phi>_bij: "bij_betw ?\<phi> (top1_fundamental_group_carrier E' TE' e0') H"
      proof -
        have hf_bij_H: "bij_betw f_iso H (f_iso ` H)"
        proof -
          from hf_iso have "inj_on f_iso G" unfolding top1_group_iso_on_def bij_betw_def
            by (by100 blast)
          from inj_on_subset[OF this assms(3)] show ?thesis
            unfolding bij_betw_def by (by100 blast)
        qed
        have hp_bij: "bij_betw ?p_star (top1_fundamental_group_carrier E' TE' e0') (f_iso ` H)"
          unfolding bij_betw_def using hp_inj hH_corr by (by100 blast)
        \<comment> \<open>\\<phi> is bijective: injective (both components injective) + surjective (image = H).\<close>
        show ?thesis unfolding bij_betw_def
        proof (intro conjI)
          show "inj_on ?\<phi> (top1_fundamental_group_carrier E' TE' e0')"
          proof (rule comp_inj_on)
            show "inj_on ?p_star (top1_fundamental_group_carrier E' TE' e0')"
              by (rule hp_inj)
            show "inj_on ?f_inv (?p_star ` top1_fundamental_group_carrier E' TE' e0')"
            proof -
              have "?p_star ` top1_fundamental_group_carrier E' TE' e0' = f_iso ` H"
                using hH_corr by (by100 blast)
              moreover have "inj_on ?f_inv (f_iso ` H)"
              proof (rule inj_onI)
                fix x y assume "x \<in> f_iso ` H" "y \<in> f_iso ` H"
                  and "?f_inv x = ?f_inv y"
                from \<open>x \<in> f_iso ` H\<close> obtain hx where "hx \<in> H" "x = f_iso hx" by (by100 blast)
                from \<open>y \<in> f_iso ` H\<close> obtain hy where "hy \<in> H" "y = f_iso hy" by (by100 blast)
                have "inj_on f_iso G" using hf_iso unfolding top1_group_iso_on_def bij_betw_def
                  by (by100 blast)
                have "?f_inv x = hx"
                  using inv_into_f_f[OF \<open>inj_on f_iso G\<close>] \<open>hx \<in> H\<close> assms(3) \<open>x = f_iso hx\<close>
                  by (by100 blast)
                have "?f_inv y = hy"
                  using inv_into_f_f[OF \<open>inj_on f_iso G\<close>] \<open>hy \<in> H\<close> assms(3) \<open>y = f_iso hy\<close>
                  by (by100 blast)
                from \<open>?f_inv x = ?f_inv y\<close> \<open>?f_inv x = hx\<close> \<open>?f_inv y = hy\<close>
                have "hx = hy" by (by100 simp)
                thus "x = y" using \<open>x = f_iso hx\<close> \<open>y = f_iso hy\<close> by (by100 simp)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
          qed
          show "?\<phi> ` top1_fundamental_group_carrier E' TE' e0' = H"
          proof (rule set_eqI, rule iffI)
            fix h assume "h \<in> ?\<phi> ` top1_fundamental_group_carrier E' TE' e0'"
            then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'" "h = ?\<phi> c"
              by (by100 blast)
            thus "h \<in> H" using h\<phi>_maps by (by100 blast)
          next
            fix h assume "h \<in> H"
            hence "h \<in> G" using assms(3) by (by100 blast)
            hence "f_iso h \<in> f_iso ` H" using \<open>h \<in> H\<close> by (by100 blast)
            hence "f_iso h \<in> ?p_star ` top1_fundamental_group_carrier E' TE' e0'"
              using hH_corr by (by100 blast)
            then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'"
                "?p_star c = f_iso h" by (by100 blast)
            have "inj_on f_iso G" using hf_iso unfolding top1_group_iso_on_def bij_betw_def
              by (by100 blast)
            have "?f_inv (f_iso h) = h"
              using inv_into_f_f[OF \<open>inj_on f_iso G\<close> \<open>h \<in> G\<close>] by (by100 simp)
            hence "?\<phi> c = h" using \<open>?p_star c = f_iso h\<close> unfolding comp_def by (by100 simp)
            thus "h \<in> ?\<phi> ` top1_fundamental_group_carrier E' TE' e0'"
              using \<open>c \<in> _\<close> by (by100 blast)
          qed
        qed
      qed
      \<comment> \<open>\\<phi> preserves mul.\<close>
      have h\<phi>_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>"
        unfolding top1_group_hom_on_def comp_def
      proof (intro conjI ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        show "?f_inv (?p_star c) \<in> H" using h\<phi>_maps \<open>c \<in> _\<close> unfolding comp_def
          by (by100 blast)
      next
        fix a b assume "a \<in> top1_fundamental_group_carrier E' TE' e0'"
            and "b \<in> top1_fundamental_group_carrier E' TE' e0'"
        \<comment> \<open>p* preserves mul: p*(mul\\_E(a,b)) = mul\\_X(p*a, p*b).\<close>
        have "?p_star (top1_fundamental_group_mul E' TE' e0' a b) =
            top1_fundamental_group_mul X TX x0 (?p_star a) (?p_star b)"
          using hp_hom \<open>a \<in> _\<close> \<open>b \<in> _\<close> unfolding top1_group_hom_on_def by (by100 blast)
        \<comment> \<open>f\\_inv preserves mul: f\\_inv(mul\\_X(x,y)) = mul(f\\_inv(x), f\\_inv(y)).\<close>
        moreover have "?f_inv (top1_fundamental_group_mul X TX x0 (?p_star a) (?p_star b)) =
            mul (?f_inv (?p_star a)) (?f_inv (?p_star b))"
        proof -
          have "?p_star a \<in> top1_fundamental_group_carrier X TX x0"
            using hp_hom \<open>a \<in> _\<close> unfolding top1_group_hom_on_def by (by100 blast)
          have "?p_star b \<in> top1_fundamental_group_carrier X TX x0"
            using hp_hom \<open>b \<in> _\<close> unfolding top1_group_hom_on_def by (by100 blast)
          from hf_inv_hom[unfolded top1_group_hom_on_def]
          show ?thesis using \<open>?p_star a \<in> _\<close> \<open>?p_star b \<in> _\<close> by (by100 blast)
        qed
        ultimately show "?f_inv (?p_star (top1_fundamental_group_mul E' TE' e0' a b)) =
            mul (?f_inv (?p_star a)) (?f_inv (?p_star b))" by (by100 simp)
      qed
      \<comment> \<open>Package as group\\_iso\\_on.\<close>
      have "top1_group_iso_on (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>"
        unfolding top1_group_iso_on_def using h\<phi>_hom h\<phi>_bij by (by100 blast)
      thus ?thesis unfolding top1_groups_isomorphic_on_def by (by100 blast)
    qed
    \<comment> \<open>Transfer freeness: \\<pi>\\_1(E') free \\<Rightarrow> H free.\<close>
    from free_group_iso_transfer[OF hfree_E this assms(2)]
    obtain \<iota>H' where hfreeH: "top1_is_free_group_full_on H mul e invg \<iota>H' S_E"
      by (by100 blast)
    show ?thesis
      apply (rule exI[of _ \<iota>H'])
      apply (rule exI[of _ S_E])
      apply (rule hfreeH)
      done
  qed
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
  shows "\<exists>(\<iota>H::nat \<Rightarrow> 'g) (SH::nat set).
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
      and f_iso85 :: "'g \<Rightarrow> _"
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
      and he0': "e0' \<in> E'"
      and hE'_strict: "is_topology_on_strict E' TE'"
      and "p' e0' = x0"
      and hH_corr85: "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'
          ` top1_fundamental_group_carrier E' TE' e0' = f_iso85 ` H"
      and hf_iso85: "top1_group_iso_on F mul
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) f_iso85"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + graph covering (83.4) + H-correspondence.
       Same infrastructure as \\<S>85.1.\<close>
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
  \<comment> \<open>Step 3b: H is free (same pattern as \\<S>85.1 step 3c).\<close>
  have hH_free: "\<exists>(\<iota>H::nat \<Rightarrow> 'g) (SH::nat set).
      top1_is_free_group_full_on H mul e invg \<iota>H SH"
  proof -
    \<comment> \<open>Same proof as \\<S>85.1 step 3c.\<close>
    have hX_strict85: "is_topology_on_strict X TX"
      using hX_graph unfolding top1_is_graph_on_def by (by100 blast)
    have hp85_inj: "inj_on (top1_fundamental_group_induced_on E' TE' e0' X TX x0 p')
        (top1_fundamental_group_carrier E' TE' e0')"
      by (rule covering_induced_injective[OF hE'_cov hE'_strict hX_strict85 he0' \<open>p' e0' = x0\<close>])
    let ?p_star85 = "top1_fundamental_group_induced_on E' TE' e0' X TX x0 p'"
    let ?f_inv85 = "inv_into F f_iso85"
    let ?\<phi>85 = "?f_inv85 \<circ> ?p_star85"
    have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier E' TE' e0')
        (top1_fundamental_group_mul E' TE' e0') H mul"
    proof -
      \<comment> \<open>Same proof as \\<S>85.1 iso composition.\<close>
      have hE_top85: "is_topology_on E' TE'"
        using hE'_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hX_top85: "is_topology_on X TX"
        using hX_strict85 unfolding is_topology_on_strict_def by (by100 blast)
      have hp85_cont: "top1_continuous_map_on E' TE' X TX p'"
        using hE'_cov unfolding top1_covering_map_on_def by (by100 blast)
      have hp85_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0) ?p_star85"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hE_top85 hX_top85
            he0' hx0 hp85_cont \<open>p' e0' = x0\<close>])
      have hG85_grp: "top1_is_group_on F mul e invg"
        using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
      have hpiX85_grp: "top1_is_group_on (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0) (top1_fundamental_group_id X TX x0)
          (top1_fundamental_group_invg X TX x0)"
        by (rule top1_fundamental_group_is_group[OF hX_top85 hx0])
      note hf85_inv_iso = group_iso_on_inverse[OF hf_iso85 hG85_grp hpiX85_grp]
      have hf85_inv_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
          F mul ?f_inv85"
        using hf85_inv_iso[unfolded top1_group_iso_on_def, THEN conjunct1] .
      \<comment> \<open>\\<phi>85 maps into H.\<close>
      have h\<phi>85_maps: "\<forall>c \<in> top1_fundamental_group_carrier E' TE' e0'. ?\<phi>85 c \<in> H"
      proof (intro ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        hence "?p_star85 c \<in> f_iso85 ` H" using hH_corr85 by (by100 blast)
        then obtain h where "h \<in> H" "f_iso85 h = ?p_star85 c" by (by100 blast)
        have "h \<in> F" using \<open>h \<in> H\<close> assms(3) by (by100 blast)
        have "?f_inv85 (?p_star85 c) = ?f_inv85 (f_iso85 h)" using \<open>f_iso85 h = ?p_star85 c\<close>
          by (by100 simp)
        also have "\<dots> = h"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF
              hf_iso85[unfolded top1_group_iso_on_def, THEN conjunct2]] \<open>h \<in> F\<close>]
          by (by100 simp)
        finally show "?\<phi>85 c \<in> H" using \<open>h \<in> H\<close> unfolding comp_def by (by100 simp)
      qed
      \<comment> \<open>\\<phi>85 is hom.\<close>
      have h\<phi>85_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>85"
        unfolding top1_group_hom_on_def comp_def
      proof (intro conjI ballI)
        fix c assume "c \<in> top1_fundamental_group_carrier E' TE' e0'"
        show "?f_inv85 (?p_star85 c) \<in> H" using h\<phi>85_maps \<open>c \<in> _\<close> unfolding comp_def
          by (by100 blast)
      next
        fix a b assume ha: "a \<in> top1_fundamental_group_carrier E' TE' e0'"
            and hb: "b \<in> top1_fundamental_group_carrier E' TE' e0'"
        have "?p_star85 (top1_fundamental_group_mul E' TE' e0' a b) =
            top1_fundamental_group_mul X TX x0 (?p_star85 a) (?p_star85 b)"
          using hp85_hom ha hb unfolding top1_group_hom_on_def by (by100 blast)
        moreover have "?f_inv85 (top1_fundamental_group_mul X TX x0 (?p_star85 a) (?p_star85 b)) =
            mul (?f_inv85 (?p_star85 a)) (?f_inv85 (?p_star85 b))"
        proof -
          have "?p_star85 a \<in> top1_fundamental_group_carrier X TX x0"
            using hp85_hom ha unfolding top1_group_hom_on_def by (by100 blast)
          have "?p_star85 b \<in> top1_fundamental_group_carrier X TX x0"
            using hp85_hom hb unfolding top1_group_hom_on_def by (by100 blast)
          from hf85_inv_hom[unfolded top1_group_hom_on_def]
          show ?thesis using \<open>?p_star85 a \<in> _\<close> \<open>?p_star85 b \<in> _\<close> by (by100 blast)
        qed
        ultimately show "?f_inv85 (?p_star85 (top1_fundamental_group_mul E' TE' e0' a b)) =
            mul (?f_inv85 (?p_star85 a)) (?f_inv85 (?p_star85 b))" by (by100 simp)
      qed
      \<comment> \<open>\\<phi>85 is bijective.\<close>
      have h\<phi>85_bij: "bij_betw ?\<phi>85 (top1_fundamental_group_carrier E' TE' e0') H"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on ?\<phi>85 (top1_fundamental_group_carrier E' TE' e0')"
        proof (rule comp_inj_on[OF hp85_inj])
          have "?p_star85 ` top1_fundamental_group_carrier E' TE' e0' = f_iso85 ` H"
            using hH_corr85 by (by100 blast)
          moreover have "inj_on ?f_inv85 (f_iso85 ` H)"
          proof (rule inj_onI)
            fix x y assume "x \<in> f_iso85 ` H" "y \<in> f_iso85 ` H" "?f_inv85 x = ?f_inv85 y"
            from \<open>x \<in> f_iso85 ` H\<close> obtain hx where "hx \<in> H" "x = f_iso85 hx" by (by100 blast)
            from \<open>y \<in> f_iso85 ` H\<close> obtain hy where "hy \<in> H" "y = f_iso85 hy" by (by100 blast)
            have "inj_on f_iso85 F" using hf_iso85 unfolding top1_group_iso_on_def bij_betw_def
              by (by100 blast)
            have "?f_inv85 x = hx"
              using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close>] \<open>hx \<in> H\<close> assms(3) \<open>x = f_iso85 hx\<close>
              by (by100 blast)
            have "?f_inv85 y = hy"
              using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close>] \<open>hy \<in> H\<close> assms(3) \<open>y = f_iso85 hy\<close>
              by (by100 blast)
            from \<open>?f_inv85 x = ?f_inv85 y\<close> \<open>?f_inv85 x = hx\<close> \<open>?f_inv85 y = hy\<close>
            have "hx = hy" by (by100 simp)
            thus "x = y" using \<open>x = f_iso85 hx\<close> \<open>y = f_iso85 hy\<close> by (by100 simp)
          qed
          ultimately show "inj_on ?f_inv85 (?p_star85 ` top1_fundamental_group_carrier E' TE' e0')"
            by (by100 simp)
        qed
        show "?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0' = H"
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> ?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0'"
          then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'" "h = ?\<phi>85 c"
            by (by100 blast)
          thus "h \<in> H" using h\<phi>85_maps by (by100 blast)
        next
          fix h assume "h \<in> H"
          hence "h \<in> F" using assms(3) by (by100 blast)
          hence "f_iso85 h \<in> f_iso85 ` H" using \<open>h \<in> H\<close> by (by100 blast)
          hence "f_iso85 h \<in> ?p_star85 ` top1_fundamental_group_carrier E' TE' e0'"
            using hH_corr85 by (by100 blast)
          then obtain c where "c \<in> top1_fundamental_group_carrier E' TE' e0'"
              "?p_star85 c = f_iso85 h" by (by100 blast)
          have "inj_on f_iso85 F" using hf_iso85 unfolding top1_group_iso_on_def bij_betw_def
            by (by100 blast)
          have "?f_inv85 (f_iso85 h) = h"
            using inv_into_f_f[OF \<open>inj_on f_iso85 F\<close> \<open>h \<in> F\<close>] by (by100 simp)
          hence "?\<phi>85 c = h" using \<open>?p_star85 c = f_iso85 h\<close> unfolding comp_def by (by100 simp)
          thus "h \<in> ?\<phi>85 ` top1_fundamental_group_carrier E' TE' e0'"
            using \<open>c \<in> _\<close> by (by100 blast)
        qed
      qed
      \<comment> \<open>Package as group\\_iso\\_on.\<close>
      have "top1_group_iso_on (top1_fundamental_group_carrier E' TE' e0')
          (top1_fundamental_group_mul E' TE' e0') H mul ?\<phi>85"
        unfolding top1_group_iso_on_def using h\<phi>85_hom h\<phi>85_bij by (by100 blast)
      thus ?thesis unfolding top1_groups_isomorphic_on_def by (by100 blast)
    qed
    from free_group_iso_transfer[OF hfree_E this assms(4)]
    show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 3c: rank = kn+1 (Euler characteristic argument).\<close>
  from hH_free obtain \<iota>H :: "nat \<Rightarrow> 'g" and SH :: "nat set"
    where "top1_is_free_group_full_on H mul e invg \<iota>H SH"
    by (by100 blast)
  have "card SH = k * n + 1"
    sorry \<comment> \<open>Euler char: X has 1 vertex + (n+1) edges, chi(X) = -n.
       E' has k sheets: chi(E') = k*chi(X) = -kn.
       rank(pi1(E')) = 1-chi(E') = kn+1.
       H iso pi1(E') \\<Rightarrow> same rank by free\\_group\\_rank\\_invariant\\_finite.\<close>
  show ?thesis
    using \<open>top1_is_free_group_full_on H mul e invg \<iota>H SH\<close> \<open>card SH = k * n + 1\<close>
    by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end

