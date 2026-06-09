theory AlgTop
  imports "AlgTopCached12.AlgTopCached12"
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



(** Theorem 71.3: fully proved and cached in ac9/AlgTopCached9.thy. **)




\<comment> \<open>free\_group\_hom\_subset\_injective + Theorem\_71\_3\_pi1\_free moved to AlgTopCached9.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful) is now Theorem\_71\_3 in AlgTopCached9.
   It states: \\<pi>\\_1(X, p) is free on J (the actual book statement).
   The old int-set packaging wrapper (Theorem\_71\_3\_wedge\_of\_circles\_general)
   was unused dead code and has been removed.\<close>





\<comment> \<open>§71 helpers + §74 moved to AlgTopCached8.\<close>

\<comment> \<open>Elementary scheme operations (Munkres \\<S>76).
   A scheme is a list of (edge\\_name, direction) pairs representing a polygonal identification.
   Elementary operations preserve the quotient homeomorphism type.\<close>

definition top1_inverse_edge :: "'a \<times> bool \<Rightarrow> 'a \<times> bool" where
  "top1_inverse_edge e = (fst e, \<not> snd e)"

inductive top1_elementary_scheme_operation :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  rotate: "top1_elementary_scheme_operation (u @ v) (v @ u)" |
  cancel: "top1_elementary_scheme_operation (u @ [a, top1_inverse_edge a] @ v) (u @ v)" |
  uncancel: "top1_elementary_scheme_operation (u @ v) (u @ [a, top1_inverse_edge a] @ v)" |
  invert: "top1_elementary_scheme_operation w (rev (map top1_inverse_edge w))" |
  \<comment> \<open>Relabel: replace all occurrences of label old by label new.
     Book \\<S>76 operation (iii): "replace all occurrences of any given label by some other
     label that does not appear elsewhere in the scheme."\<close>
  relabel: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (if l = old then new else l, b)) w)" |
  \<comment> \<open>Flip orientation: change sign of exponent of all occurrences of a given label.
     Book \\<S>76 operation (iii): "one can change the sign of the exponent of all occurrences
     of a given label a; this amounts to reversing the orientations of all edges labelled a."\<close>
  flip_label: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) w)" |
  \<comment> \<open>Cut-and-repaste: the combined effect of Munkres \\<S>76 Theorem 76.1 on a single polygon.
     Cut at position between u1 and u2, introducing new label c.
     Flip one piece. Paste along label a (which appears in both pieces).
     Net effect on scheme: [u1] a [u2] a [u3] \\<sim> [u1] a a [u2\\<inverse>] [u3].
     This brings two copies of label a (same orientation) together.
     Formally: rotate one piece around and paste, cancelling u2 into u2\\<inverse>.\<close>
  cut_paste: "top1_elementary_scheme_operation
      (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)
      (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)" |
  \<comment> \<open>Cut-paste variant 2 (Figure 77.2): rearrange with a new label.
     Transforms y0 a y1 a y2 into b y2 b (y1 y0\\<inverse>) where b is new.
     This is the book's Figure 77.2 operation from \\<S>77 Lemma 77.1 Step 2.\<close>
  cut_paste2: "top1_elementary_scheme_operation
      (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)
      ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))" |
  \<comment> \<open>Cut-paste for opposite-orientation labels (Figure 77.3).
     Net effect: move u1 from before a to after a\\<inverse>.
     u0 @ u1 @ [(a,T)] @ u2 @ [(a,F)] @ u3 \\<to> u0 @ [(a,T)] @ u2 @ [(a,F)] @ u1 @ u3.\<close>
  cut_paste_opp: "top1_elementary_scheme_operation
      (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)
      (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"

\<comment> \<open>The scheme equivalence is the reflexive-transitive closure of elementary operations.\<close>
definition top1_scheme_equiv :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  "top1_scheme_equiv = top1_elementary_scheme_operation\<^sup>*\<^sup>*"

section \<open>\<S>76 Cutting and Pasting\<close>

\<comment> \<open>Quotient uniqueness: two quotient maps on the same space with the same fibres
   give homeomorphic quotient spaces. Follows from Theorem 22.2 applied both ways.\<close>
lemma quotient_same_fibres_homeomorphic:
  fixes X :: "'a set" and TX :: "'a set set"
    and Y1 :: "'b set" and TY1 :: "'b set set"
    and Y2 :: "'c set" and TY2 :: "'c set set"
  assumes hp1: "top1_quotient_map_on X TX Y1 TY1 p1"
      and hp2: "top1_quotient_map_on X TX Y2 TY2 p2"
      and hfibres: "\<forall>x\<in>X. \<forall>y\<in>X. (p1 x = p1 y) \<longleftrightarrow> (p2 x = p2 y)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>p2 is constant on fibres of p1 (from hfibres).\<close>
  have hp2_range: "\<forall>x\<in>X. p2 x \<in> Y2"
    using hp2 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp2_const: "\<forall>x\<in>X. \<forall>y\<in>X. p1 x = p1 y \<longrightarrow> p2 x = p2 y"
    using hfibres by (by100 blast)
  \<comment> \<open>By Theorem 22.2: p2 factors through p1 as f: Y1 \\<to> Y2.\<close>
  from Theorem_22_2[OF hp1 hp2_range hp2_const]
  obtain f where hf_range: "\<forall>y\<in>Y1. f y \<in> Y2"
      and hf_comp: "\<forall>x\<in>X. f (p1 x) = p2 x"
      and hf_cont_iff: "top1_continuous_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_continuous_map_on X TX Y2 TY2 p2"
      and hf_quot_iff: "top1_quotient_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_quotient_map_on X TX Y2 TY2 p2"
    by (by100 blast)
  \<comment> \<open>Similarly p1 factors through p2 as g: Y2 \\<to> Y1.\<close>
  have hp1_range: "\<forall>x\<in>X. p1 x \<in> Y1"
    using hp1 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp1_const: "\<forall>x\<in>X. \<forall>y\<in>X. p2 x = p2 y \<longrightarrow> p1 x = p1 y"
    using hfibres by (by100 blast)
  from Theorem_22_2[OF hp2 hp1_range hp1_const]
  obtain g where hg_range: "\<forall>y\<in>Y2. g y \<in> Y1"
      and hg_comp: "\<forall>x\<in>X. g (p2 x) = p1 x"
      and hg_cont_iff: "top1_continuous_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_continuous_map_on X TX Y1 TY1 p1"
      and hg_quot_iff: "top1_quotient_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_quotient_map_on X TX Y1 TY1 p1"
    by (by100 blast)
  \<comment> \<open>f is a quotient map (since p2 is).\<close>
  have hf_quot: "top1_quotient_map_on Y1 TY1 Y2 TY2 f"
    using hf_quot_iff hp2 by simp
  \<comment> \<open>f is bijective: injective (from g \\<circ> f = id on Y1) and surjective (quotient maps are surjective).\<close>
  have hf_surj: "f ` Y1 = Y2"
  proof -
    have "p2 ` X = Y2" using hp2 unfolding top1_quotient_map_on_def by (by100 blast)
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    show ?thesis
    proof
      show "f ` Y1 \<subseteq> Y2" using hf_range by (by100 blast)
    next
      show "Y2 \<subseteq> f ` Y1"
      proof
        fix y2 assume "y2 \<in> Y2"
        hence "\<exists>x\<in>X. p2 x = y2" using \<open>p2 ` X = Y2\<close> by (by100 blast)
        then obtain x where "x \<in> X" "p2 x = y2" by (by100 blast)
        hence "f (p1 x) = y2" using hf_comp by simp
        moreover have "p1 x \<in> Y1" using hp1_range \<open>x \<in> X\<close> by (by100 blast)
        ultimately show "y2 \<in> f ` Y1" by (by100 blast)
      qed
    qed
  qed
  have hgf_id: "\<forall>y\<in>Y1. g (f y) = y"
  proof
    fix y1 assume "y1 \<in> Y1"
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    then obtain x where "x \<in> X" "p1 x = y1" using \<open>y1 \<in> Y1\<close> by (by100 blast)
    have "f y1 = f (p1 x)" using \<open>p1 x = y1\<close> by simp
    also have "\<dots> = p2 x" using hf_comp \<open>x \<in> X\<close> by simp
    finally have "f y1 = p2 x" .
    hence "g (f y1) = g (p2 x)" by simp
    also have "\<dots> = p1 x" using hg_comp \<open>x \<in> X\<close> by simp
    finally show "g (f y1) = y1" using \<open>p1 x = y1\<close> by simp
  qed
  have hf_inj: "inj_on f Y1"
  proof (rule inj_onI)
    fix y1 y1' assume "y1 \<in> Y1" "y1' \<in> Y1" "f y1 = f y1'"
    have "g (f y1) = y1" using hgf_id \<open>y1 \<in> Y1\<close> by simp
    have "g (f y1') = y1'" using hgf_id \<open>y1' \<in> Y1\<close> by simp
    from \<open>f y1 = f y1'\<close> have "g (f y1) = g (f y1')" by simp
    thus "y1 = y1'" using \<open>g (f y1) = y1\<close> \<open>g (f y1') = y1'\<close> by simp
  qed
  have "bij_betw f Y1 Y2" unfolding bij_betw_def using hf_inj hf_surj by simp
  \<comment> \<open>Bijective quotient map = homeomorphism.\<close>
  from top1_bij_quotient_map_on_imp_homeomorphism_on[OF hf_quot this]
  show ?thesis by (by100 blast)
qed

\<comment> \<open>Elementary operations preserve quotient\\_of\\_scheme\\_on for the SAME space.
   If Y is a quotient of scheme s, and s → t via an elementary operation,
   then Y is also a quotient of scheme t (same polygon, adjusted vertex labeling).\<close>
lemma elementary_operation_preserves_quotient:
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "top1_elementary_scheme_operation s t"
  shows "top1_quotient_of_scheme_on Y TY t"
  using assms(2,1)
proof (induction rule: top1_elementary_scheme_operation.induct)
  case (rotate u v)
  \<comment> \<open>s = u@v, t = v@u. Same polygon, vertices cyclically shifted.\<close>
  thus ?case sorry
next
  case (cancel u a v)
  \<comment> \<open>s = u@[a,a\\<inverse>]@v, t = u@v. Cancel adjacent inverse pair. Fold polygon.\<close>
  thus ?case sorry
next
  case (uncancel u v a)
  \<comment> \<open>s = u@v, t = u@[a,a\\<inverse>]@v. Insert cancellable pair. Unfold polygon.\<close>
  thus ?case sorry
next
  case (invert w)
  \<comment> \<open>s = w, t = rev(map inverse w). Reverse and invert all edges.\<close>
  thus ?case sorry
next
  case (relabel w old new)
  \<comment> \<open>s = w, t = map (rename old\\<to>new) w. Rename label. Same polygon and quotient map.\<close>
  thus ?case sorry
next
  case (flip_label w a)
  \<comment> \<open>s = w, t = map (flip a) w. Same polygon P, quotient map q, vertices.
     The flip preserves fst and the snd-equality correspondence when labels match.
     All 11 conditions of quotient\\_of\\_scheme\\_on transfer with the same witnesses.\<close>
  thus ?case sorry
next
  case (cut_paste u1 a u2 u3)
  \<comment> \<open>s = u1@[a]@u2@[a]@u3, t = u1@[a,a]@rev(inv(u2))@u3. Cut and paste.\<close>
  thus ?case sorry
next
  case (cut_paste2 u0 a u1 u2 b)
  \<comment> \<open>s = u0@[a]@u1@[a]@u2, t = [b]@u2@[b]@u1@rev(inv(u0)). Cut-paste variant.\<close>
  thus ?case sorry
next
  case (cut_paste_opp u0 u1 a u2 u3)
  \<comment> \<open>s = u0@u1@[a]@u2@[a\\<inverse>]@u3, t = u0@[a]@u2@[a\\<inverse>]@u1@u3. Move u1 past a.\<close>
  thus ?case sorry
qed

\<comment> \<open>scheme\\_equiv preserves quotient: if Y is quotient of s and s ~ t, then Y is quotient of t.\<close>
\<comment> \<open>Each elementary operation is reversible: if s → t, then t ~* s.\<close>
lemma elementary_operation_reverse:
  assumes "top1_elementary_scheme_operation s t"
  shows "top1_scheme_equiv t s"
  using assms
proof (induction rule: top1_elementary_scheme_operation.induct)
  case (rotate u v) \<comment> \<open>u@v → v@u. Reverse: rotate v@u → u@v.\<close>
  show ?case unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate[of v u] by simp
next
  case (cancel u a v) \<comment> \<open>u@[a,inv a]@v → u@v. Reverse: uncancel.\<close>
  show ?case unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.uncancel[of u v a] by simp
next
  case (uncancel u v a) \<comment> \<open>u@v → u@[a,inv a]@v. Reverse: cancel.\<close>
  show ?case unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cancel[of u a v] by simp
next
  case (invert w) \<comment> \<open>w → rev(inv w). Reverse: invert again (involutive).\<close>
  have hinv_inv: "\<And>x. top1_inverse_edge (top1_inverse_edge x) = x"
    unfolding top1_inverse_edge_def by simp
  have "rev (map top1_inverse_edge (rev (map top1_inverse_edge w))) = w"
  proof -
    have "map top1_inverse_edge (map top1_inverse_edge w) = w"
    proof (induction w)
      case Nil thus ?case by simp
    next
      case (Cons a w) thus ?case using hinv_inv by simp
    qed
    thus ?thesis by (simp add: rev_map)
  qed
  thus ?case unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.invert[of "rev (map top1_inverse_edge w)"] by simp
next
  case (relabel w old new) \<comment> \<open>Reverse of relabel. Use relabel(new→old) + fix collisions.\<close>
  show ?case sorry
next
  case (flip_label w a) \<comment> \<open>flip is involutive: flip(flip(w)) = w.\<close>
  let ?f = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  have hflip_invol: "?f (?f w) = w"
  proof (induction w)
    case Nil thus ?case by simp
  next
    case (Cons e w) obtain l bo where "e = (l, bo)" by (cases e)
    thus ?case using Cons.IH by simp
  qed
  show ?case unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.flip_label[of "?f w" a] hflip_invol by simp
next
  case (cut_paste u1 a u2 u3) \<comment> \<open>Reverse via cut\\_paste on result.\<close>
  show ?case sorry
next
  case (cut_paste2 u0 a u1 u2 b) show ?case sorry
next
  case (cut_paste_opp u0 u1 a u2 u3)
  \<comment> \<open>Reverse: rotate + cut\\_paste\\_opp + rotate (3 elementary operations).\<close>
  have r1: "top1_elementary_scheme_operation
      (u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1 @ u3)
      (u3 @ u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1)"
    using top1_elementary_scheme_operation.rotate
      [of "u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1" u3] by simp
  have r2: "top1_elementary_scheme_operation
      (u3 @ u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1)
      ([(a,True)] @ u2 @ [(a,False)] @ u3 @ u0 @ u1)"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[]" "u3 @ u0" a u2 u1] by simp
  have r3: "top1_elementary_scheme_operation
      ([(a,True)] @ u2 @ [(a,False)] @ u3 @ u0 @ u1)
      (u0 @ u1 @ [(a,True)] @ u2 @ [(a,False)] @ u3)"
    using top1_elementary_scheme_operation.rotate
      [of "[(a,True)] @ u2 @ [(a,False)] @ u3" "u0 @ u1"] by simp
  show ?case unfolding top1_scheme_equiv_def
    using r1 r2 r3 by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

\<comment> \<open>scheme\\_equiv is symmetric.\<close>
lemma scheme_equiv_sym:
  assumes "top1_scheme_equiv s t"
  shows "top1_scheme_equiv t s"
  using assms unfolding top1_scheme_equiv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl thus ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  from elementary_operation_reverse[OF rtrancl_into_rtrancl.hyps(2)]
  have "top1_scheme_equiv c b" .
  from this rtrancl_into_rtrancl.IH show ?case
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

lemma scheme_equiv_preserves_quotient:
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "top1_scheme_equiv s t"
  shows "top1_quotient_of_scheme_on Y TY t"
  using assms(2,1) unfolding top1_scheme_equiv_def
  by (induction rule: rtranclp.induct) (auto intro: elementary_operation_preserves_quotient)

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
            thus ?thesis unfolding Q_def by (by100 auto)
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

\<comment> \<open>Two convex n-gons in R² are homeomorphic via a boundary-preserving map.
   The homeomorphism maps vertex i of P1 to vertex i of P2, and maps each edge linearly.\<close>
lemma convex_polygon_homeomorphism:
  assumes "top1_is_polygonal_region_on P1 n" and "top1_is_polygonal_region_on P2 n"
  shows "\<exists>\<phi>. top1_homeomorphism_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1)
      P2
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) \<phi>"
  sorry \<comment> \<open>Construct \\<phi> by piecewise-linear map on centroid triangulation.
     NOTE: homeomorphic\\_convex\\_compact from HOL-Analysis/Homeomorphism.thy would give this
     directly, but Complex\\_Main does not import HOL-Analysis. Need direct construction:
     triangulate both polygons from centroids, define affine map on each triangle,
     paste, show continuity via top1\\_continuous\\_map\\_on\\_real2\\_subspace\\_general bridge.\<close>

\<comment> \<open>Quotient-of-scheme uniqueness: any two quotient spaces of the same scheme are homeomorphic.
   Proof: both are quotients of convex n-gons by the same identification pattern.
   The n-gons are homeomorphic (convex compact in R²), and the homeomorphism respects
   the boundary identifications. So the quotient spaces are homeomorphic.\<close>
lemma scheme_quotient_uniqueness:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 scheme"
      and "top1_quotient_of_scheme_on Y2 TY2 scheme"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Extract full polygon data from both quotients (including vertices and identification).\<close>
  let ?n = "length scheme"
  from assms(3) obtain P1 q1 where
      hP1: "top1_is_polygonal_region_on P1 ?n"
      and hq1: "top1_quotient_map_on P1
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) Y1 TY1 q1"
    by (rule quotient_of_scheme_extract)
  from assms(4) obtain P2 q2 where
      hP2: "top1_is_polygonal_region_on P2 ?n"
      and hq2: "top1_quotient_map_on P2
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) Y2 TY2 q2"
    by (rule quotient_of_scheme_extract)
  \<comment> \<open>Get homeomorphism \\<phi>: P1 \\<to> P2 from convex\\_polygon\\_homeomorphism.\<close>
  from convex_polygon_homeomorphism[OF hP1 hP2]
  obtain \<phi> where h\<phi>: "top1_homeomorphism_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) P2
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) \<phi>"
    by (by100 blast)
  \<comment> \<open>q2 \\<circ> \\<phi>: P1 \\<to> Y2 is a quotient map.\<close>
  have h\<phi>_quot: "top1_quotient_map_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) P2
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) \<phi>"
    by (rule top1_homeomorphism_on_imp_quotient_map_on[OF h\<phi>])
  have hcomp_quot: "top1_quotient_map_on P1
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P1) Y2 TY2 (q2 \<circ> \<phi>)"
    by (rule top1_quotient_map_on_comp[OF h\<phi>_quot hq2])
  \<comment> \<open>Fibres of q1 and q2\\<circ>\\<phi> agree: both identify boundary points according to the same scheme.
     Interior points have singleton fibres under both maps.
     Edge points: \\<phi> maps edge i of P1 to edge i of P2 (by h\\<phi>\\_edge), so the scheme
     identification pattern is preserved.\<close>
  have hfibres: "\<forall>x\<in>P1. \<forall>y\<in>P1. (q1 x = q1 y) \<longleftrightarrow> ((q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y)"
    sorry \<comment> \<open>Uses h\\<phi>\\_edge + hq1\\_ident + hq1\\_inj + hq1\\_bd + matching conditions on P2.
       Key: \\<phi> preserves the edge parametrization, so same-scheme identification \\<Rightarrow> same fibres.
       The proof needs the vx1'/vy1' from \\<phi> to match the vx1/vy1 from q1, which requires
       showing that the vertex functions are essentially unique (up to the polygon's geometry).\<close>
  from quotient_same_fibres_homeomorphic[OF hq1 hcomp_quot hfibres]
  show ?thesis .
qed

\<comment> \<open>scheme\\_equiv preserves homeomorphism type: equivalent schemes give homeomorphic quotients.\<close>
lemma scheme_equiv_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 s"
      and "top1_quotient_of_scheme_on Y2 TY2 t"
      and "top1_scheme_equiv s t"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  have "top1_quotient_of_scheme_on Y1 TY1 t"
    by (rule scheme_equiv_preserves_quotient[OF assms(3) assms(5)])
  from scheme_quotient_uniqueness[OF assms(1) assms(2) this assms(4)]
  show ?thesis .
qed

\<comment> \<open>Scheme rotation preserves quotient type: quotient(u@v) \\<cong> quotient(v@u).
   The edge identifications are the same up to cyclic shift.\<close>
lemma scheme_rotate_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (v @ u)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation iv): "Permute. Renumbering the vertices of the
     polygonal region so as to begin with a different vertex does not affect the quotient space."
     Formal argument: u@v and v@u have the same length n = |u|+|v|. Define shifted vertex
     positions vx'(i) = vx((i+|u|) mod n). The polygon P is unchanged (same convex hull).
     The quotient map q is unchanged. The scheme (v@u)!i = (u@v)!((i+|u|) mod n), so all
     identification conditions transfer. Apply quotient\\_same\\_fibres\\_homeomorphic.\<close>
  let ?n = "length u + length v"
  \<comment> \<open>Strategy: Show Y1 is ALSO a quotient of v@u (same polygon, rotated vertices).
     Then Y1 and Y2 are both quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  \<comment> \<open>The scheme v@u has the same length.\<close>
  have hlen_eq: "length (v @ u) = ?n" by simp
  have hlen_uv: "length (u @ v) = ?n" by simp
  \<comment> \<open>Key: (v@u)!i = (u@v)!((i + length u) mod n) for i < n.\<close>
  have hshift: "\<forall>i < ?n. (v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
  proof (intro allI impI)
    fix i assume "i < ?n"
    show "(v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
    proof (cases "i < length v")
      case True
      hence "(v @ u) ! i = v ! i" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i + length u"
        using True by simp
      moreover have "(u @ v) ! (i + length u) = v ! i"
        using True by (simp add: nth_append)
      ultimately show ?thesis by simp
    next
      case False
      hence "i \<ge> length v" by linarith
      hence "(v @ u) ! i = u ! (i - length v)" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i - length v"
      proof -
        have "i + length u = ?n + (i - length v)" using \<open>i \<ge> length v\<close> by linarith
        hence "(i + length u) mod ?n = (?n + (i - length v)) mod ?n"
          by (metis add.commute)
        also have "\<dots> = (i - length v) mod ?n" by simp
        also have "\<dots> = i - length v"
          using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by simp
        finally show ?thesis .
      qed
      moreover have "(u @ v) ! (i - length v) = u ! (i - length v)"
      proof -
        have "i - length v < length u" using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by linarith
        thus ?thesis by (simp add: nth_append)
      qed
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>Y1 is also a quotient of v@u (same polygon, rotated vertex numbering).\<close>
  have hY1_vu: "top1_quotient_of_scheme_on Y1 TY1 (v @ u)"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.rotate])
  \<comment> \<open>Both Y1 and Y2 are quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_vu assms(4)])
qed

\<comment> \<open>Scheme cancellation preserves quotient type: quotient(u@[a,a\\<inverse>]@v) \\<cong> quotient(u@v).
   Folding two adjacent inverse edges doesn't change the quotient space.\<close>
lemma scheme_cancel_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ [a, top1_inverse_edge a] @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (u @ v)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation vi): "Cancel. Replace w = y0 a a\\<inverse> y1 by y0 y1."
     Formal: The (n+2)-gon for u@[a,a\\<inverse>]@v has two adjacent edges labeled a, a\\<inverse>.
     These edges are identified in the quotient. "Folding" the polygon along these edges
     gives an n-gon. The fold map is a quotient map P(n+2) \\<to> P(n) that preserves
     all other edge identifications.
     Compose: q1: P(n+2) \\<to> Y1, fold: P(n+2) \\<to> P(n), and q2\\<inverse>: P(n) \\<to> Y2.
     The composition gives a homeomorphism Y1 \\<to> Y2.\<close>
  \<comment> \<open>By elementary\\_operation\\_preserves\\_quotient with the cancel rule:
     Y1 is also a quotient of u@v. Then scheme\\_quotient\\_uniqueness gives Y1 \\<cong> Y2.\<close>
  have "top1_quotient_of_scheme_on Y1 TY1 (u @ v)"
    by (rule elementary_operation_preserves_quotient[OF assms(3)
        top1_elementary_scheme_operation.cancel[of u a v]])
  from scheme_quotient_uniqueness[OF assms(1) assms(2) this assms(4)]
  show ?thesis .
qed

\<comment> \<open>Scheme inversion preserves quotient type: quotient(w) \\<cong> quotient(rev(map inverse w)).
   Reflecting the polygon preserves the quotient space.\<close>
lemma scheme_invert_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 w"
      and "top1_quotient_of_scheme_on Y2 TY2 (rev (map top1_inverse_edge w))"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation v): "Flip. Flipping the polygonal region over.
     The order of the vertices is reversed, and so is the orientation of each edge."
     Formal: Reflecting the polygon (reversing vertex order) gives a valid quotient
     of rev(map inverse w). Then scheme\\_quotient\\_uniqueness gives Y1 \\<cong> Y2.\<close>
  have hY1_inv: "top1_quotient_of_scheme_on Y1 TY1 (rev (map top1_inverse_edge w))"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.invert])
  \<comment> \<open>Originally: Extract (P,q,vx,vy) from assms(3). Define reflected vertices:
       vx'(i) = vx(n-1-i), vy'(i) = vy(n-1-i) (reverse order).
       The same polygon P (reflection is a homeomorphism), same quotient map q.
       Edge i in the reflected scheme = inverse of edge (n-1-i) in w.
       All conditions transfer via the reversal.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_inv assms(4)])
qed
  \<comment> \<open>Reflect the polygon (reverse vertex order + flip orientations).
     The reflection map commutes with the identification.\<close>

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
  \<comment> \<open>Prove the strong version: for ALL quotient spaces of related schemes, homeo.\<close>
  have hcases: "\<And>s t. top1_elementary_scheme_operation s t \<Longrightarrow>
      top1_quotient_of_scheme_on X1 TX1 s \<Longrightarrow>
      top1_quotient_of_scheme_on X2 TX2 t \<Longrightarrow>
      \<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
  proof -
    fix s t assume hop: "top1_elementary_scheme_operation s t"
        and hs: "top1_quotient_of_scheme_on X1 TX1 s"
        and ht: "top1_quotient_of_scheme_on X2 TX2 t"
    \<comment> \<open>First prove for ANY pair of quotient spaces (needed for sym/trans cases).\<close>
    have huniv: "\<And>s t (Y1 :: 'x set) TY1 (Y2 :: 'x set) TY2.
        top1_elementary_scheme_operation s t \<Longrightarrow>
        is_topology_on_strict Y1 TY1 \<Longrightarrow> is_topology_on_strict Y2 TY2 \<Longrightarrow>
        top1_quotient_of_scheme_on Y1 TY1 s \<Longrightarrow>
        top1_quotient_of_scheme_on Y2 TY2 t \<Longrightarrow>
        \<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
    proof -
      fix s t and Y1 :: "'x set" and TY1 and Y2 :: "'x set" and TY2
      assume hop: "top1_elementary_scheme_operation s t"
          and hY1: "is_topology_on_strict Y1 TY1" and hY2: "is_topology_on_strict Y2 TY2"
          and hs: "top1_quotient_of_scheme_on Y1 TY1 s"
          and ht: "top1_quotient_of_scheme_on Y2 TY2 t"
      show "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h" using hop
      proof (cases rule: top1_elementary_scheme_operation.cases)
        case (rotate u v)
        then show ?thesis using scheme_rotate_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (cancel u a v)
        then show ?thesis using scheme_cancel_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (uncancel u v a)
        \<comment> \<open>Uncancel = reverse of cancel. s = u@v, t = u@[a, a\\<inverse>]@v.\<close>
        have hs2: "top1_quotient_of_scheme_on Y1 TY1 (u @ v)" using hs uncancel by simp
        have ht2: "top1_quotient_of_scheme_on Y2 TY2 (u @ [a, top1_inverse_edge a] @ v)"
          using ht uncancel by simp
        from scheme_cancel_homeomorphic[OF hY2 hY1 ht2 hs2]
        obtain h where "top1_homeomorphism_on Y2 TY2 Y1 TY1 h" by (by100 blast)
        from homeomorphism_inverse[OF this]
        show ?thesis by (by100 blast)
      next
        case invert
        then show ?thesis using scheme_invert_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (relabel old new)
        \<comment> \<open>Relabeling preserves the quotient: same polygon, same q, renamed labels.
           Y1 is also a quotient of the relabeled scheme. Then scheme\\_quotient\\_uniqueness.\<close>
        have hop_relabel: "top1_elementary_scheme_operation s (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule top1_elementary_scheme_operation.relabel)
        have hY1_relabel: "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs hop_relabel])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          using ht relabel by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (flip_label a)
        \<comment> \<open>Flipping orientations: same polygon, same q, flipped edge directions.
           Y1 is also a quotient of the flipped scheme.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs top1_elementary_scheme_operation.flip_label])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          using ht flip_label by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste u1 a u2 u3)
        \<comment> \<open>Cut-and-repaste: \\<S>76 Theorem 76.1. Cut, flip, paste preserves quotient.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
            using hs cut_paste by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste[of u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
          using ht cut_paste by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste2 u0 a u1 u2 b)
        have "top1_quotient_of_scheme_on Y1 TY1
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
            using hs cut_paste2 by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste2[of u0 a u1 u2 b]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
          using ht cut_paste2 by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste_opp u0 u1 a u2 u3)
        have "top1_quotient_of_scheme_on Y1 TY1
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
            using hs cut_paste_opp by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste_opp[of u0 u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
          using ht cut_paste_opp by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      qed
    qed
    from huniv[OF hop assms(1) assms(2) hs ht]
    show "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h" .
  qed
  show ?thesis using hcases[OF assms(3)] assms(4) by (by100 blast)
qed



\<comment> \<open>§75 + §73 + §74.4 moved to AlgTopCached8.\<close>

\<comment> \<open>NOTE: free\_abelian\_quotient\_by\_twice\_sum\_structure was here but is unused —
   its content is fully proved inside Theorem\_75\_4 (certified in AlgTopCached12).
   Removed per expert audit 13 recommendation.\<close>

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
  \<comment> \<open>Step 1: By Theorem 78.1, X is a quotient of finitely many triangular regions.\<close>
  from Theorem_78_1_triangulable_surface[OF assms(1) assms(3)]
  obtain \<T> q_tri where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      "\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3"
      "\<forall>T \<in> \<T>. top1_continuous_map_on T
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_tri"
      "(\<Union>T\<in>\<T>. q_tri ` T) = X"
      "\<forall>U. U \<subseteq> X \<longrightarrow>
          (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
              subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
    by (by100 auto)
  \<comment> \<open>Step 2: Iteratively paste triangles along shared edges using Theorem 76.1 (\\<S>76).
     Book proof: "As long as two regions have edges bearing the same label, we can
     paste them together. Eventually either one has a single polygon (theorem proved)
     or several polygons with no shared labels. The latter gives a disconnected space,
     contradicting X connected."
     Formally: induction on card(\\<T>). If card = 1: done. If card > 1: find two regions
     sharing a label, paste them (§76.1), reducing card by 1. Apply IH.\<close>
  \<comment> \<open>Base case: if card(\\<T>) = 1, the single triangle is already a polygon.\<close>
  have hbase: "card \<T> = 1 \<Longrightarrow> ?thesis"
  proof -
    assume "card \<T> = 1"
    then obtain T0 where hT0: "\<T> = {T0}" using card_1_singletonE by (by100 blast)
    have hpoly: "top1_is_polygonal_region_on T0 3" using h\<T>(3) hT0 by (by100 blast)
    \<comment> \<open>q\\_tri restricted to T0 is a quotient map from T0 to X.
       Coverage: q\\_tri ` T0 = X (since \\<Union>\\<T> = X and \\<T> = {T0}).
       Quotient topology: U \\<in> TX \\<longleftrightarrow> preimage in T0 is open (from h\\<T>(6)).\<close>
    have hcov: "q_tri ` T0 = X" using h\<T>(5) hT0 by (by100 auto)
    have hcont: "top1_continuous_map_on T0
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0) X TX q_tri"
      using h\<T>(4) hT0 by (by100 blast)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0"
    have hquot_cond: "\<And>U. U \<subseteq> X \<Longrightarrow> U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP"
    proof -
      fix U assume "U \<subseteq> X"
      from h\<T>(6)[rule_format, OF this]
      have "U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T)" .
      also have "\<dots> = ({p\<in>T0. q_tri p \<in> U} \<in> ?TP)"
        using hT0 by simp
      finally show "U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP" .
    qed
    have hquot: "top1_quotient_map_on T0 ?TP X TX q_tri"
      unfolding top1_quotient_map_on_def
    proof (intro conjI allI impI)
      show "is_topology_on T0 ?TP"
        using subspace_topology_is_topology_on[OF product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]] by simp
      show "is_topology_on X TX"
        using assms(1) unfolding top1_is_surface_on_def top1_connected_on_def by (by100 blast)
      show "top1_continuous_map_on T0 ?TP X TX q_tri" by (rule hcont)
      show "q_tri ` T0 = X" by (rule hcov)
      fix V assume "V \<subseteq> X" "{p \<in> T0. q_tri p \<in> V} \<in> ?TP"
      thus "V \<in> TX" using hquot_cond[OF \<open>V \<subseteq> X\<close>] by simp
    qed
    show ?thesis
      apply (rule exI[of _ T0], rule exI[of _ 3], rule exI[of _ q_tri])
      using hpoly hquot by (by100 blast)
  qed
  \<comment> \<open>Inductive step: if card > 1, find two adjacent triangles, paste them.\<close>
  show ?thesis
  proof (cases "card \<T> = 1")
    case True thus ?thesis by (rule hbase)
  next
    case False
    \<comment> \<open>card(\\<T>) > 1. By connectedness of X, two triangles share an edge.
       Paste them (\\<S>76 Theorem 76.1) to get a larger polygon. Repeat.\<close>
    have "card \<T> \<noteq> 0" using h\<T>(2) h\<T>(1) by (by100 auto)
    hence "card \<T> > 1" using False \<open>card \<T> \<noteq> 0\<close> by (by100 linarith)
    show ?thesis sorry \<comment> \<open>Induction on card(\\<T>) > 1. At each step, paste two adjacent
       regions sharing a label. When card = 1: done (base case above).\<close>
  qed
qed

section \<open>\<S>77 The Classification Theorem\<close>

\<comment> \<open>Lemma 77.1 Step 1, subcase y2 = []: a y1 a ~ aa y1\\<inverse>.
   Sequence: rotate \\<to> invert \\<to> flip\\_label a.
   Requires: a does not appear in y1 (from proper scheme).\<close>
lemma Lemma_77_1_step1_y2_empty:
  assumes "\<forall>e \<in> set y1. fst e \<noteq> a"
  shows "top1_scheme_equiv
      ([(a, True)] @ y1 @ [(a, True)])
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
proof -
  \<comment> \<open>Step 1: Rotate: [(a,T)] @ y1 @ [(a,T)] \\<to> y1 @ [(a,T),(a,T)].\<close>
  have h1: "top1_elementary_scheme_operation
      ([(a, True)] @ (y1 @ [(a, True)]))
      ((y1 @ [(a, True)]) @ [(a, True)])"
    by (rule top1_elementary_scheme_operation.rotate)
  \<comment> \<open>Step 2: Invert: y1 @ [(a,T),(a,T)] \\<to> [(a,F),(a,F)] @ inv(y1).\<close>
  have h2: "top1_elementary_scheme_operation
      (y1 @ [(a, True), (a, True)])
      (rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)])))"
    by (rule top1_elementary_scheme_operation.invert)
  \<comment> \<open>Simplify: rev(map inv (y1 @ [(a,T),(a,T)])) = [(a,F),(a,F)] @ rev(map inv y1).\<close>
  have h2_simp: "rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)]))
      = [(a, False), (a, False)] @ rev (map top1_inverse_edge y1)"
    unfolding top1_inverse_edge_def by simp
  \<comment> \<open>Step 3: flip\\_label a: [(a,F),(a,F)] @ inv(y1) \\<to> [(a,T),(a,T)] @ inv(y1).
     (Since a not in y1, flip\\_label only affects the two a-edges.)\<close>
  have h3: "top1_elementary_scheme_operation
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      (map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
           ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1)))"
    by (rule top1_elementary_scheme_operation.flip_label)
  have h3_simp: "map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      = [(a, True), (a, True)] @ rev (map top1_inverse_edge y1)"
  proof -
    have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) [(a, False), (a, False)]
        = [(a, True), (a, True)]" by simp
    moreover have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) (rev (map top1_inverse_edge y1))
        = rev (map top1_inverse_edge y1)"
    proof (rule map_idI)
      fix e assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by simp
      then obtain e0 where "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 auto)
      hence "fst e = fst e0" unfolding top1_inverse_edge_def by (by100 simp)
      have "fst e0 \<noteq> a" using assms \<open>e0 \<in> set y1\<close> by (by100 blast)
      hence "fst e \<noteq> a" using \<open>fst e = fst e0\<close> by simp
      thus "(case e of (l, b) \<Rightarrow> (l, if l = a then \<not> b else b)) = e"
        using \<open>fst e \<noteq> a\<close> by (cases e) simp
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Chain: w \\<to> w1 \\<to> w2 \\<to> w3.\<close>
  \<comment> \<open>Chain the 3 operations via rtranclp.\<close>
  have step1: "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)]) (y1 @ [(a, True), (a, True)])"
    unfolding top1_scheme_equiv_def using h1 by simp
  have step2: "top1_scheme_equiv (y1 @ [(a, True), (a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h2 h2_simp by simp
  have step3: "top1_scheme_equiv ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h3 h3_simp by simp
  \<comment> \<open>Chain: step1 \\<to> step2 \\<to> step3.\<close>
  from step1 step2 have "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from this step3 show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Lemma 77.1 (Munkres): If w = [y0] a [y1] a [y2] (proper scheme with a appearing twice
   with same exponent), then w ~ aa [y0 y1\\<inverse> y2].\<close>
lemma Lemma_77_1_projective_collection:
  assumes "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
      and "\<exists>b::'a. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  shows "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
proof (cases "y0 = []")
  case True
  \<comment> \<open>Step 1: y0 empty. Show a y1 a y2 ~ aa y1\\<inverse> y2.\<close>
  show ?thesis
  proof (cases "y1 = []")
    case True
    \<comment> \<open>y1 = []: a a y2 ~ aa y2. Trivially same (reflexivity).\<close>
    show ?thesis using \<open>y0 = []\<close> True unfolding top1_scheme_equiv_def by simp
  next
    case False
    show ?thesis
    proof (cases "y2 = []")
      case True
      \<comment> \<open>y2 = []: a y1 a ~ aa y1\\<inverse>. Use Lemma\\_77\\_1\\_step1\\_y2\\_empty.\<close>
      have "\<forall>e \<in> set y1. fst e \<noteq> a" using assms by (by100 blast)
      from Lemma_77_1_step1_y2_empty[OF this]
      show ?thesis using \<open>y0 = []\<close> True by simp
    next
      case False2: False
      \<comment> \<open>Both y1, y2 non-empty: direct from cut\\_paste operation.\<close>
      have "top1_elementary_scheme_operation
          ([] @ [(a, True)] @ y1 @ [(a, True)] @ y2)
          ([] @ [(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        by (rule top1_elementary_scheme_operation.cut_paste)
      hence "top1_scheme_equiv
          ([(a, True)] @ y1 @ [(a, True)] @ y2)
          ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        unfolding top1_scheme_equiv_def by simp
      thus ?thesis using \<open>y0 = []\<close> by simp
    qed
  qed
next
  case False
  \<comment> \<open>Step 2: y0 non-empty. Book proof (Munkres Figure 77.2):
     y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> \\<sim> aa y0 y1\\<inverse> y2.\<close>
  \<comment> \<open>Choose a fresh label b \\<noteq> a (exists because labels are from an infinite type).\<close>
  obtain b :: 'a where hb: "b \<noteq> a" "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    using assms(2) by (by100 blast)
  \<comment> \<open>Step 2a: y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) via cut\\_paste2.\<close>
  have step2a: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste2[of y0 a y1 y2 b] by simp
  \<comment> \<open>Step 2b: b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> via cut\\_paste (Step 1).\<close>
  have step2b: "top1_scheme_equiv
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste[of "[]" b y2 "y1 @ rev (map top1_inverse_edge y0)"]
    by simp
  \<comment> \<open>Step 2c: bb y2\\<inverse> y1 y0\\<inverse> \\<sim> (y0 y1\\<inverse> y2) b\\<inverse> b\\<inverse> via invert.\<close>
  have step2c: "top1_scheme_equiv
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
        (rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))))"
      by (rule top1_elementary_scheme_operation.invert)
    moreover have "rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0)))
        = y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)]"
    proof -
      have hinv_inv: "\<And>x. top1_inverse_edge (top1_inverse_edge x) = x"
        unfolding top1_inverse_edge_def by (by100 simp)
      have hmap_inv_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (map top1_inverse_edge xs) = xs"
        by (simp add: hinv_inv map_idI)
      have hrev_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map top1_inverse_edge (rev (map top1_inverse_edge xs))
            = rev (map top1_inverse_edge (map top1_inverse_edge xs))"
          by (simp add: rev_map)
        also have "\<dots> = rev xs" using hmap_inv_inv by simp
        finally show "map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs" .
      qed
      have hcomp_id: "top1_inverse_edge \<circ> top1_inverse_edge = id"
      proof (rule ext)
        fix x show "(top1_inverse_edge \<circ> top1_inverse_edge) x = id x" using hinv_inv by simp
      qed
      have hmap_comp_id: "\<And>xs :: ('a \<times> bool) list. map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = map id xs"
          by (rule arg_cong[of _ _ "\<lambda>f. map f xs"]) (rule hcomp_id)
        thus "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs" by simp
      qed
      show ?thesis
        by (simp add: rev_map hmap_comp_id hrev_inv top1_inverse_edge_def)
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2d: rotate to b\\<inverse> b\\<inverse> (y0 y1\\<inverse> y2).\<close>
  have step2d: "top1_scheme_equiv
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate[of
        "y0 @ rev (map top1_inverse_edge y1) @ y2" "[(b, False), (b, False)]"]
    by simp
  \<comment> \<open>Step 2e: flip\\_label b: b\\<inverse>b\\<inverse> \\<to> bb.\<close>
  have step2e: "top1_scheme_equiv
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
             ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.flip_label)
    moreover have "map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have "\<And>xs. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      moreover have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2f: relabel b \\<to> a.\<close>
  have step2f: "top1_scheme_equiv
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (if l = b then a else l, bo))
             ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.relabel)
    moreover have "map (\<lambda>(l, bo). (if l = b then a else l, bo))
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have hmap_relabel: "\<And>xs :: ('a \<times> bool) list. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (if l = b then a else l, bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      have "\<forall>e \<in> set y0. fst e \<noteq> b" using hb(2) by (by100 blast)
      have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      have "\<forall>e \<in> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      show ?thesis
        using hmap_relabel[OF \<open>\<forall>e \<in> set y0. fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set y2. fst e \<noteq> b\<close>]
        by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Chain all steps.\<close>
  \<comment> \<open>Chain all steps via transitivity.\<close>
  from step2a step2b have s_ab: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_ab step2c have s_abc: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abc step2d have s_abcd: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcd step2e have s_abcde: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcde step2f show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Key lemma: for w0=[], w2=[], we can extract the commutator to front.
   a b w1 a\\<inverse> b\\<inverse> ~ a b a\\<inverse> b\\<inverse> w1.
   6-step sequence: rotate, flip\\_label a, cut\\_paste\\_opp a, flip\\_label a, rotate, cut\\_paste\\_opp b.\<close>
lemma Lemma_77_3_simple:
  assumes hab: "a \<noteq> b"
  shows "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
proof -
  let ?w = "[(a, True), (b, True)] @ w1 @ [(a, False), (b, False)]"
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_elementary_scheme_operation ?w
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
    using top1_elementary_scheme_operation.rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)]"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_elementary_scheme_operation
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    \<comment> \<open>First show the target equals the map result.\<close>
    have htarget: "?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a (move ?flip\\_a w1 from before a to after a\\<inverse>).\<close>
  have s3: "top1_elementary_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)]" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (flip back: restores w1).\<close>
  have s4: "top1_elementary_scheme_operation
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    have hflip_invol: "?flip_a (?flip_a w1) = w1"
    proof (induction w1)
      case Nil thus ?case by simp
    next
      case (Cons e w1)
      obtain l bo where he: "e = (l, bo)" by (cases e)
      show ?case using Cons.IH by (simp add: he)
    qed
    have htarget: "[(a, False), (b, False), (a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_elementary_scheme_operation
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])"
    using top1_elementary_scheme_operation.rotate
      [of "[(a,False),(b,False)]" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b (move w1 from before b to after b\\<inverse>).\<close>
  have s6: "top1_elementary_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" "[]"] by simp
  \<comment> \<open>Chain all steps.\<close>
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_scheme_equiv_def
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

\<comment> \<open>Extended simple case: a b w1 a\\<inverse> b\\<inverse> w2 ~ a b a\\<inverse> b\\<inverse> w1 w2 (w0=[], general w2).
   Same 6-step proof as Lemma\\_77\\_3\\_simple — the tail w2 passes through all steps.\<close>
lemma Lemma_77_3_w0_empty:
  assumes hab: "a \<noteq> b"
  shows "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  have hba: "b \<noteq> a" using hab by (by100 blast)
  have hflip_invol: "\<And>xs. ?flip_a (?flip_a xs) = xs"
  proof -
    fix xs :: "('a \<times> bool) list"
    show "?flip_a (?flip_a xs) = xs"
    proof (induction xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
      thus ?case using Cons.IH by simp
    qed
  qed
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_elementary_scheme_operation
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
    using top1_elementary_scheme_operation.rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)] @ w2"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_elementary_scheme_operation
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])"
  proof -
    have htarget: "?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a.\<close>
  have s3: "top1_elementary_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)] @ ?flip_a w2" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (restores w1 and w2).\<close>
  have s4: "top1_elementary_scheme_operation
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])"
  proof -
    have htarget: "[(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_elementary_scheme_operation
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)"
    using top1_elementary_scheme_operation.rotate
      [of "[(a,False),(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b.\<close>
  have s6: "top1_elementary_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" w2] by simp
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_scheme_equiv_def
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

\<comment> \<open>Lemma 77.3 (Munkres): general case. w0 a b w1 a\\<inverse> b\\<inverse> w2 ~ (aba\\<inverse>b\\<inverse>) w0 w1 w2.
   Proof: cut\\_paste\\_opp to move w0, then w0-empty case, then cut\\_paste\\_opp on b.\<close>
lemma Lemma_77_3_torus_extraction:
  assumes "a \<noteq> b"
  shows "top1_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  let ?flip_b = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs"
  have hab': "b \<noteq> a" using assms by (by100 blast)
  \<comment> \<open>Step 1: cut\\_paste\\_opp on a moves w0 past a\\<inverse>.\<close>
  have s1: "top1_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste_opp[of "[]" w0 a "[(b,True)] @ w1" "[(b,False)] @ w2"]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>After step 1: a b w1 a\\<inverse> w0 b\\<inverse> w2.
     Step 2 (flip trick on a, 5 ops): swap w1 past (b,T).
     Result: a w1 b a\\<inverse> w0 b\\<inverse> w2.\<close>
  have s2: "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move [(a,T),(b,T)] to end.\<close>
    have r1: "top1_elementary_scheme_operation
        ([(a,True),(b,True)] @ w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2)
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,True),(b,True)]" "w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label a.\<close>
    have r2_eq: "?flip_a (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        = ?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)]"
      using hab' by simp
    have r2: "top1_elementary_scheme_operation
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])"
      unfolding r2_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>cut\\_paste\\_opp on a: move ?flip\\_a w1 from before a to after a\\<inverse>.\<close>
    have r3: "top1_elementary_scheme_operation
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])"
      using top1_elementary_scheme_operation.cut_paste_opp
        [of "[]" "?flip_a w1" a "?flip_a w0 @ [(b,False)] @ ?flip_a w2" "[(b,True)]"] by simp
    \<comment> \<open>flip\\_label a back.\<close>
    have r4_eq: "?flip_a ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        = [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)]"
    proof -
      have hflip_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_a (?flip_a xs) = xs"
      proof -
        fix xs :: "('a \<times> bool) list" show "?flip_a (?flip_a xs) = xs"
        proof (induction xs)
          case Nil thus ?case by simp
        next
          case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
          thus ?case using Cons.IH by simp
        qed
      qed
      thus ?thesis using hab' by simp
    qed
    have r4: "top1_elementary_scheme_operation
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])"
      unfolding r4_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>rotate: bring [(a,T)] w1 [(b,T)] to front.\<close>
    have r5: "top1_elementary_scheme_operation
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,False)] @ w0 @ [(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_scheme_equiv_def
      by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  qed
  \<comment> \<open>Step 3 (flip trick on b, 5 ops): move w0 from between a\\<inverse>, b\\<inverse> to between b, a\\<inverse>.
     Result: a w1 b w0 a\\<inverse> b\\<inverse> w2 (now a\\<inverse>b\\<inverse> are adjacent!).\<close>
  have s3: "top1_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move prefix to end.\<close>
    have r1: "top1_elementary_scheme_operation
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,True)] @ w1 @ [(b,True),(a,False)]" "w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label b.\<close>
    have r2_eq: "?flip_b (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        = ?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)]"
      using assms by simp
    have r2: "top1_elementary_scheme_operation
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])"
      unfolding r2_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>cut\\_paste\\_opp on b: move ?flip\\_b w0 from before b to after b\\<inverse>.\<close>
    have r3: "top1_elementary_scheme_operation
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])"
      using top1_elementary_scheme_operation.cut_paste_opp
        [of "[]" "?flip_b w0" b "?flip_b w2 @ [(a,True)] @ ?flip_b w1" "[(a,False)]"] by simp
    \<comment> \<open>flip\\_label b back.\<close>
    have hflip_b_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_b (?flip_b xs) = xs"
    proof -
      fix xs :: "('a \<times> bool) list" show "?flip_b (?flip_b xs) = xs"
      proof (induction xs)
        case Nil thus ?case by simp
      next
        case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
        thus ?case using Cons.IH by simp
      qed
    qed
    have r4_eq: "?flip_b ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        = [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"
      using assms hflip_b_invol by simp
    have r4: "top1_elementary_scheme_operation
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])"
      unfolding r4_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>rotate: bring the right part to front.\<close>
    have r5: "top1_elementary_scheme_operation
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])
        ([(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False),(b,False)] @ w2)"
      using top1_elementary_scheme_operation.rotate
        [of "[(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_scheme_equiv_def
      by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  qed
  \<comment> \<open>Step 4: cut\\_paste\\_opp on b moves w1 from before b to after b\\<inverse>.
     a [w1] b [w0] a\\<inverse> b\\<inverse> w2 \\<to> a b [w0] a\\<inverse> b\\<inverse> [w1] w2.\<close>
  have s4: "top1_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste_opp[of "[(a,True)]" w1 b "w0 @ [(a,False)]" w2]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>Step 5: apply Lemma\\_77\\_3\\_w0\\_empty: a b w0 a\\<inverse> b\\<inverse> (w1@w2) ~ a b a\\<inverse> b\\<inverse> w0 w1 w2.\<close>
  have s5: "top1_scheme_equiv
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
    using Lemma_77_3_w0_empty[OF assms, of w0 "w1 @ w2"] by simp
  from s1 s2 s3 s4 s5 show ?thesis
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

\<comment> \<open>Lemma 77.4 (Munkres): A projective pair + commutator = 3 projective pairs.
   w0 (cc)(aba\\<inverse>b\\<inverse>) w1 ~ w0 (aabbcc) w1.
   Proof: 5-step chain using Lemma 77.1 (*) and rotations.\<close>
lemma Lemma_77_4_projective_absorbs_torus:
  fixes a b c :: 'a and w0 w1 :: "('a \<times> bool) list"
  assumes "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
      and "\<forall>e \<in> set w0 \<union> set w1. fst e \<noteq> a \<and> fst e \<noteq> b \<and> fst e \<noteq> c"
      and "infinite (UNIV :: 'a set)"
  shows "top1_scheme_equiv
      (w0 @ [(c, True), (c, True), (a, True), (b, True), (a, False), (b, False)] @ w1)
      (w0 @ [(a, True), (a, True), (b, True), (b, True), (c, True), (c, True)] @ w1)"
proof -
  \<comment> \<open>Fresh label helper: since UNIV is infinite and our sets are finite, fresh labels exist.\<close>
  have hfresh: "\<And>S :: 'a set. finite S \<Longrightarrow> \<exists>x. x \<notin> S"
  proof -
    fix S :: "'a set" assume "finite S"
    from assms(5) have "\<not> finite (UNIV :: 'a set)" by simp
    hence "UNIV \<noteq> S" using \<open>finite S\<close> by (by100 blast)
    thus "\<exists>x. x \<notin> S" by (by100 blast)
  qed
  \<comment> \<open>Obtain a fresh label d \\<noteq> a,b,c and not in w0,w1.\<close>
  obtain d :: 'a where hd: "d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}"
  proof -
    have "finite (fst ` (set w0 \<union> set w1) \<union> {a, b, c} :: 'a set)" by simp
    moreover have "\<not> finite (UNIV :: 'a set)" using assms(5) by simp
    ultimately have "UNIV \<noteq> (fst ` (set w0 \<union> set w1) \<union> {a, b, c} :: 'a set)" by (by100 metis)
    hence "\<exists>d :: 'a. d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}" by (by100 blast)
    thus ?thesis using that by (by100 blast)
  qed
  hence hd_ne: "d \<noteq> a" "d \<noteq> b" "d \<noteq> c" and hd_fresh: "\<forall>e \<in> set w0 \<union> set w1. fst e \<noteq> d"
    by (by100 auto)+
  \<comment> \<open>Pre-establish all three Lemma 77.1 applications.\<close>
  have h771_c: "top1_scheme_equiv
      ([(a,True),(b,True)] @ [(c,True)] @ [(b,True),(a,True)] @ [(c,True)] @ (w1 @ w0))
      ([(c,True),(c,True)] @ [(a,True),(b,True)] @ rev (map top1_inverse_edge [(b,True),(a,True)]) @ (w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  have h771_b: "top1_scheme_equiv
      ([(a,True)] @ [(b,True)] @ [(c,True)] @ [(b,True)] @ ([(a,True),(c,True)] @ w1 @ w0))
      ([(b,True),(b,True)] @ [(a,True)] @ rev (map top1_inverse_edge [(c,True)]) @ ([(a,True),(c,True)] @ w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  have h771_a: "top1_scheme_equiv
      ([(b,True),(b,True)] @ [(a,True)] @ [(c,False)] @ [(a,True)] @ ([(c,True)] @ w1 @ w0))
      ([(a,True),(a,True)] @ [(b,True),(b,True)] @ rev (map top1_inverse_edge [(c,False)]) @ ([(c,True)] @ w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  \<comment> \<open>Step 1: Rotate to bring ccaba\\<inverse>b\\<inverse> to front.\<close>
  have s1: "top1_scheme_equiv
      (w0 @ [(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1)
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate
      [of w0 "[(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1"]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>Step 2: Lemma 77.1 (*) reversed on label c.
     Forward (*): y0 c y1 c y2 ~ cc y0 inv(y1) y2
     With y0 = [(a,T),(b,T)], y1 = [(b,T),(a,T)], y2 = w1@w0:
     [(a,T),(b,T)] c [(b,T),(a,T)] c (w1@w0) ~ cc [(a,T),(b,T)] inv([(b,T),(a,T)]) (w1@w0)
     = cc [(a,T),(b,T)] [(a,F),(b,F)] (w1@w0)
     Reversed: cc ab a\\<inverse>b\\<inverse> w1 w0 ~ ab c ba c w1 w0.\<close>
  have s2: "top1_scheme_equiv
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    \<comment> \<open>Forward Lemma 77.1 (*) on label c:
       [(a,T),(b,T)] c [(b,T),(a,T)] c (w1@w0) ~ cc [(a,T),(b,T)] inv([(b,T),(a,T)]) (w1@w0)
       i.e., ab c ba c w1w0 ~ cc ab (ba)\\<inverse> w1w0 = cc ab a\\<inverse>b\\<inverse> w1w0.
       Then apply scheme\\_equiv\\_sym to reverse.\<close>
    have fwd: "top1_scheme_equiv
        ([(a,True),(b,True)] @ [(c,True)] @ [(b,True),(a,True)] @ [(c,True)] @ (w1 @ w0))
        ([(c,True),(c,True)] @ [(a,True),(b,True)] @ rev (map top1_inverse_edge [(b,True),(a,True)]) @ (w1 @ w0))"
      by (rule h771_c)
    moreover have "rev (map top1_inverse_edge [(b,True),(a,True)]) = [(a,False),(b,False)]"
      unfolding top1_inverse_edge_def by simp
    ultimately have fwd': "top1_scheme_equiv
        ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
        ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
      by simp
    show ?thesis by (rule scheme_equiv_sym[OF fwd'])
  qed
  \<comment> \<open>Step 3: Lemma 77.1 (*) forward on label b.
     [a] b [c] b [acw1w0] ~ bb [a] inv([c]) [acw1w0] = bb a c\\<inverse> a c w1 w0.\<close>
  have s3: "top1_scheme_equiv
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_scheme_equiv
        ([(a,True)] @ [(b,True)] @ [(c,True)] @ [(b,True)] @ ([(a,True),(c,True)] @ w1 @ w0))
        ([(b,True),(b,True)] @ [(a,True)] @ rev (map top1_inverse_edge [(c,True)]) @ ([(a,True),(c,True)] @ w1 @ w0))"
      by (rule h771_b)
    moreover have "rev (map top1_inverse_edge [(c,True)]) = [(c,False)]"
      unfolding top1_inverse_edge_def by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Step 4: Lemma 77.1 (*) forward on label a.
     [bb] a [c\\<inverse>] a [cw1w0] ~ aa [bb] inv([c\\<inverse>]) [cw1w0] = aa bb c c w1 w0.\<close>
  have s4: "top1_scheme_equiv
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_scheme_equiv
        ([(b,True),(b,True)] @ [(a,True)] @ [(c,False)] @ [(a,True)] @ ([(c,True)] @ w1 @ w0))
        ([(a,True),(a,True)] @ [(b,True),(b,True)] @ rev (map top1_inverse_edge [(c,False)]) @ ([(c,True)] @ w1 @ w0))"
      by (rule h771_a)
    moreover have "rev (map top1_inverse_edge [(c,False)]) = [(c,True)]"
      unfolding top1_inverse_edge_def by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Step 5: Rotate back.\<close>
  have s5: "top1_scheme_equiv
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)
      (w0 @ [(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate
      [of "[(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1" w0]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  from s1 s2 s3 s4 s5 show ?thesis
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

\<comment> \<open>Predicate: a scheme w is the standard n-fold torus scheme
   a1 b1 a1\\<inverse> b1\\<inverse> ... an bn an\\<inverse> bn\\<inverse> (4n edges). (Moved before scheme\\_normal\\_form.)\<close>
definition top1_is_torus_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_torus_scheme w n \<longleftrightarrow> n > 0 \<and> w = top1_n_torus_scheme n"

\<comment> \<open>Predicate: a scheme w is the standard m-fold projective scheme
   a1 a1 a2 a2 ... am am (2m edges). (Moved before scheme\\_normal\\_form.)\<close>
definition top1_is_projective_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_projective_scheme w m \<longleftrightarrow> m > 0 \<and> w = top1_m_projective_scheme m"

\<comment> \<open>Helper: in a proper length-4 torus-type scheme, the two non-adjacent-pair elements
   have the same label but opposite directions.\<close>
lemma proper_len4_torus_pair_props:
  fixes scheme :: "(nat \<times> bool) list" and e1 e2 :: "nat \<times> bool"
  assumes hlen: "length scheme = 4"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      and htorus: "\<not> (\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))"
      and hfst_eq: "fst e1 = fst e2"
      and he1_in: "e1 \<in> set scheme" and he2_in: "e2 \<in> set scheme"
      and he_ne_lab: "fst e1 \<noteq> fst (scheme ! i)"
      and hi: "i < 3" "fst (scheme!i) = fst (scheme!(i+1))"
  shows "snd e1 \<noteq> snd e2"
  sorry

\<comment> \<open>Main normal form theorem (Munkres \\<S>77 Theorem 77.5 core):
   Every proper labelling scheme is equivalent to one of:
   (1) aa\\<inverse>bb\\<inverse> (sphere, length 4)
   (2) a1a1...amam (projective, m \\<ge> 1)
   (3) a1b1a1\\<inverse>b1\\<inverse>...anbnanbnan\\<inverse>bn\\<inverse> (torus, n \\<ge> 1)\<close>
lemma scheme_normal_form:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 4"
      and "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      \<comment> \<open>Proper: each label appears exactly 0 or 2 times.\<close>
  shows "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w)"
  using assms
proof (induction "length scheme" arbitrary: scheme rule: less_induct)
  case (less scheme)
  \<comment> \<open>Classify: does the scheme have a label with same-direction occurrences (projective type)?
     Or all labels have opposite-direction occurrences (torus type)?\<close>
  show ?case
  proof (cases "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
      \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)")
    case True
    \<comment> \<open>Projective type: at least one label appears twice with same direction.
       Use Lemma 77.1 to collect same-direction pairs, then Lemma 77.4 if needed.\<close>
    show ?thesis sorry
  next
    case False
    \<comment> \<open>Torus type: all labels appear with opposite directions.
       Step 1 (torus): extract commutator blocks using Lemma 77.3.\<close>
    show ?thesis
    proof (cases "length scheme = 4")
      case True
      \<comment> \<open>Base case: length 4 torus scheme.
         If adjacent cancellable pair: cancel to length 2, then uncancel to sphere.
         If no adjacent cancellable pair: labels alternate \\<Rightarrow> torus n=1.\<close>
      show ?thesis
      proof (cases "\<exists>i < 3. fst (scheme!i) = fst (scheme!(i+1))")
        case True
        \<comment> \<open>Adjacent same-label pair (must be opposite direction since torus type).
           Cancel gives length 2 scheme, then uncancel to sphere form.\<close>
        \<comment> \<open>Step: scheme has adjacent same-label pair at some position i.
           Cancel to get length 2 scheme. Then uncancel to sphere.\<close>
        from True obtain i where hi: "i < 3" "fst (scheme!i) = fst (scheme!(i+1))" by (by100 blast)
        \<comment> \<open>Since torus type, the adjacent pair has opposite directions.\<close>
        \<comment> \<open>Cancel → length 2 → uncancel → sphere form [(a,T),(a,F),(b,T),(b,F)].\<close>
        \<comment> \<open>All length 4 torus schemes with adjacent same-label are equivalent to sphere.\<close>
        have "\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)]"
        proof -
          \<comment> \<open>The adjacent pair at position i has opposite directions (torus type).
             So scheme![i+1] = top1\\_inverse\\_edge (scheme![i]).
             Rotate to bring it to front, cancel, uncancel with fresh.\<close>
          \<comment> \<open>scheme!(i+1) = inv(scheme!i): same label + torus type \\<Rightarrow> opposite directions.\<close>
          have hsnd_ne: "snd (scheme!i) \<noteq> snd (scheme!(i+1))"
          proof
            assume "snd (scheme!i) = snd (scheme!(i+1))"
            have "i < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
            have "i+1 < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
            have "i \<noteq> i+1" by simp
            have "fst (scheme!i) = fst (scheme!(i+1))" using hi(2) .
            have "snd (scheme!i) = snd (scheme!(i+1))" by (rule \<open>snd (scheme!i) = snd (scheme!(i+1))\<close>)
            hence "i < length scheme \<and> (i+1) < length scheme \<and> i \<noteq> (i+1) \<and>
                fst (scheme!i) = fst (scheme!i) \<and> fst (scheme!(i+1)) = fst (scheme!i) \<and>
                snd (scheme!i) = snd (scheme!(i+1))"
              using \<open>i < length scheme\<close> \<open>i+1 < length scheme\<close> hi(2) by simp
            hence "\<exists>label. \<exists>ia<length scheme. \<exists>j<length scheme. ia \<noteq> j
                \<and> fst (scheme!ia) = label \<and> fst (scheme!j) = label \<and> snd (scheme!ia) = snd (scheme!j)"
              by (by100 blast)
            with \<open>\<not> (\<exists>label. _)\<close> show False by simp
          qed
          have hinv: "scheme!(i+1) = top1_inverse_edge (scheme!i)"
            using hi(2) hsnd_ne unfolding top1_inverse_edge_def
            by (cases "scheme!i", cases "scheme!(i+1)") simp
          \<comment> \<open>Split the list at position i.\<close>
          define prefix where "prefix = take i scheme"
          define suffix where "suffix = drop (i + 2) scheme"
          have hlen_i: "i + 1 < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
          obtain prefix suffix where
              hdecomp: "scheme = prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix"
              and hlen_ps: "length prefix + length suffix = 2"
              and hlen_pf: "length prefix = i"
          proof
            show "scheme = take i scheme @ [scheme!i, top1_inverse_edge (scheme!i)] @ drop (i+2) scheme"
            proof -
              have "scheme = take i scheme @ scheme!i # drop (Suc i) scheme"
                using id_take_nth_drop[of i scheme] hi(1) \<open>length scheme = 4\<close> by simp
              also have "drop (Suc i) scheme = scheme!(i+1) # drop (Suc (Suc i)) scheme"
                using Cons_nth_drop_Suc[of "Suc i" scheme] hlen_i by simp
              finally show ?thesis using hinv by simp
            qed
            show "length (take i scheme) + length (drop (i+2) scheme) = 2"
              using \<open>length scheme = 4\<close> hi(1) by simp
            show "length (take i scheme) = i"
              using hi(1) \<open>length scheme = 4\<close> by simp
          qed
          \<comment> \<open>Rotate + cancel: scheme ~ prefix @ suffix (length 2).\<close>
          have "top1_scheme_equiv scheme (prefix @ suffix)"
          proof -
            have "top1_elementary_scheme_operation
                (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)
                (prefix @ suffix)"
              by (rule top1_elementary_scheme_operation.cancel)
            thus ?thesis using hdecomp unfolding top1_scheme_equiv_def by simp
          qed
          \<comment> \<open>prefix @ suffix has length 2 = the other label pair. Uncancel to get sphere.\<close>
          obtain a_lab :: nat where ha: "a_lab \<noteq> fst (hd (prefix @ suffix))"
          proof -
            show ?thesis by (rule that[of "Suc (fst (hd (prefix @ suffix)))"]) simp
          qed
          have "top1_scheme_equiv (prefix @ suffix)
              (prefix @ [(a_lab, True), top1_inverse_edge (a_lab, True)] @ suffix)"
            unfolding top1_scheme_equiv_def
            using top1_elementary_scheme_operation.uncancel[of prefix suffix "(a_lab, True)"] by simp
          \<comment> \<open>Chain: scheme ~ cancel ~ uncancel → length 4 with two label pairs.\<close>
          have hinv_simp: "top1_inverse_edge (a_lab, True) = (a_lab, False)"
            unfolding top1_inverse_edge_def by simp
          from \<open>top1_scheme_equiv (prefix @ suffix) _\<close>
          have "top1_scheme_equiv (prefix @ suffix)
              (prefix @ [(a_lab, True), (a_lab, False)] @ suffix)"
            by (simp add: hinv_simp)
          hence "top1_scheme_equiv scheme
              (prefix @ [(a_lab, True), (a_lab, False)] @ suffix)"
            using \<open>top1_scheme_equiv scheme (prefix @ suffix)\<close>
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          \<comment> \<open>The result has labels a\\_lab and fst(hd(prefix@suffix)), both with opposite directions.
             By flip\\_label and relabel if needed: ~ sphere form.\<close>
          \<comment> \<open>Rotate [(a\\_lab,T),(a\\_lab,F)] to front, then flip\\_label for sphere form.\<close>
          moreover have "top1_scheme_equiv (prefix @ [(a_lab,True),(a_lab,False)] @ suffix)
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)"
            unfolding top1_scheme_equiv_def
            using top1_elementary_scheme_operation.rotate[of prefix "[(a_lab,True),(a_lab,False)] @ suffix"]
            by (simp add: rtranclp.rtrancl_into_rtrancl)
          ultimately have hchain: "top1_scheme_equiv scheme
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)"
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          \<comment> \<open>suffix@prefix has length 2, same label, opposite directions. ~ sphere form.\<close>
          \<comment> \<open>suffix@prefix has length 2 with same label, opposite directions.
             Take a=a\\_lab, b=fst(hd(suffix@prefix)).\<close>
          \<comment> \<open>suffix@prefix has exactly 2 elements (from hlen\\_ps).\<close>
          obtain e1 e2 where hsp_list: "suffix @ prefix = [e1, e2]"
          proof -
            have "length (suffix @ prefix) = 2" using hlen_ps by simp
            then obtain e1 rest where "suffix @ prefix = e1 # rest" by (cases "suffix @ prefix") simp_all
            moreover then obtain e2 where "rest = [e2]" using \<open>length (suffix @ prefix) = 2\<close> by (cases rest) simp_all
            ultimately show ?thesis using that by simp
          qed
          \<comment> \<open>The elements e1, e2 are from the original scheme (minus the cancel pair).
             They must have the same label and opposite directions.\<close>
          have he_in: "e1 \<in> set scheme \<and> e2 \<in> set scheme"
          proof -
            from hsp_list have "e1 \<in> set (suffix @ prefix)" by (by100 simp)
            hence "e1 \<in> set suffix \<or> e1 \<in> set prefix" by (by100 simp)
            moreover have hpf_sub: "set prefix \<subseteq> set scheme"
            proof (rule subsetI)
              fix x assume "x \<in> set prefix"
              hence "x \<in> set (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)"
                by (by100 simp)
              thus "x \<in> set scheme" using hdecomp by (by100 simp)
            qed
            moreover have hsf_sub: "set suffix \<subseteq> set scheme"
            proof (rule subsetI)
              fix x assume "x \<in> set suffix"
              hence "x \<in> set (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)"
                by (by100 simp)
              thus "x \<in> set scheme" using hdecomp by (by100 simp)
            qed
            ultimately have "e1 \<in> set scheme" by (by100 blast)
            moreover have "e2 \<in> set scheme"
            proof -
              from hsp_list have "e2 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e2 \<in> set suffix \<or> e2 \<in> set prefix" by (by100 simp)
              thus ?thesis using \<open>set prefix \<subseteq> set scheme\<close> \<open>set suffix \<subseteq> set scheme\<close> by (by100 blast)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          have he_ne_label: "fst e1 \<noteq> fst (scheme!i) \<and> fst e2 \<noteq> fst (scheme!i)"
          proof -
            let ?lab = "fst (scheme!i)"
            have hlab_card: "card {j. j < 4 \<and> fst (scheme ! j) = ?lab} = 2"
            proof -
              from less(3) have "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} \<in> {0, 2}"
                by (by100 blast)
              moreover have "i \<in> {j. j < length scheme \<and> fst (scheme ! j) = ?lab}"
                using hi(1) \<open>length scheme = 4\<close> by (by100 simp)
              hence "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} \<noteq> 0"
                by (by100 auto)
              ultimately have "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} = 2"
                by (by100 blast)
              thus ?thesis using \<open>length scheme = 4\<close> by (by100 simp)
            qed
            have hlab_only: "\<forall>k < 4. fst (scheme ! k) = ?lab \<longrightarrow> k = i \<or> k = i + 1"
            proof (intro allI impI)
              fix k assume hk: "k < 4" "fst (scheme ! k) = ?lab"
              show "k = i \<or> k = i + 1"
              proof (rule ccontr)
                assume "\<not> (k = i \<or> k = i + 1)"
                hence hk_ne: "k \<noteq> i" "k \<noteq> i + 1" by (by100 blast)+
                have "{i, i+1, k} \<subseteq> {j. j < 4 \<and> fst (scheme ! j) = ?lab}"
                  using hi(1) hk \<open>length scheme = 4\<close> hi(2) by (by100 auto)
                moreover have "card {i, i+1, k} = 3"
                  using hk_ne by (by100 auto)
                moreover have "finite {j. j < 4 \<and> fst (scheme ! j) = ?lab}" by (by100 simp)
                ultimately have "card {j. j < 4 \<and> fst (scheme ! j) = ?lab} \<ge> 3"
                  by (metis card_mono le_antisym not_less_eq_eq)
                thus False using hlab_card by (by100 simp)
              qed
            qed
            \<comment> \<open>e1 from prefix or suffix: position \<noteq> i, \<noteq> i+1.\<close>
            \<comment> \<open>Elements of prefix are at positions < i in scheme.\<close>
            \<comment> \<open>Elements at positions < i in scheme have label \<noteq> ?lab.\<close>
            have hpos_ne: "\<forall>k. k < length prefix \<longrightarrow> fst (scheme ! k) \<noteq> ?lab"
            proof (intro allI impI)
              fix k assume "k < length prefix"
              hence "k < i" using hlen_pf by (by100 simp)
              hence "k < 4" using hi(1) \<open>length scheme = 4\<close> by (by100 auto)
              moreover have "k \<noteq> i" using \<open>k < i\<close> by (by100 simp)
              moreover have "k \<noteq> i + 1" using \<open>k < i\<close> by (by100 simp)
              ultimately show "fst (scheme ! k) \<noteq> ?lab" using hlab_only by (by100 blast)
            qed
            have hpf_ne: "\<forall>x \<in> set prefix. fst x \<noteq> ?lab"
            proof (rule ballI)
              fix x assume hx_pf: "x \<in> set prefix"
              hence "\<exists>k. k < length prefix \<and> prefix ! k = x"
                by (simp add: in_set_conv_nth)
              then obtain k where hk: "k < length prefix" "prefix ! k = x"
                by (by100 blast)
              have "k < i" using hk(1) hlen_pf by (by100 simp)
              have hsk: "scheme ! k = x"
              proof -
                have hk': "k < length prefix" using hk(1) .
                have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k = prefix ! k"
                  using nth_append[of prefix _ k] hk' by (by100 simp)
                thus ?thesis using hdecomp hk(2) by (by100 simp)
              qed
              have "k < 4" using \<open>k < i\<close> hi(1) \<open>length scheme = 4\<close> by (by100 auto)
              moreover have "k \<noteq> i" using \<open>k < i\<close> by (by100 simp)
              moreover have "k \<noteq> i + 1" using \<open>k < i\<close> by (by100 simp)
              ultimately have "fst (scheme ! k) \<noteq> ?lab" using hlab_only by (by100 blast)
              thus "fst x \<noteq> ?lab" using hsk by (by100 simp)
            qed
            have hsf_ne: "\<forall>x \<in> set suffix. fst x \<noteq> ?lab"
            proof (rule ballI)
              fix x assume hx_sf: "x \<in> set suffix"
              hence "\<exists>k. k < length suffix \<and> suffix ! k = x"
                by (simp add: in_set_conv_nth)
              then obtain k where hk: "k < length suffix" "suffix ! k = x"
                by (by100 blast)
              define k' where "k' = i + 2 + k"
              have hsk: "scheme ! k' = x"
              proof -
                have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k' = suffix ! k"
                proof -
                  have "k' = length prefix + 2 + k" using hlen_pf unfolding k'_def by (by100 simp)
                  have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k'
                      = ([scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! (k' - length prefix)"
                    using nth_append[of prefix _ k'] \<open>k' = length prefix + 2 + k\<close> by (by100 simp)
                  also have "k' - length prefix = 2 + k" using \<open>k' = length prefix + 2 + k\<close> by (by100 simp)
                  also have "([scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! (2 + k) = suffix ! k"
                    using hk(1) by (by100 simp)
                  finally show ?thesis .
                qed
                thus ?thesis using hdecomp hk(2) by (by100 simp)
              qed
              have "k' < 4" using hk(1) hlen_pf hlen_ps unfolding k'_def by (by100 auto)
              moreover have "k' \<noteq> i" unfolding k'_def by (by100 simp)
              moreover have "k' \<noteq> i + 1" unfolding k'_def by (by100 simp)
              ultimately have "fst (scheme ! k') \<noteq> ?lab" using hlab_only by (by100 blast)
              thus "fst x \<noteq> ?lab" using hsk by (by100 simp)
            qed
            have "fst e1 \<noteq> ?lab \<and> fst e2 \<noteq> ?lab"
            proof -
              from hsp_list have "e1 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e1 \<in> set suffix \<or> e1 \<in> set prefix" by (by100 simp)
              hence "fst e1 \<noteq> ?lab" using hpf_ne hsf_ne by (by100 blast)
              moreover from hsp_list have "e2 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e2 \<in> set suffix \<or> e2 \<in> set prefix" by (by100 simp)
              hence "fst e2 \<noteq> ?lab" using hpf_ne hsf_ne by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            thus ?thesis by (by100 simp)
          qed
          have "fst e1 = fst e2"
          proof -
            \<comment> \<open>Since length scheme = 4, there are exactly 4 positions.
               Positions i and i+1 have label fst(scheme!i).
               The other 2 positions have elements e1 and e2 (from prefix/suffix).
               By properness: fst(e1) appears 0 or 2 times. At least once (e1). So 2 times.
               Those 2 times can't include i or i+1 (different label, by he\_ne\_label).
               The other 2 positions have fst = fst(e1). Since e2 is at one of those: fst(e1) = fst(e2).\<close>
            \<comment> \<open>Direct argument: scheme has 4 elements. 2 have label fst(scheme!i).
               e1, e2 are the other 2. If fst(e1) \<noteq> fst(e2), then fst(e1) appears only once
               (at e1's position). But properness requires 0 or 2 occurrences. Contradiction.\<close>
            show ?thesis
            proof (rule ccontr)
              assume hne: "fst e1 \<noteq> fst e2"
              \<comment> \<open>fst(e1) appears at e1's position and no other.\<close>
              \<comment> \<open>e1's position: some k1 with scheme!k1 = e1.
                 e2's position: some k2 with scheme!k2 = e2, fst(e2) \<noteq> fst(e1).
                 i and i+1: label = fst(scheme!i) \<noteq> fst(e1).
                 So fst(e1) appears exactly 1 time, contradicting properness.\<close>
              from he_in have "e1 \<in> set scheme" by (by100 blast)
              hence "\<exists>k1. k1 < length scheme \<and> scheme ! k1 = e1"
                by (simp add: in_set_conv_nth)
              then obtain k1 where hk1: "k1 < length scheme" "scheme ! k1 = e1" by (by100 blast)
              have "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} \<in> {0, 2}"
                using less(3) by (by100 blast)
              moreover have "k1 \<in> {j. j < length scheme \<and> fst (scheme ! j) = fst e1}"
                using hk1 by (by100 simp)
              hence "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} \<noteq> 0"
                by (by100 auto)
              ultimately have hcard_e1: "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} = 2"
                by (by100 blast)
              \<comment> \<open>Positions with label fst(e1): exactly 2. Can't include i or i+1.\<close>
              \<comment> \<open>The 2 positions must be among {0,1,2,3} - {i, i+1} which has 2 elements.\<close>
              \<comment> \<open>These 2 positions correspond to e1 and e2's positions.
                 But fst(e2) \<noteq> fst(e1) means e2's position is NOT among them.
                 So only 1 position has label fst(e1): k1. Card = 1 \<noteq> 2. Contradiction.\<close>
              have hcard1: "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} = 2"
                using hcard_e1 \<open>length scheme = 4\<close> by (by100 simp)
              \<comment> \<open>Count: positions i, i+1 have different label. e2's position has different label.
                 So at most 1 position (e1's) has label fst(e1).\<close>
              \<comment> \<open>But card = 2 means at least 2 positions. Contradiction if only k1 has it.\<close>
              \<comment> \<open>Get k2, show the set \<subseteq> {k1} using label contradictions + presburger, then card \<le> 1.\<close>
              from he_in have "e2 \<in> set scheme" by (by100 blast)
              hence "\<exists>k2. k2 < length scheme \<and> scheme ! k2 = e2" by (simp add: in_set_conv_nth)
              then obtain k2 where hk2: "k2 < length scheme" "scheme ! k2 = e2" by (by100 blast)
              have hset_sub: "{j. j < 4 \<and> fst (scheme ! j) = fst e1} \<subseteq> {k1}"
              proof (rule subsetI)
                fix j assume hj_in: "j \<in> {j. j < 4 \<and> fst (scheme ! j) = fst e1}"
                hence hj: "j < 4" "fst (scheme ! j) = fst e1" by (by100 simp)+
                have hjni: "j \<noteq> i"
                proof assume "j = i"
                  hence "fst e1 = fst (scheme ! i)" using hj(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hjni1: "j \<noteq> i + 1"
                proof assume "j = i + 1"
                  hence "fst e1 = fst (scheme ! (i+1))" using hj(2) by (by100 simp)
                  hence "fst e1 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hjnk2: "j \<noteq> k2"
                proof assume "j = k2"
                  hence "fst e1 = fst e2" using hj(2) hk2(2) by (by100 simp)
                  thus False using hne by (by100 simp)
                qed
                have hk2ni: "k2 \<noteq> i"
                proof assume "k2 = i"
                  hence "fst e2 = fst (scheme ! i)" using hk2(2) by (by100 simp)
                  moreover from he_ne_label have "fst e2 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk2ni1: "k2 \<noteq> i + 1"
                proof assume "k2 = i + 1"
                  hence "fst e2 = fst (scheme ! (i+1))" using hk2(2) by (by100 simp)
                  hence "fst e2 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e2 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1ni: "k1 \<noteq> i"
                proof assume "k1 = i"
                  hence "fst e1 = fst (scheme ! i)" using hk1(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1ni1: "k1 \<noteq> i + 1"
                proof assume "k1 = i + 1"
                  hence "fst e1 = fst (scheme ! (i+1))" using hk1(2) by (by100 simp)
                  hence "fst e1 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1nk2: "k1 \<noteq> k2"
                proof assume "k1 = k2"
                  hence "fst e1 = fst e2" using hk1(2) hk2(2) by (by100 simp)
                  thus False using hne by (by100 simp)
                qed
                have "i < 3" using hi(1) by (by100 simp)
                have "k2 < 4" using hk2(1) \<open>length scheme = 4\<close> by (by100 simp)
                have "k1 < 4" using hk1(1) \<open>length scheme = 4\<close> by (by100 simp)
                from hj(1) \<open>k1 < 4\<close> \<open>k2 < 4\<close> \<open>i < 3\<close>
                    hjni hjni1 hjnk2 hk1ni hk1ni1 hk1nk2 hk2ni hk2ni1
                have "j = k1" by (by100 presburger)
                thus "j \<in> {k1}" by (by100 simp)
              qed
              have "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> card {k1}"
                by (rule card_mono) (by100 simp, rule hset_sub)
              hence "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> 1" by (by100 simp)
              show False using hcard1 \<open>card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> 1\<close>
                by (by100 simp)
            qed
          qed
          have "snd e1 \<noteq> snd e2"
            using proper_len4_torus_pair_props[OF \<open>length scheme = 4\<close> less(3)]
            using \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
                i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
                \<and> snd (scheme ! i) = snd (scheme ! j))\<close>
            using \<open>fst e1 = fst e2\<close> he_in he_ne_label hi
            by (by100 blast)
          define b_lab where "b_lab = fst e1"
          define d_b where "d_b = snd e1"
          have hsp: "suffix @ prefix = [(b_lab, d_b), (b_lab, \<not>d_b)]"
            using hsp_list \<open>fst e1 = fst e2\<close> \<open>snd e1 \<noteq> snd e2\<close>
            unfolding b_lab_def d_b_def by (cases e1, cases e2) simp
          have hab_ne: "a_lab \<noteq> b_lab"
          proof -
            have "hd (prefix @ suffix) \<in> set (prefix @ suffix)"
            proof -
              have "prefix @ suffix \<noteq> []"
              proof
                assume "prefix @ suffix = []"
                hence "length (prefix @ suffix) = 0" by (by100 simp)
                hence "length prefix + length suffix = 0" by (by100 simp)
                thus False using hlen_ps by (by100 simp)
              qed
              hence "hd (prefix @ suffix) \<in> set (prefix @ suffix)"
                using list.set_sel(1) by (by100 blast)
              thus ?thesis .
            qed
            hence "hd (prefix @ suffix) \<in> set prefix \<union> set suffix" by (by100 simp)
            hence "hd (prefix @ suffix) \<in> set suffix \<union> set prefix" by (by100 blast)
            hence "hd (prefix @ suffix) \<in> set (suffix @ prefix)" by (by100 simp)
            hence "hd (prefix @ suffix) \<in> set [e1, e2]" using hsp_list by (by100 simp)
            hence "hd (prefix @ suffix) = e1 \<or> hd (prefix @ suffix) = e2" by (by100 simp)
            hence "fst (hd (prefix @ suffix)) = fst e1"
              using \<open>fst e1 = fst e2\<close>
            proof (elim disjE)
              assume "hd (prefix @ suffix) = e1" thus ?thesis by (by100 simp)
            next
              assume "hd (prefix @ suffix) = e2" thus ?thesis using \<open>fst e1 = fst e2\<close> by (by100 simp)
            qed
            hence "a_lab \<noteq> fst e1" using ha by (by100 simp)
            thus ?thesis unfolding b_lab_def by (by100 simp)
          qed
          obtain b_lab d_b where
              hsp: "suffix @ prefix = [(b_lab, d_b), (b_lab, \<not>d_b)]" and
              hab_ne: "a_lab \<noteq> b_lab"
            using hsp hab_ne by (by100 blast)
          \<comment> \<open>Now [(a\\_lab,T),(a\\_lab,F)] @ [(b\\_lab,d\\_b),(b\\_lab,\\<not>d\\_b)] ~ sphere form.\<close>
          have "top1_scheme_equiv
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)
              ([(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)])"
          proof -
            show ?thesis
            proof (cases d_b)
              case True
              hence "suffix @ prefix = [(b_lab, True), (b_lab, False)]" using hsp by simp
              thus ?thesis unfolding top1_scheme_equiv_def by simp
            next
              case False
              hence "suffix @ prefix = [(b_lab, False), (b_lab, True)]" using hsp by simp
              hence target_eq: "[(a_lab,True),(a_lab,False)] @ suffix @ prefix
                  = [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]" by simp
              have hflip_result: "map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo))
                  [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                  = [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
                using hab_ne by simp
              have "top1_elementary_scheme_operation
                  [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                  [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
              proof -
                have "top1_elementary_scheme_operation
                    [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                    (map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo))
                         [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)])"
                  by (rule top1_elementary_scheme_operation.flip_label)
                thus ?thesis unfolding hflip_result .
              qed
              thus ?thesis unfolding target_eq top1_scheme_equiv_def by simp
            qed
          qed
          hence "top1_scheme_equiv scheme [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
            using hchain unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          thus ?thesis using hab_ne by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      next
        case no_adj: False
        \<comment> \<open>No adjacent same-label \\<Rightarrow> labels alternate.
           scheme = [(a,d1),(b,d2),(a,d3),(b,d4)] where a \\<noteq> b, d1\\<noteq>d3, d2\\<noteq>d4.
           After rotate + flip\\_label + relabel: equivalent to torus n=1.\<close>
        \<comment> \<open>With length 4, 2 labels, alternating: scheme ~ torus n=1.
           This uses: the scheme is equivalent to [(a,T),(b,T),(a,F),(b,F)]
           via at most rotate + flip\\_label + relabel.\<close>
        have "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w"
        proof -
          \<comment> \<open>The scheme has length 4, 2 distinct labels, alternating, opposite directions.
             After flip\\_label and relabel: [(0,T),(1,T),(0,F),(1,F)] = torus n=1.\<close>
          \<comment> \<open>Extract the 4 elements.\<close>
          obtain s0 s1 s2 s3 where hsch4: "scheme = [s0, s1, s2, s3]"
            using \<open>length scheme = 4\<close> by (cases scheme; simp; cases "tl scheme"; simp;
              cases "tl (tl scheme)"; simp; cases "tl (tl (tl scheme))"; simp)
          \<comment> \<open>Properties: alternating labels, opposite directions.\<close>
          have "fst s0 \<noteq> fst s1"
          proof -
            from no_adj have "\<not> (fst (scheme!0) = fst (scheme!1))" by (by100 auto)
            thus ?thesis using hsch4 by simp
          qed
          have "fst s0 = fst s2"
          proof (rule ccontr)
            assume "fst s0 \<noteq> fst s2"
            \<comment> \<open>fst s0 appears at position 0 but not 1, 2. In proper scheme with 2 occurrences,
               it must be at position 3. Then fst s2 = fst s1 (only other label).
               But positions 1,2 are adjacent with same label \\<Rightarrow> contradicts no\\_adj.\<close>
            \<comment> \<open>First show fst s3 = fst s0 (from properness of fst s0).\<close>
            \<comment> \<open>Properness of fst s0: appears at exactly 2 positions.\<close>
            have hcard_s0: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 0
                \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2"
              using less.prems(2)[THEN spec, of "fst s0"] by (by100 blast)
            have "0 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
              using hsch4 \<open>length scheme = 4\<close> by simp
            hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<noteq> 0" by (by100 auto)
            hence hcard_s0_2: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2"
              using hcard_s0 by linarith
            \<comment> \<open>Positions with label fst s0: subset of {0,3} (not 1 by \\<noteq>fst s1, not 2 by assumption).\<close>
            have hsub_03: "{i. i < length scheme \<and> fst (scheme!i) = fst s0} \<subseteq> {0, 3}"
            proof
              fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
              hence hj: "j < 4" "fst (scheme!j) = fst s0" using \<open>length scheme = 4\<close> by auto
              have "j \<noteq> 1"
              proof assume "j = 1" hence "fst s1 = fst s0" using hj(2) hsch4 by simp
                with \<open>fst s0 \<noteq> fst s1\<close> show False by simp qed
              moreover have "j \<noteq> 2"
              proof assume "j = 2" hence "fst s2 = fst s0" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
              ultimately show "j \<in> {0, 3}" using hj(1) by (simp add: eval_nat_numeral) linarith
            qed
            \<comment> \<open>Card 2 subset of {0,3} with card {0,3} = 2 means equality.\<close>
            have "card {0::nat, 3} = 2" by simp
            hence "{i. i < length scheme \<and> fst (scheme!i) = fst s0} = {0, 3}"
              using hsub_03 hcard_s0_2 card_subset_eq[of "{0::nat, 3}"] by simp
            hence "3 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}" by simp
            hence "fst s3 = fst s0" using hsch4 by (simp add: eval_nat_numeral)
            \<comment> \<open>Then fst s2 = fst s1: fst s2 \\<noteq> fst s0 (assumption) and fst s2 \\<noteq> fst s3 = fst s0.
               Properness of fst s2: appears at 2 positions. Not at 0 (fst s0) or 3 (fst s0).
               So only at 1 and 2. Hence fst(scheme!1) = fst s2, i.e., fst s1 = fst s2.\<close>
            have "fst s2 = fst s1"
            proof -
              have hcard_s2: "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 0
                  \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 2"
                using less.prems(2)[THEN spec, of "fst s2"] by (by100 blast)
              have "2 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}"
                using hsch4 \<open>length scheme = 4\<close> by (simp add: eval_nat_numeral)
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} \<noteq> 0" by (by100 auto)
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 2"
                using hcard_s2 by linarith
              moreover have "{i. i < length scheme \<and> fst (scheme!i) = fst s2} \<subseteq> {1, 2}"
              proof
                fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}"
                hence hj: "j < 4" "fst (scheme!j) = fst s2" using \<open>length scheme = 4\<close> by auto
                have "j \<noteq> 0"
                proof assume "j = 0" hence "fst s2 = fst s0" using hj(2) hsch4 by simp
                  with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
                moreover have "j \<noteq> 3"
                proof assume "j = 3" hence "fst s2 = fst s3" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                  hence "fst s2 = fst s0" using \<open>fst s3 = fst s0\<close> by simp
                  with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
                ultimately show "j \<in> {1, 2}" using hj(1) by (simp add: eval_nat_numeral) linarith
              qed
              ultimately have "{i. i < length scheme \<and> fst (scheme!i) = fst s2} = {1, 2}"
                using card_subset_eq[of "{1::nat, 2}"] by simp
              hence "1 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}" by simp
              thus "fst s2 = fst s1" using hsch4 by simp
            qed
            hence "fst (scheme!1) = fst (scheme!2)" using hsch4 by simp
            have h12: "\<not> (fst (scheme!1) = fst (scheme!(Suc 1)))"
              using no_adj by (by5000 force)
            have "\<not> (fst (scheme!1) = fst (scheme!2))" using h12 by (simp add: numeral_2_eq_2)
            thus False using \<open>fst (scheme!1) = fst (scheme!2)\<close> by simp
          qed
          have "fst s1 = fst s3"
          proof (rule ccontr)
            assume "fst s1 \<noteq> fst s3"
            \<comment> \<open>fst s3 \\<noteq> fst s1 and fst s3 \\<noteq> fst s0 (otherwise fst s0 appears at 0,2,3 = 3 times).
               So fst s3 is a 3rd label. But scheme has only 2 labels (proper, length 4).
               Contradiction: fst s3 appears only at position 3, card = 1.\<close>
            have hproper_s0: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<in> {0, 2}"
            proof -
              from less.prems(2) have "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}" .
              thus ?thesis by (by100 blast)
            qed
            have "fst s3 \<noteq> fst s0"
            proof
              assume "fst s3 = fst s0"
              have "{0::nat, 2, 3} \<subseteq> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
                using hsch4 \<open>length scheme = 4\<close> \<open>fst s0 = fst s2\<close> \<open>fst s3 = fst s0\<close>
                by (simp add: eval_nat_numeral)
              hence "card {0::nat, 2, 3} \<le> card {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
                by (intro card_mono) simp
              hence "3 \<le> card {i. i < length scheme \<and> fst (scheme!i) = fst s0}" by simp
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<ge> 3" by simp
              moreover from hproper_s0 have "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 0
                  \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2" by (by100 blast)
              ultimately show False by linarith
            qed
            \<comment> \<open>Now fst s3 \\<noteq> fst s0 and fst s3 \\<noteq> fst s1. So fst s3 appears only at position 3.
               card = 1, but proper says {0, 2}. Contradiction.\<close>
            have "{i. i < length scheme \<and> fst (scheme!i) = fst s3} = {3}"
            proof
              show "{i. i < length scheme \<and> fst (scheme!i) = fst s3} \<subseteq> {3}"
              proof
                fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s3}"
                hence hj: "j < 4" "fst (scheme!j) = fst s3" using \<open>length scheme = 4\<close> by auto
                show "j \<in> {3}"
                proof -
                  have "j \<in> {0,1,2,3}" using hj(1) by (simp add: eval_nat_numeral, by100 auto)
                  moreover have "j = 0 \<Longrightarrow> fst s3 = fst s0" using hj(2) hsch4 by simp
                  moreover have "j = 1 \<Longrightarrow> fst s3 = fst s1" using hj(2) hsch4 by simp
                  moreover have "j = 2 \<Longrightarrow> fst s3 = fst s2" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                  ultimately show "j \<in> {3}" using \<open>fst s3 \<noteq> fst s0\<close> \<open>fst s1 \<noteq> fst s3\<close> \<open>fst s0 = fst s2\<close>
                    by (simp add: eval_nat_numeral, by100 auto)
                qed
              qed
            next
              show "{3} \<subseteq> {i. i < length scheme \<and> fst (scheme!i) = fst s3}"
                using hsch4 \<open>length scheme = 4\<close> by (simp add: eval_nat_numeral)
            qed
            hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s3} = 1" by simp
            moreover have "card {i. i < length scheme \<and> fst (scheme!i) = fst s3} \<in> {0, 2}"
              using less.prems(2) by simp
            ultimately show False by simp
          qed
          have htorus: "\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))"
            by (rule \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))\<close>)
          have "snd s0 \<noteq> snd s2"
          proof
            assume "snd s0 = snd s2"
            have "(0::nat) < length scheme" "2 < length scheme" "(0::nat) \<noteq> 2"
                "fst (scheme!0) = fst s0" "fst (scheme!2) = fst s0"
                "snd (scheme!0) = snd (scheme!2)"
              using \<open>length scheme = 4\<close> hsch4 \<open>fst s0 = fst s2\<close> \<open>snd s0 = snd s2\<close>
              by (simp_all add: eval_nat_numeral)
            hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
              by (intro exI[of _ "fst s0"] exI[of _ 0] exI[of _ 2]) (by100 blast)
            with htorus show False by simp
          qed
          have "snd s1 \<noteq> snd s3"
          proof
            assume "snd s1 = snd s3"
            have "(1::nat) < length scheme" "3 < length scheme" "(1::nat) \<noteq> 3"
                "fst (scheme!1) = fst s1" "fst (scheme!3) = fst s1"
                "snd (scheme!1) = snd (scheme!3)"
              using \<open>length scheme = 4\<close> hsch4 \<open>fst s1 = fst s3\<close> \<open>snd s1 = snd s3\<close>
              by (simp_all add: eval_nat_numeral)
            hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
              by (intro exI[of _ "fst s1"] exI[of _ 1] exI[of _ 3]) (by100 blast)
            with htorus show False by simp
          qed
          \<comment> \<open>After flip\\_label: scheme ~ [(fst s0,T),(fst s1,T),(fst s0,F),(fst s1,F)].
             This is a torus scheme of type n=1 (with labels fst s0, fst s1).
             Then relabel to standard labels gives top1\\_n\\_torus\\_scheme 1.\<close>
          \<comment> \<open>Construct equivalence: scheme ~ flip\\_label(s) ~ relabel ~ torus n=1.\<close>
          \<comment> \<open>The scheme is [(fst s0,d0),(fst s1,d1),(fst s0,\\<not>d0),(fst s1,\\<not>d1)] where d0=snd s0, d1=snd s1.\<close>
          \<comment> \<open>After at most 2 flip\\_labels and 2 relabels: ~ [(0,T),(1,T),(0,F),(1,F)] = torus n=1.\<close>
          \<comment> \<open>Step 1: flip\\_label if needed to standardize snd to True at positions 0,1.\<close>
          define scheme1 where "scheme1 = (if snd s0 then scheme else
              map (\<lambda>(l,b). (l, if l = fst s0 then \<not>b else b)) scheme)"
          have hequiv1: "top1_scheme_equiv scheme scheme1"
            unfolding scheme1_def top1_scheme_equiv_def
            using top1_elementary_scheme_operation.flip_label[of scheme "fst s0"]
            by (cases "snd s0") simp_all
          define scheme2 where "scheme2 = (if snd s1 then scheme1 else
              map (\<lambda>(l,b). (l, if l = fst s1 then \<not>b else b)) scheme1)"
          have hequiv2: "top1_scheme_equiv scheme1 scheme2"
            unfolding scheme2_def top1_scheme_equiv_def
            using top1_elementary_scheme_operation.flip_label[of scheme1 "fst s1"]
            by (cases "snd s1") simp_all
          \<comment> \<open>After flips: scheme2 = [(fst s0,T),(fst s1,T),(fst s0,F),(fst s1,F)].\<close>
          have hsch2: "scheme2 = [(fst s0,True),(fst s1,True),(fst s0,False),(fst s1,False)]"
          proof -
            \<comment> \<open>After flip1: scheme1 has snd at position 0 = True.\<close>
            have "s2 = (fst s0, \<not> snd s0)" using \<open>fst s0 = fst s2\<close> \<open>snd s0 \<noteq> snd s2\<close>
              by (cases s2) simp
            have "s3 = (fst s1, \<not> snd s1)" using \<open>fst s1 = fst s3\<close> \<open>snd s1 \<noteq> snd s3\<close>
              by (cases s3) simp
            have hsch_exp: "scheme = [(fst s0, snd s0), (fst s1, snd s1), (fst s0, \<not>snd s0), (fst s1, \<not>snd s1)]"
              using hsch4 \<open>s2 = (fst s0, \<not> snd s0)\<close> \<open>s3 = (fst s1, \<not> snd s1)\<close>
              by (cases s0, cases s1) simp
            show ?thesis
              unfolding scheme2_def scheme1_def hsch_exp
              using \<open>fst s0 \<noteq> fst s1\<close> by (cases "snd s0"; cases "snd s1") simp_all
          qed
          \<comment> \<open>Step 2: relabel to standard labels 0, 1 via elementary relabel operations.\<close>
          have "top1_scheme_equiv scheme2 (top1_n_torus_scheme 1)"
          proof (cases "fst s1 = (0::nat)")
            case False
            \<comment> \<open>fst s1 \\<noteq> 0: relabel fst s0\\<to>0, then fst s1\\<to>1 (no collision).\<close>
            have h_r1: "top1_scheme_equiv scheme2
                (map (\<lambda>(l,b). (if l = fst s0 then 0 else l, b)) scheme2)"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel[of scheme2 "fst s0" 0] by simp
            have h_mid: "map (\<lambda>(l,b). (if l = fst s0 then 0 else l, b)) scheme2
                = [(0,True),(fst s1,True),(0,False),(fst s1,False)]"
              unfolding hsch2 using \<open>fst s0 \<noteq> fst s1\<close> by simp
            have h_r2: "top1_scheme_equiv [(0,True),(fst s1,True),(0,False),(fst s1,False)]
                (map (\<lambda>(l,b). (if l = fst s1 then 1 else l, b)) [(0,True),(fst s1,True),(0,False),(fst s1,False)])"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel
                [of "[(0,True),(fst s1,True),(0,False),(fst s1,False)]" "fst s1" 1] by simp
            have h_final: "map (\<lambda>(l,b). (if l = fst s1 then 1 else l, b)) [(0,True),(fst s1,True),(0,False),(fst s1,False)]
                = top1_n_torus_scheme 1"
              unfolding top1_n_torus_scheme_def using False by simp
            from h_r1 have "top1_scheme_equiv scheme2 [(0,True),(fst s1,True),(0,False),(fst s1,False)]"
              unfolding top1_scheme_equiv_def h_mid by simp
            moreover from h_r2 have "top1_scheme_equiv [(0,True),(fst s1,True),(0,False),(fst s1,False)] (top1_n_torus_scheme 1)"
              unfolding top1_scheme_equiv_def h_final by simp
            ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          next
            case True
            \<comment> \<open>fst s1 = 0: use 3-step relabel via intermediate label (fst s0 + 1).\<close>
            hence "fst s0 \<noteq> 0" using \<open>fst s0 \<noteq> fst s1\<close> by simp
            define fr where "fr = fst s0 + 1"
            have hfr: "fr \<noteq> fst s0" "fr \<noteq> fst s1" "fr \<noteq> 0" "fr \<noteq> 1"
              unfolding fr_def using True \<open>fst s0 \<noteq> 0\<close> by simp_all
            \<comment> \<open>relabel fst s0\\<to>fr, then fst s1=0\\<to>1, then fr\\<to>0.\<close>
            \<comment> \<open>scheme2 = [(fst s0,T),(0,T),(fst s0,F),(0,F)]. relabel fst s0\\<to>1:\\<close>
            have h_r1: "top1_scheme_equiv scheme2
                (map (\<lambda>(l,b). (if l = fst s0 then 1 else l, b)) scheme2)"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel[of scheme2 "fst s0" 1] by simp
            have h_mid: "map (\<lambda>(l,b). (if l = fst s0 then 1 else l, b)) scheme2
                = [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]"
              unfolding hsch2 using \<open>fst s0 \<noteq> fst s1\<close> True by (simp add: eval_nat_numeral)
            \<comment> \<open>[(1,T),(0,T),(1,F),(0,F)] ~ rotate ~ flip\\_label 1 ~ target.\<close>
            have h_rot: "top1_elementary_scheme_operation
                [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]
                [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]"
              using top1_elementary_scheme_operation.rotate[of "[(Suc 0,True)]" "[(0,True),(Suc 0,False),(0,False)]"]
              by simp
            have h_flip: "top1_elementary_scheme_operation
                [(0::nat,True),(Suc 0,False),(0,False),(Suc 0,True)]
                (map (\<lambda>(l,b). (l, if l = Suc 0 then \<not>b else b)) [(0,True),(Suc 0,False),(0,False),(Suc 0,True)])"
              by (rule top1_elementary_scheme_operation.flip_label)
            have h_flip_simp: "map (\<lambda>(l,b). (l, if l = Suc (0::nat) then \<not>b else b)) [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]
                = [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              by simp
            have "[(0::nat,True),(Suc 0,True),(0,False),(Suc 0,False)] = top1_n_torus_scheme 1"
              unfolding top1_n_torus_scheme_def by (simp add: eval_nat_numeral)
            from h_r1 h_mid have s2_mid: "top1_scheme_equiv scheme2 [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]"
              unfolding top1_scheme_equiv_def by simp
            from s2_mid h_rot have s2_rot: "top1_scheme_equiv scheme2 [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]"
              unfolding top1_scheme_equiv_def by (meson rtranclp.rtrancl_into_rtrancl)
            from h_flip have "top1_elementary_scheme_operation
                [(0::nat,True),(Suc 0,False),(0,False),(Suc 0,True)]
                [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              using h_flip_simp by simp
            with s2_rot have "top1_scheme_equiv scheme2 [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              unfolding top1_scheme_equiv_def by (meson rtranclp.rtrancl_into_rtrancl)
            thus ?thesis using \<open>[(0::nat,True),(Suc 0,True),(0,False),(Suc 0,False)] = top1_n_torus_scheme 1\<close>
              by simp
          qed
          have "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w"
          proof -
            have "top1_scheme_equiv scheme (top1_n_torus_scheme 1)"
              using hequiv1 hequiv2 \<open>top1_scheme_equiv scheme2 (top1_n_torus_scheme 1)\<close>
              unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            thus ?thesis
              unfolding top1_is_torus_scheme_def by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
    next
      case False
      \<comment> \<open>Length > 4: either has cancellable adjacent pair (shorter scheme) or
         no adjacent same labels. Apply Lemma 77.3 to extract commutator.\<close>
      have hlen_gt4: "length scheme > 4" using less.prems(1) False by linarith
      \<comment> \<open>Book proof: check if scheme has adjacent cancellable pair.\<close>
      show ?thesis
      proof (cases "\<exists>i. i + 1 < length scheme \<and> fst (scheme!i) = fst (scheme!(i+1))
              \<and> snd (scheme!i) \<noteq> snd (scheme!(i+1))")
        case True
        \<comment> \<open>Adjacent inverse pair found: cancel to get shorter torus scheme.
           Apply IH to the shorter scheme.\<close>
        show ?thesis sorry
      next
        case no_adj_gt4: False
        \<comment> \<open>No adjacent inverse pairs. Book proof:
           1. Choose label a with closest opposite-direction occurrences.
           2. Find label b between them (exists because length > 4 and no adjacent same).
           3. By flip\\_label if needed, arrange as w0 a b w1 a\\<inverse> b\\<inverse> w2.
           4. Apply Lemma 77.3: ~ aba\\<inverse>b\\<inverse> w0 w1 w2.
           5. aba\\<inverse>b\\<inverse> w3 is a torus scheme with w3 shorter or equal length.
           6. Continue extracting commutators (or apply IH if w3 cancels).\<close>
        \<comment> \<open>Extract label a and positions of a, a\\<inverse>, label b between them.\<close>
        have "\<exists>a b w0 w1 w2. a \<noteq> b \<and>
            top1_scheme_equiv scheme
              (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)"
          sorry \<comment> \<open>Combinatorial: from torus-type proper scheme with no adjacent same-label
             and length > 4, extract the commutator pattern.\<close>
        then obtain a_lab b_lab w0' w1' w2' where hab: "a_lab \<noteq> b_lab"
            and hequiv: "top1_scheme_equiv scheme
              (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2')"
          by (by100 blast)
        \<comment> \<open>Apply Lemma 77.3.\<close>
        from Lemma_77_3_torus_extraction[OF hab, of w0' w1' w2']
        have "top1_scheme_equiv
            (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2')
            ([(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2')" .
        \<comment> \<open>Chain: scheme ~ pattern ~ aba\\<inverse>b\\<inverse> w3.\<close>
        hence "top1_scheme_equiv scheme
            ([(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2')"
          using hequiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        \<comment> \<open>The result aba\\<inverse>b\\<inverse> w3 is a torus scheme. If w3 is empty: done (torus n=1).
           If w3 nonempty: continue extracting commutators or apply IH.\<close>
        show ?thesis sorry
      qed
    qed
  qed
qed

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
  \<comment> \<open>Step 1: Extract edge scheme from the polygonal quotient.
     The polygon P has n edges. The quotient map q identifies boundary edges in pairs.
     For each pair of identified edges: assign a shared label. The direction (same or opposite)
     determines the exponent (True/False). This gives the edge scheme.
     The scheme satisfies quotient\\_of\\_scheme\\_on by construction.\<close>
  obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    sorry \<comment> \<open>Extract scheme from polygonal quotient. Construction:
       1. P has n vertices. Edge i goes from vertex i to vertex (i+1) mod n.
       2. q identifies edge i with some edge j (possibly reversed).
       3. Assign label k to both edges i and j. Direction: True if same, False if reversed.
       4. The resulting list of (label, direction) pairs is the scheme.
       5. Verify all conditions of quotient\\_of\\_scheme\\_on (P is the polygon, q is the map,
          vertex positions are the polygon's vertices).\<close>
  \<comment> \<open>Step 2: Apply elementary operations (Theorem 76) to reduce scheme.
     Operations: relabel, rotate, cancel, cut, paste, flip.
     Step 2a: Bring all vertices to one equivalence class.
     Step 2b: Collect pairs aa into adjacent positions (projective type).
     Step 2c: Pair remaining letters into commutator blocks aba\<inverse>b\<inverse> (torus type).\<close>
  \<comment> \<open>NOTE: top1\\_is\\_torus\\_scheme, top1\\_is\\_projective\\_scheme now defined (\\<S>77 section).
     top1\\_scheme\\_equiv = rtranclp of elementary operations (defined before \\<S>76).\<close>
  have hreduced: "(\<exists>n>0. \<exists>w. top1_is_torus_scheme w n
            \<and> top1_scheme_equiv scheme w)
      \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m
            \<and> top1_scheme_equiv scheme w)"
    sorry \<comment> \<open>From scheme\\_normal\\_form: scheme is proper (each label twice) and length \\<ge> 4.
       Properness follows from the polygonal quotient structure. Length \\<ge> 4 from surface.
       scheme\\_normal\\_form gives equivalence to torus or projective normal form.
       (Sphere case eliminated: length 0 contradicts quotient\\_of\\_scheme\\_on requiring n \\<ge> 3.)\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.
     - Empty/sphere: cancellation gives S² (a@a⁻¹@b@b⁻¹ with cancellation).
     - Torus scheme: the standard n-torus IS the quotient of this scheme
       (by definition top1\\_is\\_n\\_fold\\_torus\\_on). scheme\\_quotient\\_uniqueness gives homeo.
     - Projective scheme: similarly, top1\\_is\\_m\\_fold\\_projective\\_on.
     Plus: Theorem 76 preserves quotient homeomorphism type, so scheme\\_equiv gives homeo.\<close>
  \<comment> \<open>Identity homeomorphism on X (used in both torus and projective cases).\<close>
  have hX_top: "is_topology_on X TX" using hconn unfolding top1_connected_on_def by (by100 blast)
  have hid_homeo: "top1_homeomorphism_on X TX X TX id"
  proof -
    have hid_cont: "top1_continuous_map_on X TX X TX id"
      by (rule top1_continuous_map_on_id[OF hX_top])
    have "\<forall>x\<in>X. inv_into X id x = x"
    proof
      fix x assume "x \<in> X"
      have "inv_into X id (id x) = x" by (rule inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>])
      thus "inv_into X id x = x" by simp
    qed
    hence "top1_continuous_map_on X TX X TX (inv_into X id)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI allI impI)
      fix x assume hxX: "x \<in> X" thus "inv_into X id x \<in> X" using \<open>\<forall>x\<in>X. inv_into X id x = x\<close> by simp
    next
      fix V assume "V \<in> TX"
      have "{x \<in> X. inv_into X id x \<in> V} = {x \<in> X. id x \<in> V}"
      proof
        show "{x \<in> X. inv_into X id x \<in> V} \<subseteq> {x \<in> X. id x \<in> V}"
          using \<open>\<forall>x\<in>X. inv_into X id x = x\<close> by (by100 auto)
        show "{x \<in> X. id x \<in> V} \<subseteq> {x \<in> X. inv_into X id x \<in> V}"
          using \<open>\<forall>x\<in>X. inv_into X id x = x\<close> by (by100 auto)
      qed
      thus "{x \<in> X. inv_into X id x \<in> V} \<in> TX"
        using hid_cont unfolding top1_continuous_map_on_def using \<open>V \<in> TX\<close> by simp
    qed
    thus ?thesis unfolding top1_homeomorphism_on_def using hX_top hid_cont by simp
  qed
  show ?thesis
  proof -
    \<comment> \<open>If scheme\\_equiv to a normal form: Theorem 76 gives homeomorphism preservation.
       The normal form's quotient = the standard surface. So X \\<cong> standard surface.\<close>
    from hreduced show ?thesis
    proof (elim disjE exE conjE)
      \<comment> \<open>Case 1: scheme \\<sim> torus normal form.\<close>
      fix n w assume hn: "n > 0" and htor: "top1_is_torus_scheme w n"
          and hequiv: "top1_scheme_equiv scheme w"
      \<comment> \<open>X is quotient of w (by scheme\\_equiv\\_preserves\\_quotient).\<close>
      have "top1_quotient_of_scheme_on X TX w"
        by (rule scheme_equiv_preserves_quotient[OF hsch hequiv])
      hence "top1_quotient_of_scheme_on X TX (top1_n_torus_scheme n)"
        using htor unfolding top1_is_torus_scheme_def by simp
      hence "top1_is_n_fold_torus_on X TX n"
        using hn unfolding top1_is_n_fold_torus_on_def by simp
      \<comment> \<open>X is itself an n-fold torus. Take T\\_n = X, h = id.\<close>
      show ?thesis
        using hn \<open>top1_is_n_fold_torus_on X TX n\<close> hid_homeo
        by (by5000 blast)
    next
      \<comment> \<open>Case 3: scheme \\<sim> projective normal form.\<close>
      fix m w assume hm: "m > 0" and hproj: "top1_is_projective_scheme w m"
          and hequiv: "top1_scheme_equiv scheme w"
      have "top1_quotient_of_scheme_on X TX w"
        by (rule scheme_equiv_preserves_quotient[OF hsch hequiv])
      hence "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
        using hproj unfolding top1_is_projective_scheme_def by simp
      show ?thesis
      proof (cases "m \<ge> 2")
        case True
        hence "top1_is_m_fold_projective_on X TX m"
          unfolding top1_is_m_fold_projective_on_def
          using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close> by simp
        thus ?thesis using hm \<open>top1_is_m_fold_projective_on X TX m\<close> hid_homeo by (by5000 blast)
      next
        case False hence hm1: "m = 1" using hm by linarith
        \<comment> \<open>m=1: projective scheme has length 2, but quotient\\_of\\_scheme needs polygon with n \\<ge> 3. Contradiction.\<close>
        have hlen2: "length (top1_m_projective_scheme 1) = 2"
          unfolding top1_m_projective_scheme_def by simp
        from \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close>
        have hqs1: "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme 1)"
          using hm1 by simp
        from hqs1 obtain P0 q0 where "top1_is_polygonal_region_on P0 (length (top1_m_projective_scheme 1))"
          by (rule quotient_of_scheme_extract)
        hence "top1_is_polygonal_region_on P0 2" using hlen2 by simp
        hence "2 \<ge> (3::nat)" unfolding top1_is_polygonal_region_on_def by (by100 blast)
        hence False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


end

