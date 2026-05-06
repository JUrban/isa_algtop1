theory AlgTop
  imports "AlgTopC.AlgTopCached"
begin




\<comment> \<open>===== Theorems with sorry, moved here for caching =====\<close>


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
  \<comment> \<open>Step 1: S²-{p,q} = U \<union> V where U = S²-e13, V = S²-e24.
     Both U, V are open in S²-{p,q}. U \<inter> V = S²-(e13 \<union> e24) has two path-components.\<close>
  \<comment> \<open>Step 2: U and V are each simply connected (S² minus a point is contractible to the
     opposite hemisphere; S² minus an arc is still simply connected).\<close>
  \<comment> \<open>Step 3: f alternates between U and V (traversing edges alternately in each).
     By Theorem 63.1 (generalized SvK for non-trivial intersection),
     the path-class [f] is non-trivial in \<pi>_1(S²-{p,q}).\<close>
  show ?thesis sorry \<comment> \<open>Theorem 63.1: alternating loop in U\<union>V is non-trivial when U\<inter>V disconnected.\<close>
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
      have hsub_eq: "subspace_topology ?Xpq ?TXpq C = ?TC"
        using subspace_topology_trans[OF \<open>C \<subseteq> ?Xpq\<close>] by (by100 simp)
      have hid_eq: "id = (\<lambda>x::(real\<times>real\<times>real). x)" by (rule ext) (by100 simp)
      show ?thesis
      proof -
        have h1: "top1_continuous_map_on C (subspace_topology ?Xpq ?TXpq C) ?Xpq ?TXpq id"
          using top1_continuous_map_on_restrict_domain_simple[OF hid_Xpq \<open>C \<subseteq> ?Xpq\<close>] .
        have h2: "top1_continuous_map_on C ?TC ?Xpq ?TXpq id"
          using h1 hsub_eq by (by100 presburger)
        show ?thesis using h2 hid_eq by (by100 presburger)
      qed
    qed
    show ?thesis
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTC hTXpq hc0_C hc0_Xpq hincl]) (by100 simp)
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hj_hom hj_inj hj_surj unfolding bij_betw_def by (by100 blast)
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


section \<open>\<S>69 Free Groups\<close>


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


(** Z is free on {0} with generator map \<iota>(0) = 1.
    Extracted from the base case of Theorem 71.1 for reuse. **)
lemma Z_is_free_on_one_generator:
  "top1_is_free_group_full_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
      (\<lambda>(_::nat). (1::int)) {0::nat}"
proof -
  have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hZ_in: "\<forall>s\<in>{0::nat}. (\<lambda>(_::nat). (1::int)) s \<in> top1_Z_group"
    unfolding top1_Z_group_def by (by100 simp)
  have hZ_inj: "inj_on (\<lambda>(_::nat). (1::int)) {0::nat}"
    unfolding inj_on_def by (by100 simp)
  have hZ_gen: "top1_Z_group = top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
        ((\<lambda>(_::nat). (1::int)) ` {0::nat})"
  proof -
    have himg: "(\<lambda>(_::nat). (1::int)) ` {0::nat} = {1::int}" by (by100 simp)
    have himg_sub: "{1::int} \<subseteq> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
    \<comment> \<open>UNIV \<subseteq> subgroup_generated: every integer is in every subgroup containing 1.\<close>
    have hsub: "top1_Z_group \<subseteq> top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {1::int}"
    proof (rule subsetI)
      fix n :: int assume "n \<in> top1_Z_group"
      \<comment> \<open>Need: n \<in> \<Inter>{H. {1} \<subseteq> H \<and> H \<subseteq> UNIV \<and> group H}.\<close>
      show "n \<in> top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {1::int}"
        unfolding top1_subgroup_generated_on_def
      proof (rule InterI)
        fix H assume hH: "H \<in> {H. {1::int} \<subseteq> H \<and> H \<subseteq> top1_Z_group \<and>
            top1_is_group_on H top1_Z_mul top1_Z_id top1_Z_invg}"
        hence h1_in: "(1::int) \<in> H" and hH_grp: "top1_is_group_on H top1_Z_mul top1_Z_id top1_Z_invg"
          by (by100 blast)+
        \<comment> \<open>H is a subgroup of Z containing 1. Show n \<in> H by induction on |n|.\<close>
        have h0_in: "top1_Z_id \<in> H"
          using hH_grp unfolding top1_is_group_on_def by (by100 blast)
        have hinv_cl: "\<And>x. x \<in> H \<Longrightarrow> top1_Z_invg x \<in> H"
          using hH_grp unfolding top1_is_group_on_def by (by100 blast)
        have hmul_cl: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> top1_Z_mul x y \<in> H"
          using hH_grp unfolding top1_is_group_on_def by (by100 blast)
        have hm1_in: "(-1::int) \<in> H"
          using hinv_cl[OF h1_in] unfolding top1_Z_invg_def by (by100 simp)
        \<comment> \<open>Positive integers: int k \<in> H for all k by induction.\<close>
        have hpos: "\<And>k::nat. int k \<in> H"
        proof -
          fix k :: nat show "int k \<in> H"
          proof (induction k)
            case 0 thus ?case using h0_in unfolding top1_Z_id_def by (by100 simp)
          next
            case (Suc k)
            have "int (Suc k) = top1_Z_mul 1 (int k)"
              unfolding top1_Z_mul_def by (by100 simp)
            thus ?case using hmul_cl[OF h1_in Suc.IH] by (by100 simp)
          qed
        qed
        \<comment> \<open>Negative integers: - int k \<in> H for all k.\<close>
        have hneg: "\<And>k::nat. - int k \<in> H"
        proof -
          fix k :: nat show "- int k \<in> H"
          proof (induction k)
            case 0 thus ?case using h0_in unfolding top1_Z_id_def by (by100 simp)
          next
            case (Suc k)
            have "- int (Suc k) = top1_Z_mul (-1) (- int k)"
              unfolding top1_Z_mul_def by (by100 simp)
            thus ?case using hmul_cl[OF hm1_in Suc.IH] by (by100 simp)
          qed
        qed
        \<comment> \<open>Every integer is either int k or - int k.\<close>
        show "n \<in> H"
        proof (cases "n \<ge> 0")
          case True
          then obtain k where "n = int k" by (rule nonneg_int_cases)
          thus ?thesis using hpos by (by100 simp)
        next
          case False
          hence "n < 0" by (by100 simp)
          hence "- n \<ge> 0" by (by100 simp)
          then obtain k where hk: "- n = int k" by (rule nonneg_int_cases)
          hence "n = - int k" by (by100 simp)
          thus ?thesis using hneg by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Reverse inclusion: subgroup_generated \<subseteq> top1_Z_group.\<close>
    have hsup: "top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg {1::int} \<subseteq> top1_Z_group"
      by (rule subgroup_generated_subset[OF hZ_grp himg_sub])
    have hsub': "top1_Z_group \<subseteq> top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
        ((\<lambda>(_::nat). (1::int)) ` {0::nat})"
      using hsub himg by (by100 simp)
    have hsup': "top1_subgroup_generated_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
        ((\<lambda>(_::nat). (1::int)) ` {0::nat}) \<subseteq> top1_Z_group"
      using hsup himg by (by100 simp)
    from hsub' hsup' show ?thesis by (rule equalityI)
  qed
  \<comment> \<open>Reduced words with single generator: product = int(length) \<noteq> 0.\<close>
  have hword_prod_true: "\<And>k::nat. k > 0 \<Longrightarrow>
      top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
        (replicate k ((1::int), True)) = int k"
  proof -
    fix k :: nat
    show "k > 0 \<Longrightarrow>
        top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (replicate k ((1::int), True)) = int k"
    proof (induction k)
      case 0 thus ?case by (by100 simp)
    next
      case (Suc k)
      show ?case
      proof (cases "k = 0")
        case True
        thus ?thesis unfolding top1_Z_mul_def top1_Z_id_def by (by100 simp)
      next
        case False
        hence "k > 0" by (by100 simp)
        have "replicate (Suc k) ((1::int), True) = ((1::int), True) # replicate k ((1::int), True)"
          by (by100 simp)
        hence "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (replicate (Suc k) ((1::int), True))
          = top1_Z_mul 1 (top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
              (replicate k ((1::int), True)))"
          by (by100 simp)
        also have "\<dots> = top1_Z_mul 1 (int k)"
          using Suc.IH \<open>k > 0\<close> by (by100 simp)
        also have "\<dots> = int (Suc k)"
          unfolding top1_Z_mul_def by (by100 simp)
        finally show ?thesis .
      qed
    qed
  qed
  have hword_prod_false: "\<And>k::nat. k > 0 \<Longrightarrow>
      top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
        (replicate k ((1::int), False)) = - int k"
  proof -
    fix k :: nat
    show "k > 0 \<Longrightarrow>
        top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (replicate k ((1::int), False)) = - int k"
    proof (induction k)
      case 0 thus ?case by (by100 simp)
    next
      case (Suc k)
      show ?case
      proof (cases "k = 0")
        case True
        thus ?thesis unfolding top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
      next
        case False
        hence "k > 0" by (by100 simp)
        have "replicate (Suc k) ((1::int), False) = ((1::int), False) # replicate k ((1::int), False)"
          by (by100 simp)
        hence "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
            (replicate (Suc k) ((1::int), False))
          = top1_Z_mul (top1_Z_invg 1) (top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
              (replicate k ((1::int), False)))"
          by (by100 simp)
        also have "\<dots> = top1_Z_mul (top1_Z_invg 1) (- int k)"
          using Suc.IH \<open>k > 0\<close> by (by100 simp)
        also have "\<dots> = - int (Suc k)"
          unfolding top1_Z_mul_def top1_Z_invg_def by (by100 simp)
        finally show ?thesis .
      qed
    qed
  qed
  \<comment> \<open>A reduced word where all entries are mapped to (1,b) must be replicate k (1,b).\<close>
  \<comment> \<open>Helper: mapped word has constant boolean in reduced case.\<close>
  have hconst_bool: "\<And>ws :: (nat \<times> bool) list. ws \<noteq> [] \<Longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). ((1::int), b)) ws) \<Longrightarrow>
      \<exists>b. map (\<lambda>(s, b). ((1::int), b)) ws = replicate (length ws) ((1::int), b)"
  proof -
    fix ws :: "(nat \<times> bool) list"
    assume hne: "ws \<noteq> []"
    assume hred: "top1_is_reduced_word (map (\<lambda>(s, b). ((1::int), b)) ws)"
    \<comment> \<open>All booleans in ws are equal. First show the mapped word has constant entries.\<close>
    let ?mws = "map (\<lambda>(s, b). ((1::int), b)) ws"
    have hred_const: "\<And>xs :: (int \<times> bool) list. xs \<noteq> [] \<Longrightarrow>
        top1_is_reduced_word xs \<Longrightarrow> (\<forall>i < length xs. fst (xs ! i) = fst (hd xs)) \<Longrightarrow>
        xs = replicate (length xs) (hd xs)"
    proof -
      fix xs :: "(int \<times> bool) list"
      show "xs \<noteq> [] \<Longrightarrow> top1_is_reduced_word xs \<Longrightarrow>
          (\<forall>i < length xs. fst (xs ! i) = fst (hd xs)) \<Longrightarrow>
          xs = replicate (length xs) (hd xs)"
      proof (induction xs rule: induct_list012)
        case 1 thus ?case by (by100 simp)
      next
        case (2 x)
        thus ?case by (by100 simp)
      next
      case (3 x y zs)
        obtain gx bx where hx: "x = (gx, bx)" by (cases x) (by100 simp)
        obtain gy cy where hy: "y = (gy, cy)" by (cases y) (by100 simp)
        \<comment> \<open>The reduced-word condition for the first two elements gives gx\<noteq>gy \<or> bx=cy.\<close>
        have hred_full: "top1_is_reduced_word (x # y # zs)" using "3.prems"(2) by (by100 simp)
        have hred_pair: "(gx \<noteq> gy \<or> bx = cy) \<and> top1_is_reduced_word (y # zs)"
          using hred_full hx hy by (by100 simp)
        have hfst_all: "\<forall>i < length (x # y # zs). fst ((x # y # zs) ! i) = gx"
          using "3.prems"(3) hx by (by100 simp)
        have hgy_eq: "gy = gx" using hfst_all hy by (by100 force)
        hence hcy_eq: "bx = cy" using hred_pair by (by100 simp)
        hence hy_eq: "y = x" using hx hy hgy_eq by (by100 simp)
        have hred_tail: "top1_is_reduced_word (y # zs)" using hred_pair by (by100 blast)
        show ?case
        proof (cases "zs = []")
          case True thus ?thesis using hy_eq by (by100 simp)
        next
          case False
          hence hyzs_ne: "y # zs \<noteq> []" by (by100 simp)
          have hfst_tail: "\<forall>i < length (y # zs). fst ((y # zs) ! i) = fst (hd (y # zs))"
          proof (intro allI impI)
            fix i assume "i < length (y # zs)"
            hence "i + 1 < length (x # y # zs)" by (by100 simp)
            have "(x # y # zs) ! (i + 1) = (y # zs) ! i" by (by100 simp)
            hence "fst ((y # zs) ! i) = gx" using hfst_all \<open>i + 1 < _\<close> by (by100 force)
            thus "fst ((y # zs) ! i) = fst (hd (y # zs))" using hy hgy_eq by (by100 simp)
          qed
          have hIH: "y # zs = replicate (length (y # zs)) (hd (y # zs))"
            using "3.IH"(2)[OF hyzs_ne hred_tail hfst_tail] .
          hence "y # zs = replicate (length (y # zs)) y" by (by100 simp)
          thus ?thesis using hy_eq by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Apply to our mapped word.\<close>
    have hfst_const: "\<forall>i < length ?mws. fst (?mws ! i) = fst (hd ?mws)"
    proof (intro allI impI)
      fix i assume hi: "i < length ?mws"
      hence hi': "i < length ws" by (by100 simp)
      have "?mws ! i = (\<lambda>(s, b). ((1::int), b)) (ws ! i)"
        using hi' by (by100 simp)
      hence "fst (?mws ! i) = (1::int)" by (cases "ws ! i") (by100 simp)
      moreover have "fst (hd ?mws) = (1::int)"
      proof -
        obtain a rest where hws: "ws = a # rest" using hne
          by (cases ws) (by100 simp_all)
        show ?thesis unfolding hws by (cases a) (by100 simp)
      qed
      ultimately show "fst (?mws ! i) = fst (hd ?mws)" by (by100 simp)
    qed
    have hmws_ne: "?mws \<noteq> []" using hne by (by100 simp)
    have hmws_repl: "?mws = replicate (length ?mws) (hd ?mws)"
      using hred_const[OF hmws_ne hred hfst_const] .
    \<comment> \<open>Extract the common boolean value from hd.\<close>
    have h0_lt: "0 < length ws" using hne by (by100 simp)
    let ?b = "snd (hd ws)"
    have hhead_eq: "hd ?mws = ((1::int), ?b)"
    proof -
      obtain a rest where hws: "ws = a # rest" using hne
        by (cases ws) (by100 simp_all)
      show ?thesis unfolding hws by (cases a) (by100 simp)
    qed
    have hmap_eq: "map (\<lambda>(s, b). ((1::int), b)) ws = replicate (length ws) ((1::int), ?b)"
      using hmws_repl hhead_eq by (by100 simp)
    show "\<exists>b. map (\<lambda>(s, b). ((1::int), b)) ws = replicate (length ws) ((1::int), b)"
      using hmap_eq by (by100 blast)
  qed
  have hZ_red: "\<forall>ws :: (nat \<times> bool) list.
        ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws ! i) \<in> {0::nat}) \<longrightarrow>
        top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws) \<noteq> top1_Z_id"
  proof (intro allI impI)
    fix ws :: "(nat \<times> bool) list"
    assume hne: "ws \<noteq> []"
    assume hred: "top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws)"
    assume hS: "\<forall>i<length ws. fst (ws ! i) \<in> {0::nat}"
    have hred': "top1_is_reduced_word (map (\<lambda>(s, b). ((1::int), b)) ws)"
      using hred by (by100 simp)
    from hconst_bool[OF hne hred']
    obtain b where hb: "map (\<lambda>(s, b). ((1::int), b)) ws = replicate (length ws) ((1::int), b)"
      by (by100 blast)
    have hlen: "length ws > 0" using hne by (by100 simp)
    have hmap_eq: "map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws = map (\<lambda>(s, b). ((1::int), b)) ws"
      by (by100 simp)
    show "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws) \<noteq> top1_Z_id"
    proof (cases b)
      case True
      have heq: "map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws = replicate (length ws) ((1::int), True)"
        using hb hmap_eq True by (by100 simp)
      have "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (replicate (length ws) ((1::int), True)) = int (length ws)"
        using hword_prod_true[OF hlen] .
      thus ?thesis unfolding top1_Z_id_def using hlen heq by (by100 simp)
    next
      case False
      have heq: "map (\<lambda>(s, b). ((\<lambda>_. 1::int) s, b)) ws = replicate (length ws) ((1::int), False)"
        using hb hmap_eq False by (by100 simp)
      have "top1_group_word_product top1_Z_mul top1_Z_id top1_Z_invg
          (replicate (length ws) ((1::int), False)) = - int (length ws)"
        using hword_prod_false[OF hlen] .
      thus ?thesis unfolding top1_Z_id_def using hlen heq by (by100 simp)
    qed
  qed
  show ?thesis using hZ_grp hZ_in hZ_inj hZ_gen hZ_red
    unfolding top1_is_free_group_full_on_def by (by100 blast)
qed


(** from \<S>71 Theorem 71.1: finite wedge of circles has free fundamental group
    generated by the individual circle loops. **)
theorem Theorem_71_1_wedge_of_circles_finite:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX {..<n} p"
  shows "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
using assms proof (induction n arbitrary: X TX p rule: less_induct)
  case (less n)
  hence hwedge: "top1_is_wedge_of_circles_on X TX {..<n} p" by simp
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
    moreover from hwedge obtain C where "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X" and "p \<in> X"
      unfolding top1_is_wedge_of_circles_on_def
      apply (elim conjE exE) by (by100 blast)
    ultimately show False by (by100 simp)
  qed
  have hbase: "n = 0 \<longrightarrow> ?case" using hn_pos by (by100 simp)
  \<comment> \<open>Base case n=1: X \<cong> S¹, \<pi>_1(X) \<cong> Z which is free on 1 generator.\<close>
  have hbase1: "n = 1 \<longrightarrow> ?case"
  proof (intro impI)
    assume hn1: "n = 1"
    hence hJ1: "{..<n} = {0::nat}" by (by100 auto)
    let ?G = "top1_Z_group" and ?mul = "top1_Z_mul" and ?e = "top1_Z_id"
    let ?invg = "top1_Z_invg" and ?\<iota> = "\<lambda>(_::nat). (1::int)"
    \<comment> \<open>Step 1: Extract the wedge structure for n=1.\<close>
    have hX_strict: "is_topology_on_strict X TX"
      using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
    have hC_ex: "\<exists>C. (\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
          \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
        \<and> (\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X"
    proof -
      have hdef: "is_topology_on_strict X TX \<and> is_hausdorff_on X TX \<and> p \<in> X \<and>
        (\<exists>C. (\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
            \<and> (\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X
            \<and> (\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p})
            \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
                 (closedin_on X TX D \<longleftrightarrow>
                  (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))))"
        using hwedge[unfolded top1_is_wedge_of_circles_on_def] .
      have hC_full_ex: "\<exists>C. (\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
            \<and> (\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X
            \<and> (\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p})
            \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
                 (closedin_on X TX D \<longleftrightarrow>
                  (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))))"
        using hdef by (by100 blast)
      from hC_full_ex obtain C where
        hC1: "\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
        and hC2: "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X"
        by (elim exE conjE) (rule that, assumption+)
      show ?thesis using hC1 hC2 by (by100 blast)
    qed
    from hC_ex obtain C where
        hC_all: "\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
          \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
        and hX_eq_full: "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X"
      by blast
    have hX_eq: "(\<Union>\<alpha>\<in>{0::nat}. C \<alpha>) = X" using hX_eq_full hJ1 by (by100 simp)
    have h0_in: "(0::nat) \<in> {..<n}" using hn1 by (by100 simp)
    have hC0: "C (0::nat) \<subseteq> X" using hC_all h0_in by (by100 blast)
    have hp_C0: "p \<in> C 0" using hC_all h0_in by (by100 blast)
    have hC0_homeo: "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C 0) (subspace_topology X TX (C 0)) h"
      using hC_all h0_in by (by100 blast)
    have hX_C0: "X = C 0" using hX_eq by (by100 simp)
    \<comment> \<open>Step 2: X = C(0) is homeomorphic to S¹.\<close>
    obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
        (C 0) (subspace_topology X TX (C 0)) h"
      using hC0_homeo by (by100 blast)
    have hTC0: "subspace_topology X TX (C 0) = TX"
    proof -
      have hC0X: "C 0 = X" using hX_C0 by (by100 simp)
      have hTX_pow: "TX \<subseteq> Pow X" using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
      show ?thesis unfolding subspace_topology_def
      proof (rule set_eqI)
        fix U
        show "(U \<in> {C 0 \<inter> V |V. V \<in> TX}) = (U \<in> TX)"
        proof
          assume "U \<in> {C 0 \<inter> V |V. V \<in> TX}"
          then obtain V where "V \<in> TX" "U = C 0 \<inter> V" by (by100 blast)
          hence "U = V" using hC0X hTX_pow by (by100 blast)
          thus "U \<in> TX" using \<open>V \<in> TX\<close> by (by100 simp)
        next
          assume "U \<in> TX"
          hence "U \<subseteq> X" using hTX_pow by (by100 blast)
          hence "C 0 \<inter> U = U" using hC0X by (by100 blast)
          thus "U \<in> {C 0 \<inter> V |V. V \<in> TX}" using \<open>U \<in> TX\<close> by (by100 blast)
        qed
      qed
    qed
    have hh2: "top1_homeomorphism_on top1_S1 top1_S1_topology X TX h"
      using hh hTC0 hX_C0 by (by100 simp)
    \<comment> \<open>Step 3: \<pi>_1(X,p) \<cong> \<pi>_1(S¹, h⁻¹(p)) via homeomorphism.\<close>
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTX: "is_topology_on X TX"
      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>The homeomorphism goes S¹ \<rightarrow> X. We need the inverse X \<rightarrow> S¹ for Cor 52.5.\<close>
    let ?hinv = "inv_into top1_S1 h"
    have hhinv: "top1_homeomorphism_on X TX top1_S1 top1_S1_topology ?hinv"
      by (rule homeomorphism_inverse[OF hh2])
    have hp_X: "p \<in> X" using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
    have hhinv_p_S1: "?hinv p \<in> top1_S1"
      using hhinv hp_X unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
      by (by100 blast)
    let ?q = "?hinv p"
    have hq_eq: "?hinv p = ?q" by (by100 simp)
    have h_pi1_iso_S1: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology ?q)
        (top1_fundamental_group_mul top1_S1 top1_S1_topology ?q)"
      by (rule Corollary_52_5_homeomorphism_iso[OF hTX hTS1 hhinv hp_X hq_eq])
    \<comment> \<open>Step 4: \<pi>_1(S¹, ?hinv(p)) \<cong> \<pi>_1(S¹, (1,0)) by basepoint independence.\<close>
    have h10_S1: "(1::real, 0::real) \<in> top1_S1"
      unfolding top1_S1_def by (by100 simp)
    have h_pi1_bp: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (?hinv p))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (?hinv p))
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
      by (rule Corollary_52_2_basepoint_independent[OF S1_path_connected hhinv_p_S1 h10_S1])
    \<comment> \<open>Step 5: \<pi>_1(S¹, (1,0)) \<cong> Z by Theorem 54.5.\<close>
    have h_pi1_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>Step 6: Chain: \<pi>_1(X,p) \<cong> Z.\<close>
    have h_pi1_X_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)
        top1_Z_group top1_Z_mul"
    proof -
      have hstep1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (?hinv p))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (?hinv p))
          top1_Z_group top1_Z_mul"
        by (rule groups_isomorphic_trans_fwd[OF h_pi1_bp h_pi1_Z])
      show ?thesis
        by (rule groups_isomorphic_trans_fwd[OF h_pi1_iso_S1 hstep1])
    qed
    \<comment> \<open>Step 7: Z is free on {0::nat} with \<iota>(0) = 1.\<close>
    have hZ_free: "top1_is_free_group_full_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
        (\<lambda>(_::nat). (1::int)) {0::nat}"
      by (rule Z_is_free_on_one_generator)
    \<comment> \<open>Step 8: Combine: free group on {0} isomorphic to \<pi>_1(X,p).\<close>
    have hZ_iso_rev: "top1_groups_isomorphic_on top1_Z_group top1_Z_mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)"
    proof -
      have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
      have hpi_grp: "top1_is_group_on
          (top1_fundamental_group_carrier X TX p)
          (top1_fundamental_group_mul X TX p)
          (top1_fundamental_group_id X TX p)
          (top1_fundamental_group_invg X TX p)"
        by (rule top1_fundamental_group_is_group[OF hTX hp_X])
      show ?thesis
        by (rule top1_groups_isomorphic_on_sym[OF h_pi1_X_Z hpi_grp hZ_grp])
    qed
    have hZ_free': "top1_is_free_group_full_on ?G ?mul ?e ?invg ?\<iota> {..<n}"
      using hZ_free hJ1 by (by100 simp)
    show "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
      using hZ_free' hZ_iso_rev by (by100 blast)
  qed
  \<comment> \<open>Inductive step: n \<ge> 2. Decompose X = X_{n-1} \<union> C_n, intersection = {p}.
     By IH: \<pi>_1(X_{n-1}) free on n-1 generators. \<pi>_1(C_n) \<cong> Z, free on 1.
     X_{n-1} \<inter> C_n = {p} simply connected. Corollary 70.3 \<Rightarrow> free product.
     Theorem 69.2: free(n-1) * free(1) = free(n).\<close>
  have hstep: "n \<ge> 2 \<longrightarrow> ?case"
  proof (intro impI)
    assume hn2: "n \<ge> 2"
    \<comment> \<open>Step 0: Strong induction hypothesis. We assume the theorem holds for n-1.\<close>
    have hn1_pos: "n - 1 > 0" using hn2 by (by100 linarith)
    have hn1_lt: "n - 1 < n" using hn2 by (by100 linarith)
    have hIH: "\<forall>(Y::'a set) TY q.
        top1_is_wedge_of_circles_on Y TY {..<(n-1)} q \<longrightarrow>
        (\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
           top1_is_free_group_full_on G mul e invg \<iota> {..<(n-1)}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier Y TY q)
             (top1_fundamental_group_mul Y TY q))"
      using less.IH[OF hn1_lt] by (by100 blast)
    \<comment> \<open>Step 1: Extract the circle family C from the wedge definition.\<close>
    have hX_strict: "is_topology_on_strict X TX"
      using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
    have hTX: "is_topology_on X TX"
      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hp_X: "p \<in> X"
      using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
    have hHausdorff: "is_hausdorff_on X TX"
      using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
    obtain C where
        hC_props: "\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
            \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
        and hC_union: "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X"
        and hC_inter: "\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
        and hC_weak: "\<forall>D. D \<subseteq> X \<longrightarrow>
             (closedin_on X TX D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      using hwedge unfolding top1_is_wedge_of_circles_on_def
      by (elim conjE exE) (rule that, assumption+)
    \<comment> \<open>Step 2: Define X' = \<Union>{C(\<alpha>) | \<alpha> < n-1}, the sub-wedge of n-1 circles.
       Define Cn = C(n-1), the last circle.\<close>
    let ?X' = "\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>"
    let ?Cn = "C (n - 1)"
    have hn1_in: "n - 1 \<in> {..<n}" using hn2 by (by100 simp)
    have hCn_sub: "?Cn \<subseteq> X" using hC_props hn1_in by (by100 blast)
    have hp_Cn: "p \<in> ?Cn" using hC_props hn1_in by (by100 blast)
    have hX'_sub: "?X' \<subseteq> X"
    proof -
      have "\<forall>\<alpha>\<in>{..<(n-1)}. C \<alpha> \<subseteq> X"
      proof (intro ballI)
        fix \<alpha> assume "\<alpha> \<in> {..<(n-1)}"
        hence "\<alpha> \<in> {..<n}" using hn2 by (by100 simp)
        thus "C \<alpha> \<subseteq> X" using hC_props by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
    have hp_X': "p \<in> ?X'"
    proof -
      have "(0::nat) \<in> {..<(n-1)}" using hn2 by (by100 simp)
      moreover have "p \<in> C 0"
      proof -
        have "(0::nat) \<in> {..<n}" using hn_pos by (by100 simp)
        thus ?thesis using hC_props by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 2a: X = X' \<union> C(n-1).\<close>
    have hX_decomp: "X = ?X' \<union> ?Cn"
    proof -
      have "{..<n} = {..<(n-1)} \<union> {n-1}" using hn2 by (by100 auto)
      hence "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<union> C (n-1)"
        by (by100 auto)
      thus ?thesis using hC_union by (by100 simp)
    qed
    \<comment> \<open>Step 2b: X' \<inter> C(n-1) = {p}.\<close>
    have hX'_Cn_inter: "?X' \<inter> ?Cn = {p}"
    proof -
      have "\<forall>\<alpha>\<in>{..<(n-1)}. C \<alpha> \<inter> C (n-1) = {p}"
      proof (intro ballI)
        fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
        hence h\<alpha>n: "\<alpha> \<in> {..<n}" using hn2 by (by100 simp)
        have h\<alpha>_ne: "\<alpha> \<noteq> n - 1" using h\<alpha> by (by100 simp)
        show "C \<alpha> \<inter> C (n-1) = {p}" using hC_inter h\<alpha>n hn1_in h\<alpha>_ne by (by100 blast)
      qed
      moreover have "p \<in> ?X' \<inter> ?Cn" using hp_X' hp_Cn by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 3: X' with the subspace topology is a wedge of n-1 circles.\<close>
    let ?TX' = "subspace_topology X TX ?X'"
    have hX'_wedge: "top1_is_wedge_of_circles_on ?X' ?TX' {..<(n-1)} p"
    proof -
      \<comment> \<open>Condition 1: strict topology on X'\<close>
      have hX'_strict: "is_topology_on_strict ?X' ?TX'"
        by (rule subspace_topology_is_strict[OF hX_strict hX'_sub])
      \<comment> \<open>Condition 2: Hausdorff on X'\<close>
      have hX'_hausdorff: "is_hausdorff_on ?X' ?TX'"
        using conjunct2[OF conjunct2[OF Theorem_17_11]] hHausdorff hX'_sub by (by100 blast)
      \<comment> \<open>Condition 4: For each \<alpha> < n-1, subspace_topology X' TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)\<close>
      have hC_sub_X': "\<forall>\<alpha>\<in>{..<(n-1)}. C \<alpha> \<subseteq> ?X'"
        by (by100 blast)
      have hsub_eq: "\<forall>\<alpha>\<in>{..<(n-1)}.
          subspace_topology ?X' ?TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
      proof (intro ballI)
        fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
        have "C \<alpha> \<subseteq> ?X'" using hC_sub_X' h\<alpha> by (by100 blast)
        thus "subspace_topology ?X' ?TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
          by (rule subspace_topology_trans)
      qed
      \<comment> \<open>Condition 4 full: circles in X', p in each, homeomorphic to S1\<close>
      have hC_props': "\<forall>\<alpha>\<in>{..<(n-1)}. C \<alpha> \<subseteq> ?X' \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) h)"
      proof (intro ballI conjI)
        fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
        show "C \<alpha> \<subseteq> ?X'" using hC_sub_X' h\<alpha> by (by100 blast)
        have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
        show "p \<in> C \<alpha>" using hC_props h\<alpha>n by (by100 blast)
        have "subspace_topology ?X' ?TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
          using hsub_eq h\<alpha> by (by100 blast)
        moreover have "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
          using hC_props h\<alpha>n by (by100 blast)
        ultimately show "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) h"
          by (by100 simp)
      qed
      \<comment> \<open>Condition 5: union = X'\<close>
      have hC_union': "(\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) = ?X'"
        by (by100 simp)
      \<comment> \<open>Condition 6: pairwise intersection = {p}\<close>
      have hC_inter': "\<forall>\<alpha>\<in>{..<(n-1)}. \<forall>\<beta>\<in>{..<(n-1)}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
      proof (intro ballI impI)
        fix \<alpha> \<beta> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}" and h\<beta>: "\<beta> \<in> {..<(n-1)}" and hne: "\<alpha> \<noteq> \<beta>"
        have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
        have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
        show "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha>n h\<beta>n hne by (by100 blast)
      qed
      \<comment> \<open>Condition 7: coherent/weak topology\<close>
      have hTX': "is_topology_on ?X' ?TX'"
        using hX'_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hC_coh': "\<forall>D. D \<subseteq> ?X' \<longrightarrow>
             (closedin_on ?X' ?TX' D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)))"
      proof (intro allI impI iffI)
        fix D assume hDsub: "D \<subseteq> ?X'"
        \<comment> \<open>Forward: D closed in X' \<Rightarrow> each C(\<alpha>) \<inter> D closed in C(\<alpha>)\<close>
        { assume hDcl: "closedin_on ?X' ?TX' D"
          show "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
            \<comment> \<open>By Theorem_17_2: D closed in X' iff D = F \<inter> X' for some F closed in X\<close>
            have "closedin_on ?X' ?TX' D \<longleftrightarrow>
                (\<exists>F. closedin_on X TX F \<and> D = F \<inter> ?X')"
              by (rule Theorem_17_2[OF hTX hX'_sub])
            then obtain F where hFcl: "closedin_on X TX F" and hDeq: "D = F \<inter> ?X'"
              using hDcl by (by100 blast)
            \<comment> \<open>D \<subseteq> X, so F \<inter> X is relevant for hC_weak\<close>
            have hDX: "D \<subseteq> X" using hDsub hX'_sub by (by100 blast)
            have hFsub: "F \<subseteq> X" using hFcl by (rule closedin_sub)
            \<comment> \<open>C(\<alpha>) \<inter> D = C(\<alpha>) \<inter> F since C(\<alpha>) \<subseteq> X'\<close>
            have hCa_sub: "C \<alpha> \<subseteq> ?X'" using hC_sub_X' h\<alpha> by (by100 blast)
            have hCD_eq: "C \<alpha> \<inter> D = C \<alpha> \<inter> F"
            proof -
              have "D = F \<inter> ?X'" using hDeq .
              hence "C \<alpha> \<inter> D = C \<alpha> \<inter> (F \<inter> ?X')" by (by100 simp)
              also have "\<dots> = (C \<alpha> \<inter> ?X') \<inter> F" by (by100 blast)
              also have "C \<alpha> \<inter> ?X' = C \<alpha>" using hCa_sub by (by100 blast)
              finally show ?thesis by (by100 simp)
            qed
            \<comment> \<open>F closed in X \<Rightarrow> C(\<alpha>) \<inter> F closed in C(\<alpha>) w.r.t. subspace_topology X TX\<close>
            have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
            have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> F)"
            proof -
              have "C \<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
              hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> F) \<longleftrightarrow>
                  (\<exists>G. closedin_on X TX G \<and> C \<alpha> \<inter> F = G \<inter> C \<alpha>)"
                by (rule Theorem_17_2[OF hTX])
              moreover have "\<exists>G. closedin_on X TX G \<and> C \<alpha> \<inter> F = G \<inter> C \<alpha>"
                using hFcl by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>Rewrite using subspace_topology_trans and hCD_eq\<close>
            hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
              using hCD_eq by (by100 simp)
            moreover have "subspace_topology ?X' ?TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
              using hsub_eq h\<alpha> by (by100 simp)
            ultimately show "closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)"
              using hCD_eq by (by100 simp)
          qed
        }
        \<comment> \<open>Backward: each C(\<alpha>) \<inter> D closed in C(\<alpha>) \<Rightarrow> D closed in X'\<close>
        { assume hall: "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)"
          \<comment> \<open>Convert to subspace_topology X TX via hsub_eq\<close>
          have hall_X: "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
            have "closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)"
              using hall h\<alpha> by (by100 blast)
            thus "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
            proof -
              have "subspace_topology ?X' ?TX' (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
                using hsub_eq h\<alpha> by (by100 blast)
              thus ?thesis using \<open>closedin_on (C \<alpha>) (subspace_topology ?X' ?TX' (C \<alpha>)) (C \<alpha> \<inter> D)\<close>
                by (by100 simp)
            qed
          qed
          \<comment> \<open>For \<alpha> = n-1: D \<inter> C(n-1) \<subseteq> X' \<inter> C(n-1) = {p}, so it's {} or {p}\<close>
          have hDCn: "D \<inter> ?Cn \<subseteq> {p}"
            using hDsub hX'_Cn_inter by (by100 blast)
          have hCn_inter_D: "?Cn \<inter> D = D \<inter> ?Cn" by (by100 blast)
          \<comment> \<open>C(n-1) is homeomorphic to S1, so Hausdorff, so singletons are closed\<close>
          have hTCn: "is_topology_on ?Cn (subspace_topology X TX ?Cn)"
            by (rule subspace_topology_is_topology_on[OF hTX hCn_sub])
          have hCn_hausdorff: "is_hausdorff_on ?Cn (subspace_topology X TX ?Cn)"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] hHausdorff hCn_sub by (by100 blast)
          have hp_closed_Cn: "closedin_on ?Cn (subspace_topology X TX ?Cn) {p}"
            by (rule singleton_closed_in_hausdorff[OF hCn_hausdorff hp_Cn])
          have hempty_closed_Cn: "closedin_on ?Cn (subspace_topology X TX ?Cn) {}"
            by (rule closedin_empty[OF hTCn])
          have hCn_inter_closed: "closedin_on ?Cn (subspace_topology X TX ?Cn) (?Cn \<inter> D)"
          proof (cases "D \<inter> ?Cn = {}")
            case True
            hence "?Cn \<inter> D = {}" by (by100 blast)
            thus ?thesis using hempty_closed_Cn by (by100 simp)
          next
            case False
            hence "D \<inter> ?Cn = {p}" using hDCn by (by100 blast)
            hence "?Cn \<inter> D = {p}" by (by100 blast)
            thus ?thesis using hp_closed_Cn by (by100 simp)
          qed
          \<comment> \<open>Now: for ALL \<alpha> < n, C(\<alpha>) \<inter> D closed in C(\<alpha>) w.r.t. subspace_topology X TX\<close>
          have hall_all: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
            show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
            proof (cases "\<alpha> \<in> {..<(n-1)}")
              case True
              thus ?thesis using hall_X by (by100 blast)
            next
              case False
              hence "\<alpha> = n - 1" using h\<alpha> by (by100 simp)
              thus ?thesis using hCn_inter_closed by (by100 simp)
            qed
          qed
          \<comment> \<open>By hC_weak: D closed in X\<close>
          have hDX: "D \<subseteq> X" using hDsub hX'_sub by (by100 blast)
          have "closedin_on X TX D"
            using hC_weak hDX hall_all by (by100 blast)
          \<comment> \<open>D \<subseteq> X' and D closed in X \<Rightarrow> D = D \<inter> X' \<Rightarrow> D closed in X' by Theorem_17_2\<close>
          moreover have "D = D \<inter> ?X'" using hDsub by (by100 blast)
          ultimately show "closedin_on ?X' ?TX' D"
            using Theorem_17_2[OF hTX hX'_sub] by (by100 blast)
        }
      qed
      show ?thesis
        unfolding top1_is_wedge_of_circles_on_def
        using hX'_strict hX'_hausdorff hp_X' hC_props' hC_union' hC_inter' hC_coh'
        by (by100 blast)
    qed
    \<comment> \<open>Step 4: Apply IH to X': \<pi>_1(X', p) is free on n-1 generators.\<close>
    obtain G' :: "int set" and mul' :: "int \<Rightarrow> int \<Rightarrow> int"
        and e' :: int and invg' :: "int \<Rightarrow> int" and \<iota>' :: "nat \<Rightarrow> int" where
        hG'_free: "top1_is_free_group_full_on G' mul' e' invg' \<iota>' {..<(n-1)}"
        and hG'_iso: "top1_groups_isomorphic_on G' mul'
            (top1_fundamental_group_carrier ?X' ?TX' p)
            (top1_fundamental_group_mul ?X' ?TX' p)"
      using hIH hX'_wedge by (by100 blast)
    \<comment> \<open>Step 5: C(n-1) \<cong> S¹, so \<pi>_1(C(n-1), p) \<cong> Z, free on 1 generator.\<close>
    let ?TCn = "subspace_topology X TX ?Cn"
    have hCn_pi1_free: "\<exists>(G2::int set) mul2 e2 invg2 (\<iota>2::nat \<Rightarrow> int).
        top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 {0::nat}
      \<and> top1_groups_isomorphic_on G2 mul2
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)"
    proof -
      \<comment> \<open>Step 5a: Extract the homeomorphism h: S¹ \<rightarrow> C(n-1) from hC_props.\<close>
      obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
            ?Cn (subspace_topology X TX ?Cn) h"
        using hC_props hn1_in by (by100 blast)
      \<comment> \<open>Step 5b: Get the inverse homeomorphism hinv: C(n-1) \<rightarrow> S¹.\<close>
      let ?hinv_Cn = "inv_into top1_S1 h"
      have hhinv_Cn: "top1_homeomorphism_on ?Cn ?TCn top1_S1 top1_S1_topology ?hinv_Cn"
        by (rule homeomorphism_inverse[OF hh])
      \<comment> \<open>Step 5c: Topology facts.\<close>
      have hTCn: "is_topology_on ?Cn ?TCn"
        by (rule subspace_topology_is_topology_on[OF hTX hCn_sub])
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>Step 5d: p \<in> C(n-1) and hinv(p) \<in> S¹.\<close>
      have hhinv_p_S1: "?hinv_Cn p \<in> top1_S1"
        using hhinv_Cn hp_Cn unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
        by (by100 blast)
      \<comment> \<open>Step 5e: \<pi>_1(C(n-1), p) \<cong> \<pi>_1(S¹, hinv(p)) via homeomorphism.\<close>
      have hhinv_p_eq: "?hinv_Cn p = ?hinv_Cn p" by (by100 simp)
      have h_pi1_Cn_S1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (?hinv_Cn p))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (?hinv_Cn p))"
        by (rule Corollary_52_5_homeomorphism_iso[OF hTCn hTS1 hhinv_Cn hp_Cn hhinv_p_eq])
      \<comment> \<open>Step 5f: \<pi>_1(S¹, hinv(p)) \<cong> \<pi>_1(S¹, (1,0)) by basepoint independence.\<close>
      have h10_S1: "(1::real, 0::real) \<in> top1_S1"
        unfolding top1_S1_def by (by100 simp)
      have h_pi1_bp_Cn: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (?hinv_Cn p))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (?hinv_Cn p))
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
        by (rule Corollary_52_2_basepoint_independent[OF S1_path_connected hhinv_p_S1 h10_S1])
      \<comment> \<open>Step 5g: \<pi>_1(S¹, (1,0)) \<cong> Z by Theorem 54.5.\<close>
      have h_pi1_Z_Cn: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          top1_Z_group top1_Z_mul"
        by (rule Theorem_54_5_iso)
      \<comment> \<open>Step 5h: Chain: \<pi>_1(C(n-1), p) \<cong> Z.\<close>
      have hchain1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (?hinv_Cn p))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (?hinv_Cn p))
          top1_Z_group top1_Z_mul"
        by (rule groups_isomorphic_trans_fwd[OF h_pi1_bp_Cn h_pi1_Z_Cn])
      have hchain2: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)
          top1_Z_group top1_Z_mul"
        by (rule groups_isomorphic_trans_fwd[OF h_pi1_Cn_S1 hchain1])
      \<comment> \<open>Step 5i: Z \<cong> \<pi>_1(C(n-1), p) (reverse direction for the conclusion).\<close>
      have hZ_grp_Cn: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
      have hpi_grp_Cn: "top1_is_group_on
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)
          (top1_fundamental_group_id ?Cn ?TCn p)
          (top1_fundamental_group_invg ?Cn ?TCn p)"
        by (rule top1_fundamental_group_is_group[OF hTCn hp_Cn])
      have hZ_iso_Cn: "top1_groups_isomorphic_on top1_Z_group top1_Z_mul
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)"
        by (rule top1_groups_isomorphic_on_sym[OF hchain2 hpi_grp_Cn hZ_grp_Cn])
      \<comment> \<open>Step 5j: Z is free on {0}.\<close>
      have hZ_free_Cn: "top1_is_free_group_full_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg
          (\<lambda>(_::nat). (1::int)) {0::nat}"
        by (rule Z_is_free_on_one_generator)
      \<comment> \<open>Step 5k: Combine.\<close>
      show ?thesis
        using hZ_free_Cn hZ_iso_Cn by (by100 blast)
    qed
    obtain G2 :: "int set" and mul2 :: "int \<Rightarrow> int \<Rightarrow> int"
        and e2 :: int and invg2 :: "int \<Rightarrow> int" and \<iota>2 :: "nat \<Rightarrow> int" where
        hG2_free: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 {0::nat}"
        and hG2_iso: "top1_groups_isomorphic_on G2 mul2
            (top1_fundamental_group_carrier ?Cn ?TCn p)
            (top1_fundamental_group_mul ?Cn ?TCn p)"
      using hCn_pi1_free by (by100 blast)
    \<comment> \<open>Step 6: Build open sets U, V covering X with simply connected intersection.
       U is an open neighborhood of X' (all of C(\<alpha>) for \<alpha><n-1, plus an arc of C(n-1) containing p).
       V is an open neighborhood of C(n-1) (C(n-1) plus arcs of each C(\<alpha>) containing p).
       U \<inter> V deformation-retracts to {p}, hence is simply connected.\<close>
    obtain U V :: "'a set" where
        hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
        and hUV_cover: "U \<union> V = X"
        and hUV_sc: "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
        and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
        and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
        and hp_UV: "p \<in> U \<inter> V"
        \<comment> \<open>U deformation-retracts to X', V deformation-retracts to C(n-1).\<close>
        and hU_pi1: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
            (top1_fundamental_group_mul U (subspace_topology X TX U) p)
            (top1_fundamental_group_carrier ?X' ?TX' p)
            (top1_fundamental_group_mul ?X' ?TX' p)"
        and hV_pi1: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
            (top1_fundamental_group_mul V (subspace_topology X TX V) p)
            (top1_fundamental_group_carrier ?Cn ?TCn p)
            (top1_fundamental_group_mul ?Cn ?TCn p)"
    proof -
      \<comment> \<open>Choose points q(\<alpha>) \<noteq> p on each circle.\<close>
      have hq_exists: "\<forall>\<alpha>\<in>{..<n}. \<exists>q. q \<in> C \<alpha> \<and> q \<noteq> p"
      proof (intro ballI)
        fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
        obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
            (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h" using hC_props h\<alpha> by (by100 blast)
        have hbij: "bij_betw h top1_S1 (C \<alpha>)" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hp_in: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
        \<comment> \<open>S¹ has more than one point.\<close>
        have "(1::real, 0::real) \<in> top1_S1 \<and> (- 1, 0) \<in> top1_S1 \<and> (1::real, 0) \<noteq> (- 1::real, 0)"
          unfolding top1_S1_def by (by100 auto)
        then obtain a b :: "real \<times> real" where "a \<in> top1_S1" "b \<in> top1_S1" "a \<noteq> b" by (by100 blast)
        hence "h a \<in> C \<alpha> \<and> h b \<in> C \<alpha> \<and> h a \<noteq> h b"
          using hbij unfolding bij_betw_def inj_on_def by (by100 blast)
        hence "h a \<noteq> p \<or> h b \<noteq> p" by (by100 force)
        thus "\<exists>q. q \<in> C \<alpha> \<and> q \<noteq> p" using \<open>h a \<in> C \<alpha> \<and> h b \<in> C \<alpha> \<and> h a \<noteq> h b\<close> by (by100 blast)
      qed
      obtain q :: "nat \<Rightarrow> 'a" where hq: "\<forall>\<alpha>\<in>{..<n}. q \<alpha> \<in> C \<alpha> \<and> q \<alpha> \<noteq> p"
      proof -
        from hq_exists have "\<forall>\<alpha>\<in>{..<n}. \<exists>q. q \<in> C \<alpha> \<and> q \<noteq> p" .
        define q0 where "q0 = (\<lambda>\<alpha>. SOME q. q \<in> C \<alpha> \<and> q \<noteq> p)"
        have "\<forall>\<alpha>\<in>{..<n}. q0 \<alpha> \<in> C \<alpha> \<and> q0 \<alpha> \<noteq> p"
        proof (intro ballI)
          fix \<alpha> assume "\<alpha> \<in> {..<n}"
          hence "\<exists>q. q \<in> C \<alpha> \<and> q \<noteq> p" using hq_exists by (by100 blast)
          thus "q0 \<alpha> \<in> C \<alpha> \<and> q0 \<alpha> \<noteq> p" unfolding q0_def by (rule someI_ex)
        qed
        hence "\<exists>q. \<forall>\<alpha>\<in>{..<n}. q \<alpha> \<in> C \<alpha> \<and> q \<alpha> \<noteq> p"
          by (by100 blast)
        thus ?thesis using that by (by100 blast)
      qed
      \<comment> \<open>Define W(\<alpha>) = C(\<alpha>) - {q(\<alpha>)}, U, V.\<close>
      define W where "W \<alpha> = C \<alpha> - {q \<alpha>}" for \<alpha>
      define U_def where "U_def = (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<union> W (n-1)"
      define V_def where "V_def = (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>) \<union> C (n-1)"
      show ?thesis
      proof (rule that[of U_def V_def])
        show "openin_on X TX U_def"
        proof -
          \<comment> \<open>U_def \<subseteq> X\<close>
          have hU_sub: "U_def \<subseteq> X"
          proof -
            have h1: "(\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<subseteq> X"
              using hX'_sub by (by100 blast)
            have h2: "W (n-1) \<subseteq> C (n-1)" unfolding W_def by (by100 blast)
            have h3: "C (n-1) \<subseteq> X" using hCn_sub by (by100 blast)
            show ?thesis unfolding U_def_def using h1 h2 h3 by (by100 blast)
          qed
          \<comment> \<open>X - U_def \<subseteq> X\<close>
          have hcompl_sub: "X - U_def \<subseteq> X" by (by100 blast)
          \<comment> \<open>For each \<alpha> < n, C \<alpha> \<inter> (X - U_def) is closed in C \<alpha>\<close>
          have hall: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> (X - U_def))"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
            show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> (X - U_def))"
            proof (cases "\<alpha> \<in> {..<(n-1)}")
              case True
              \<comment> \<open>C \<alpha> \<subseteq> U_def, so C \<alpha> \<inter> (X - U_def) = {}\<close>
              have "C \<alpha> \<subseteq> (\<Union>\<beta>\<in>{..<(n-1)}. C \<beta>)" using True by (by100 blast)
              hence "C \<alpha> \<subseteq> U_def" unfolding U_def_def by (by100 blast)
              hence "C \<alpha> \<inter> (X - U_def) = {}" by (by100 blast)
              moreover have "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
              proof -
                have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                thus ?thesis by (rule subspace_topology_is_topology_on[OF hTX])
              qed
              ultimately show ?thesis using closedin_empty by (by100 simp)
            next
              case False
              hence h\<alpha>_eq: "\<alpha> = n - 1" using h\<alpha> by (by100 simp)
              \<comment> \<open>C(n-1) \<inter> (X - U_def) = {q(n-1)}\<close>
              have hCn_inter: "C (n-1) \<inter> (X - U_def) = {q (n-1)}"
              proof -
                \<comment> \<open>q(n-1) \<in> C(n-1)\<close>
                have hq_in: "q (n-1) \<in> C (n-1)" using hq hn1_in by (by100 blast)
                \<comment> \<open>q(n-1) \<notin> W(n-1)\<close>
                have hq_not_W: "q (n-1) \<notin> W (n-1)" unfolding W_def by (by100 blast)
                \<comment> \<open>q(n-1) \<notin> \<Union>{C \<beta> | \<beta> < n-1}: because C \<beta> \<inter> C(n-1) = {p} and q(n-1) \<noteq> p\<close>
                have hq_ne_p: "q (n-1) \<noteq> p" using hq hn1_in by (by100 blast)
                have hq_not_X': "q (n-1) \<notin> (\<Union>\<beta>\<in>{..<(n-1)}. C \<beta>)"
                proof (rule ccontr)
                  assume "\<not> q (n-1) \<notin> (\<Union>\<beta>\<in>{..<(n-1)}. C \<beta>)"
                  hence "q (n-1) \<in> (\<Union>\<beta>\<in>{..<(n-1)}. C \<beta>)" by (by100 blast)
                  then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hq\<beta>: "q (n-1) \<in> C \<beta>" by (by100 blast)
                  have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
                  have h\<beta>_ne: "\<beta> \<noteq> n - 1" using h\<beta> by (by100 simp)
                  have "C \<beta> \<inter> C (n-1) = {p}" using hC_inter h\<beta>n hn1_in h\<beta>_ne by (by100 blast)
                  hence "q (n-1) = p" using hq\<beta> hq_in by (by100 blast)
                  thus False using hq_ne_p by (by100 blast)
                qed
                \<comment> \<open>So q(n-1) \<notin> U_def\<close>
                have hq_not_U: "q (n-1) \<notin> U_def"
                  unfolding U_def_def using hq_not_X' hq_not_W by (by100 blast)
                \<comment> \<open>q(n-1) \<in> X\<close>
                have hq_X: "q (n-1) \<in> X" using hq_in hCn_sub by (by100 blast)
                \<comment> \<open>So q(n-1) \<in> C(n-1) \<inter> (X - U_def)\<close>
                have hq_mem: "q (n-1) \<in> C (n-1) \<inter> (X - U_def)" using hq_in hq_X hq_not_U by (by100 blast)
                \<comment> \<open>Conversely, if x \<in> C(n-1) \<inter> (X - U_def) then x = q(n-1)\<close>
                moreover have "\<forall>x. x \<in> C (n-1) \<inter> (X - U_def) \<longrightarrow> x = q (n-1)"
                proof (intro allI impI)
                  fix x assume hx: "x \<in> C (n-1) \<inter> (X - U_def)"
                  hence hx_Cn: "x \<in> C (n-1)" and hx_not_U: "x \<notin> U_def" by (by100 blast)+
                  \<comment> \<open>x \<notin> W(n-1) = C(n-1) - {q(n-1)}, so x = q(n-1)\<close>
                  have "x \<notin> W (n-1)" using hx_not_U unfolding U_def_def by (by100 blast)
                  hence "x \<notin> C (n-1) - {q (n-1)}" unfolding W_def by (by100 blast)
                  thus "x = q (n-1)" using hx_Cn by (by100 blast)
                qed
                ultimately show ?thesis by (by100 blast)
              qed
              \<comment> \<open>{q(n-1)} is closed in C(n-1) (Hausdorff)\<close>
              have hCn_hausdorff: "is_hausdorff_on (C (n-1)) (subspace_topology X TX (C (n-1)))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] hHausdorff hCn_sub by (by100 blast)
              have hq_closed: "closedin_on (C (n-1)) (subspace_topology X TX (C (n-1))) {q (n-1)}"
              proof -
                have "q (n-1) \<in> C (n-1)" using hq hn1_in by (by100 blast)
                thus ?thesis by (rule singleton_closed_in_hausdorff[OF hCn_hausdorff])
              qed
              show ?thesis using hCn_inter hq_closed h\<alpha>_eq by (by100 simp)
            qed
          qed
          \<comment> \<open>By hC_weak: X - U_def is closed in X\<close>
          have hclosed: "closedin_on X TX (X - U_def)"
            using hC_weak hcompl_sub hall by (by100 blast)
          \<comment> \<open>Hence U_def is open\<close>
          have "X - (X - U_def) = U_def" using hU_sub by (by100 blast)
          hence "U_def \<in> TX" using hclosed unfolding closedin_on_def by (by100 simp)
          thus ?thesis unfolding openin_on_def using hU_sub by (by100 blast)
        qed
        show "openin_on X TX V_def"
        proof -
          \<comment> \<open>V_def \<subseteq> X\<close>
          have hV_sub: "V_def \<subseteq> X"
          proof -
            have h1: "\<forall>\<alpha>\<in>{..<(n-1)}. W \<alpha> \<subseteq> X"
            proof (intro ballI)
              fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
              have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
              have "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
              thus "W \<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
            qed
            hence "(\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>) \<subseteq> X" by (by100 blast)
            moreover have "C (n-1) \<subseteq> X" using hCn_sub by (by100 blast)
            ultimately show ?thesis unfolding V_def_def by (by100 blast)
          qed
          \<comment> \<open>X - V_def \<subseteq> X\<close>
          have hcompl_sub: "X - V_def \<subseteq> X" by (by100 blast)
          \<comment> \<open>For each \<alpha> < n, C \<alpha> \<inter> (X - V_def) is closed in C \<alpha>\<close>
          have hall: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> (X - V_def))"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
            show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> (X - V_def))"
            proof (cases "\<alpha> = n - 1")
              case True
              \<comment> \<open>C(n-1) \<subseteq> V_def, so C(n-1) \<inter> (X - V_def) = {}\<close>
              have "C (n-1) \<subseteq> V_def" unfolding V_def_def by (by100 blast)
              hence "C (n-1) \<inter> (X - V_def) = {}" by (by100 blast)
              moreover have "is_topology_on (C (n-1)) (subspace_topology X TX (C (n-1)))"
                by (rule subspace_topology_is_topology_on[OF hTX hCn_sub])
              ultimately show ?thesis using closedin_empty True by (by100 simp)
            next
              case False
              hence h\<alpha>_lt: "\<alpha> \<in> {..<(n-1)}" using h\<alpha> by (by100 simp)
              \<comment> \<open>C \<alpha> \<inter> (X - V_def) = {q \<alpha>}\<close>
              have hC\<alpha>_inter: "C \<alpha> \<inter> (X - V_def) = {q \<alpha>}"
              proof -
                \<comment> \<open>q \<alpha> \<in> C \<alpha>\<close>
                have hq_in: "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
                \<comment> \<open>q \<alpha> \<notin> W \<alpha>\<close>
                have hq_not_W: "q \<alpha> \<notin> W \<alpha>" unfolding W_def by (by100 blast)
                \<comment> \<open>q \<alpha> \<notin> C(n-1): C \<alpha> \<inter> C(n-1) = {p} and q \<alpha> \<noteq> p\<close>
                have hq_ne_p: "q \<alpha> \<noteq> p" using hq h\<alpha> by (by100 blast)
                have hq_not_Cn: "q \<alpha> \<notin> C (n-1)"
                proof (rule ccontr)
                  assume "\<not> q \<alpha> \<notin> C (n-1)"
                  hence "q \<alpha> \<in> C (n-1)" by (by100 blast)
                  hence "q \<alpha> \<in> C \<alpha> \<inter> C (n-1)" using hq_in by (by100 blast)
                  moreover have "C \<alpha> \<inter> C (n-1) = {p}" using hC_inter h\<alpha> hn1_in False by (by100 blast)
                  ultimately have "q \<alpha> = p" by (by100 blast)
                  thus False using hq_ne_p by (by100 blast)
                qed
                \<comment> \<open>q \<alpha> \<notin> W \<beta> for \<beta> < n-1, \<beta> \<noteq> \<alpha>: because q \<alpha> \<notin> C \<beta> (as C \<alpha> \<inter> C \<beta> = {p})\<close>
                have hq_not_other_W: "\<forall>\<beta>\<in>{..<(n-1)}. \<beta> \<noteq> \<alpha> \<longrightarrow> q \<alpha> \<notin> W \<beta>"
                proof (intro ballI impI)
                  fix \<beta> assume h\<beta>: "\<beta> \<in> {..<(n-1)}" and hne: "\<beta> \<noteq> \<alpha>"
                  have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
                  have "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha> h\<beta>n hne by (by100 blast)
                  hence "q \<alpha> \<notin> C \<beta>" using hq_in hq_ne_p by (by100 blast)
                  thus "q \<alpha> \<notin> W \<beta>" unfolding W_def by (by100 blast)
                qed
                \<comment> \<open>Combine: q \<alpha> \<notin> W \<beta> for ALL \<beta> < n-1\<close>
                have hq_not_all_W: "\<forall>\<beta>\<in>{..<(n-1)}. q \<alpha> \<notin> W \<beta>"
                proof (intro ballI)
                  fix \<beta> assume h\<beta>: "\<beta> \<in> {..<(n-1)}"
                  show "q \<alpha> \<notin> W \<beta>"
                  proof (cases "\<beta> = \<alpha>")
                    case True thus ?thesis using hq_not_W by (by100 simp)
                  next
                    case False thus ?thesis using hq_not_other_W h\<beta> by (by100 blast)
                  qed
                qed
                hence hq_not_union_W: "q \<alpha> \<notin> (\<Union>\<beta>\<in>{..<(n-1)}. W \<beta>)" by (by100 blast)
                \<comment> \<open>So q \<alpha> \<notin> V_def\<close>
                have hq_not_V: "q \<alpha> \<notin> V_def"
                  unfolding V_def_def using hq_not_union_W hq_not_Cn by (by100 blast)
                \<comment> \<open>q \<alpha> \<in> X\<close>
                have hq_X: "q \<alpha> \<in> X" using hq_in hC_props h\<alpha> by (by100 blast)
                \<comment> \<open>So q \<alpha> \<in> C \<alpha> \<inter> (X - V_def)\<close>
                have hq_mem: "q \<alpha> \<in> C \<alpha> \<inter> (X - V_def)" using hq_in hq_X hq_not_V by (by100 blast)
                \<comment> \<open>Conversely, if x \<in> C \<alpha> \<inter> (X - V_def) then x = q \<alpha>\<close>
                moreover have "\<forall>x. x \<in> C \<alpha> \<inter> (X - V_def) \<longrightarrow> x = q \<alpha>"
                proof (intro allI impI)
                  fix x assume hx: "x \<in> C \<alpha> \<inter> (X - V_def)"
                  hence hx_C: "x \<in> C \<alpha>" and hx_not_V: "x \<notin> V_def" by (by100 blast)+
                  \<comment> \<open>x \<notin> W \<alpha> (since W \<alpha> \<subseteq> V_def)\<close>
                  have "W \<alpha> \<subseteq> V_def" unfolding V_def_def using h\<alpha>_lt by (by100 blast)
                  hence "x \<notin> W \<alpha>" using hx_not_V by (by100 blast)
                  hence "x \<notin> C \<alpha> - {q \<alpha>}" unfolding W_def by (by100 blast)
                  thus "x = q \<alpha>" using hx_C by (by100 blast)
                qed
                ultimately show ?thesis by (by100 blast)
              qed
              \<comment> \<open>{q \<alpha>} is closed in C \<alpha> (Hausdorff)\<close>
              have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
              hence hC\<alpha>_hausdorff: "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] hHausdorff by (by100 blast)
              have hq_closed: "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) {q \<alpha>}"
              proof -
                have "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
                thus ?thesis by (rule singleton_closed_in_hausdorff[OF hC\<alpha>_hausdorff])
              qed
              show ?thesis using hC\<alpha>_inter hq_closed by (by100 simp)
            qed
          qed
          \<comment> \<open>By hC_weak: X - V_def is closed in X\<close>
          have hclosed: "closedin_on X TX (X - V_def)"
            using hC_weak hcompl_sub hall by (by100 blast)
          \<comment> \<open>Hence V_def is open\<close>
          have "X - (X - V_def) = V_def" using hV_sub by (by100 blast)
          hence "V_def \<in> TX" using hclosed unfolding closedin_on_def by (by100 simp)
          thus ?thesis unfolding openin_on_def using hV_sub by (by100 blast)
        qed
        show "U_def \<union> V_def = X"
        proof -
          have "U_def \<union> V_def = (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<union> C (n-1)"
            unfolding U_def_def V_def_def W_def by (by100 blast)
          thus ?thesis using hX_decomp by (by100 simp)
        qed
        \<comment> \<open>Helper: Each C(alpha) is path-connected (via homeomorphism with S1).\<close>
        have hC_pc: "\<forall>\<alpha>\<in>{..<n}. top1_path_connected_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
          obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
            using hC_props h\<alpha> by (by100 blast)
          have hbij: "bij_betw h top1_S1 (C \<alpha>)"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have hcont_h: "top1_continuous_map_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have hTS1: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hTC\<alpha>: "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
          proof -
            have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
            thus ?thesis by (rule subspace_topology_is_topology_on[OF hTX])
          qed
          show "top1_path_connected_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))" using hTC\<alpha> .
          next
            fix x y assume hx: "x \<in> C \<alpha>" and hy: "y \<in> C \<alpha>"
            \<comment> \<open>Get preimages in S1.\<close>
            have hinv: "top1_homeomorphism_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))
                top1_S1 top1_S1_topology (inv_into top1_S1 h)"
              by (rule homeomorphism_inverse[OF hh])
            have hx': "inv_into top1_S1 h x \<in> top1_S1"
              using hinv hx unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
            have hy': "inv_into top1_S1 h y \<in> top1_S1"
              using hinv hy unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by (by100 blast)
            \<comment> \<open>Get a path in S1 from inv(x) to inv(y).\<close>
            obtain f where hf: "top1_is_path_on top1_S1 top1_S1_topology
                (inv_into top1_S1 h x) (inv_into top1_S1 h y) f"
              using S1_path_connected hx' hy' unfolding top1_path_connected_on_def by (by100 blast)
            \<comment> \<open>Compose: h \<circ> f is a path in C(\<alpha>).\<close>
            have hcont_f: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_S1 top1_S1_topology f"
              using hf unfolding top1_is_path_on_def by (by100 blast)
            have hcont_hf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h \<circ> f)"
              by (rule top1_continuous_map_on_comp[OF hcont_f hcont_h])
            have hf0: "f 0 = inv_into top1_S1 h x" and hf1: "f 1 = inv_into top1_S1 h y"
              using hf unfolding top1_is_path_on_def by (by100 blast)+
            have hx_eq: "h (inv_into top1_S1 h x) = x"
              using bij_betw_inv_into_right[OF hbij hx] .
            have hy_eq: "h (inv_into top1_S1 h y) = y"
              using bij_betw_inv_into_right[OF hbij hy] .
            have "(h \<circ> f) 0 = x" using hf0 hx_eq by (by100 simp)
            moreover have "(h \<circ> f) 1 = y" using hf1 hy_eq by (by100 simp)
            ultimately have "top1_is_path_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) x y (h \<circ> f)"
              unfolding top1_is_path_on_def using hcont_hf by (by100 blast)
            thus "\<exists>f. top1_is_path_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) x y f"
              by (by100 blast)
          qed
        qed
        \<comment> \<open>Helper: W(alpha) = C(alpha) - {q(alpha)} is path-connected.
           Proof: C(alpha) is homeomorphic to S1 via h. S1 minus a point is
           path-connected (parameterize via covering map R_to_S1, use convex
           interpolation avoiding the removed point). Transfer via h.\<close>
        have hW_pc: "\<forall>\<alpha>\<in>{..<n}. top1_path_connected_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
          \<comment> \<open>Get homeomorphism h: S1 -> C(alpha).\<close>
          obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
            using hC_props h\<alpha> by (by100 blast)
          have hbij: "bij_betw h top1_S1 (C \<alpha>)"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have hcont_h: "top1_continuous_map_on top1_S1 top1_S1_topology
              (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have hTS1: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
          have hTC\<alpha>: "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
            by (rule subspace_topology_is_topology_on[OF hTX hC\<alpha>_sub])
          \<comment> \<open>Inverse homeomorphism.\<close>
          let ?hinv = "inv_into top1_S1 h"
          have hhinv: "top1_homeomorphism_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))
              top1_S1 top1_S1_topology ?hinv"
            by (rule homeomorphism_inverse[OF hh])
          have hbij_inv: "bij_betw ?hinv (C \<alpha>) top1_S1"
            using hhinv unfolding top1_homeomorphism_on_def by (by100 blast)
          have hcont_hinv: "top1_continuous_map_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))
              top1_S1 top1_S1_topology ?hinv"
            using hhinv unfolding top1_homeomorphism_on_def by (by100 blast)
          \<comment> \<open>q' = h^{-1}(q(alpha)) in S1.\<close>
          have hq_in: "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
          define q' where "q' = ?hinv (q \<alpha>)"
          have hq'_S1: "q' \<in> top1_S1"
            using hbij_inv hq_in unfolding q'_def bij_betw_def by (by100 blast)
          have hq'_eq: "h q' = q \<alpha>"
            unfolding q'_def using bij_betw_inv_into_right[OF hbij hq_in] .
          \<comment> \<open>W(alpha) = h ` (S1 - {q'}).\<close>
          have hW_eq: "W \<alpha> = h ` (top1_S1 - {q'})"
          proof (intro set_eqI iffI)
            fix x assume hx: "x \<in> W \<alpha>"
            hence hx_C: "x \<in> C \<alpha>" and hx_nq: "x \<noteq> q \<alpha>" unfolding W_def by (by100 blast)+
            have "?hinv x \<in> top1_S1" using hbij_inv hx_C unfolding bij_betw_def by (by100 blast)
            moreover have "?hinv x \<noteq> q'"
            proof
              assume "?hinv x = q'"
              hence "h (?hinv x) = h q'" by (by100 simp)
              hence "x = q \<alpha>" using bij_betw_inv_into_right[OF hbij hx_C] hq'_eq by (by100 simp)
              thus False using hx_nq by (by100 blast)
            qed
            ultimately have hinv_mem: "?hinv x \<in> top1_S1 - {q'}" by (by100 blast)
            have "h (?hinv x) = x" using bij_betw_inv_into_right[OF hbij hx_C] .
            hence "x = h (?hinv x)" by (by100 simp)
            thus "x \<in> h ` (top1_S1 - {q'})" using hinv_mem by (rule image_eqI)
          next
            fix x assume "x \<in> h ` (top1_S1 - {q'})"
            then obtain s where hs: "s \<in> top1_S1 - {q'}" and hxs: "x = h s" by (by100 blast)
            have hs_S1: "s \<in> top1_S1" using hs by (by100 blast)
            have hs_nq': "s \<noteq> q'" using hs by (by100 blast)
            have hx_C: "x \<in> C \<alpha>" using hbij hs_S1 hxs unfolding bij_betw_def by (by100 blast)
            have hx_nq: "x \<noteq> q \<alpha>"
            proof
              assume "x = q \<alpha>"
              hence "h s = q \<alpha>" using hxs by (by100 simp)
              hence "h s = h q'" using hq'_eq by (by100 simp)
              hence "s = q'" using bij_betw_def hbij hs_S1 hq'_S1
                unfolding bij_betw_def inj_on_def by (by100 blast)
              thus False using hs_nq' by (by100 blast)
            qed
            show "x \<in> W \<alpha>" unfolding W_def using hx_C hx_nq by (by100 blast)
          qed
          \<comment> \<open>Now prove path connectivity of W(alpha) by transferring from S1 - {q'}.
             For x, y in W(alpha), get preimages x', y' in S1 - {q'},
             build a path in S1 - {q'} via the covering map, compose with h.\<close>
          have hW_sub: "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
          have hW_sub_X: "W \<alpha> \<subseteq> X" using hW_sub hC\<alpha>_sub by (by100 blast)
          have hTW: "is_topology_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
            by (rule subspace_topology_is_topology_on[OF hTX hW_sub_X])
          show "top1_path_connected_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))" using hTW .
          next
            fix x y assume hx: "x \<in> W \<alpha>" and hy: "y \<in> W \<alpha>"
            \<comment> \<open>Get preimages in S1 - {q'}.\<close>
            have hx_C: "x \<in> C \<alpha>" using hx unfolding W_def by (by100 blast)
            have hy_C: "y \<in> C \<alpha>" using hy unfolding W_def by (by100 blast)
            define x' where "x' = ?hinv x"
            define y' where "y' = ?hinv y"
            have hx'_S1: "x' \<in> top1_S1"
              using hbij_inv hx_C unfolding x'_def bij_betw_def by (by100 blast)
            have hy'_S1: "y' \<in> top1_S1"
              using hbij_inv hy_C unfolding y'_def bij_betw_def by (by100 blast)
            have hx'_nq: "x' \<noteq> q'"
            proof
              assume "x' = q'"
              hence "h x' = h q'" by (by100 simp)
              hence "x = q \<alpha>"
                using bij_betw_inv_into_right[OF hbij hx_C] hq'_eq
                unfolding x'_def by (by100 simp)
              thus False using hx unfolding W_def by (by100 blast)
            qed
            have hy'_nq: "y' \<noteq> q'"
            proof
              assume "y' = q'"
              hence "h y' = h q'" by (by100 simp)
              hence "y = q \<alpha>"
                using bij_betw_inv_into_right[OF hbij hy_C] hq'_eq
                unfolding y'_def by (by100 simp)
              thus False using hy unfolding W_def by (by100 blast)
            qed
            have hx'_recover: "h x' = x"
              unfolding x'_def using bij_betw_inv_into_right[OF hbij hx_C] .
            have hy'_recover: "h y' = y"
              unfolding y'_def using bij_betw_inv_into_right[OF hbij hy_C] .
            \<comment> \<open>Use covering map: get \<theta>_q, \<theta>_x, \<theta>_y with R_to_S1(\<theta>) = point.\<close>
            obtain \<theta>q where h\<theta>q: "top1_R_to_S1 \<theta>q = q'"
            proof -
              have "q' \<in> top1_S1" using hq'_S1 .
              hence heq: "fst q' ^ 2 + snd q' ^ 2 = 1" unfolding top1_S1_def by (by100 simp)
              obtain \<theta> where hcos: "fst q' = cos \<theta>" and hsin: "snd q' = sin \<theta>"
                using sincos_total_2pi[of "fst q'" "snd q'"] heq by (by100 metis)
              have "top1_R_to_S1 (\<theta> / (2 * pi)) = (cos \<theta>, sin \<theta>)"
                unfolding top1_R_to_S1_def by (by100 simp)
              hence "top1_R_to_S1 (\<theta> / (2 * pi)) = q'"
                using hcos hsin by (simp add: prod_eq_iff)
              thus ?thesis using that by (by100 blast)
            qed
            \<comment> \<open>Helper: for any a \<in> S1 - {q'}, get \<theta> \<in> (\<theta>q, \<theta>q + 1) with R_to_S1(\<theta>) = a.\<close>
            have preimage_in_interval: "\<And>a. a \<in> top1_S1 \<Longrightarrow> a \<noteq> q' \<Longrightarrow>
                \<exists>\<theta>. top1_R_to_S1 \<theta> = a \<and> \<theta>q < \<theta> \<and> \<theta> < \<theta>q + 1"
            proof -
              fix a assume ha_S1: "a \<in> top1_S1" and ha_nq: "a \<noteq> q'"
              \<comment> \<open>Get some \<theta>0 with R_to_S1(\<theta>0) = a.\<close>
              have heq_a: "fst a ^ 2 + snd a ^ 2 = 1"
                using ha_S1 unfolding top1_S1_def by (by100 simp)
              obtain \<theta>0_raw where hcos_a: "fst a = cos \<theta>0_raw" and hsin_a: "snd a = sin \<theta>0_raw"
                using sincos_total_2pi[of "fst a" "snd a"] heq_a by (by100 metis)
              define \<theta>0 where "\<theta>0 = \<theta>0_raw / (2 * pi)"
              have h\<theta>0: "top1_R_to_S1 \<theta>0 = a"
              proof -
                have "top1_R_to_S1 \<theta>0 = (cos \<theta>0_raw, sin \<theta>0_raw)"
                  unfolding top1_R_to_S1_def \<theta>0_def by (by100 simp)
                thus ?thesis using hcos_a hsin_a by (simp add: prod_eq_iff)
              qed
              \<comment> \<open>Shift \<theta>0 into (\<theta>q, \<theta>q + 1]: let k = floor(\<theta>0 - \<theta>q), \<theta>a = \<theta>0 - k.\<close>
              define k where "k = \<lfloor>\<theta>0 - \<theta>q\<rfloor>"
              define \<theta>a where "\<theta>a = \<theta>0 - of_int k"
              have h\<theta>a_R: "top1_R_to_S1 \<theta>a = a"
              proof -
                have "top1_R_to_S1 \<theta>a = top1_R_to_S1 (\<theta>0 + of_int (-k))"
                  unfolding \<theta>a_def by (by100 simp)
                also have "... = top1_R_to_S1 \<theta>0"
                  by (rule top1_R_to_S1_int_shift_early)
                finally show ?thesis using h\<theta>0 by (by100 simp)
              qed
              \<comment> \<open>\<theta>a \<in> [\<theta>q, \<theta>q + 1): by floor properties.\<close>
              have h_floor_lb: "of_int k \<le> \<theta>0 - \<theta>q"
                unfolding k_def using of_int_floor_le[of "\<theta>0 - \<theta>q"] by (by100 linarith)
              have h_floor_ub: "\<theta>0 - \<theta>q < of_int k + 1"
              proof -
                have "\<lfloor>\<theta>0 - \<theta>q\<rfloor> < \<lfloor>\<theta>0 - \<theta>q\<rfloor> + 1" by (by100 linarith)
                hence "\<theta>0 - \<theta>q < of_int (\<lfloor>\<theta>0 - \<theta>q\<rfloor> + 1)"
                  using floor_less_iff[of "\<lfloor>\<theta>0 - \<theta>q\<rfloor> + 1"] by (by100 linarith)
                thus ?thesis unfolding k_def by (by100 linarith)
              qed
              have h_floor: "\<theta>0 - \<theta>q - of_int k \<ge> 0 \<and> \<theta>0 - \<theta>q - of_int k < 1"
                using h_floor_lb h_floor_ub by (by100 linarith)
              hence h\<theta>a_ge: "\<theta>a \<ge> \<theta>q" and h\<theta>a_lt: "\<theta>a < \<theta>q + 1"
                unfolding \<theta>a_def by (by100 linarith)+
              \<comment> \<open>\<theta>a \<noteq> \<theta>q: otherwise R_to_S1(\<theta>a) = R_to_S1(\<theta>q) = q', but a \<noteq> q'.\<close>
              have h\<theta>a_ne: "\<theta>a \<noteq> \<theta>q"
              proof
                assume "\<theta>a = \<theta>q"
                hence "top1_R_to_S1 \<theta>a = top1_R_to_S1 \<theta>q" by (by100 simp)
                hence "a = q'" using h\<theta>a_R h\<theta>q by (by100 simp)
                thus False using ha_nq by (by100 blast)
              qed
              hence "\<theta>q < \<theta>a" using h\<theta>a_ge by (by100 linarith)
              thus "\<exists>\<theta>. top1_R_to_S1 \<theta> = a \<and> \<theta>q < \<theta> \<and> \<theta> < \<theta>q + 1"
                using h\<theta>a_R h\<theta>a_lt by (by100 blast)
            qed
            \<comment> \<open>For x' \<in> S1 - {q'}: get \<theta>_x \<in> (\<theta>q, \<theta>q + 1) with R_to_S1(\<theta>_x) = x'.\<close>
            obtain \<theta>x where h\<theta>x: "top1_R_to_S1 \<theta>x = x'" and h\<theta>x_range: "\<theta>q < \<theta>x \<and> \<theta>x < \<theta>q + 1"
              using preimage_in_interval[OF hx'_S1 hx'_nq] by (by100 blast)
            obtain \<theta>y where h\<theta>y: "top1_R_to_S1 \<theta>y = y'" and h\<theta>y_range: "\<theta>q < \<theta>y \<and> \<theta>y < \<theta>q + 1"
              using preimage_in_interval[OF hy'_S1 hy'_nq] by (by100 blast)
            \<comment> \<open>Build path: t \<mapsto> h(R_to_S1((1-t)*\<theta>x + t*\<theta>y)). This stays in W(alpha).\<close>
            define \<gamma> where "\<gamma> t = h (top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y))" for t
            \<comment> \<open>For t in [0,1]: (1-t)*theta_x + t*theta_y in (theta_q, theta_q+1) (convex combination).\<close>
            have h\<gamma>_range: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
                \<theta>q < (1 - t) * \<theta>x + t * \<theta>y \<and> (1 - t) * \<theta>x + t * \<theta>y < \<theta>q + 1"
            proof (intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht by (by100 blast)+
              have h1t: "0 \<le> 1 - t" using ht1 by (by100 linarith)
              \<comment> \<open>Lower bound: (1-t)*theta_x + t*theta_y >= (1-t)*theta_q + t*theta_q = theta_q,
                 with strict inequality because at least one term is strict.\<close>
              have h_lb1: "(1 - t) * \<theta>x \<ge> (1 - t) * \<theta>q"
                using h1t h\<theta>x_range by (simp add: mult_left_mono less_imp_le)
              have h_lb2: "t * \<theta>y \<ge> t * \<theta>q"
                using ht0 h\<theta>y_range by (simp add: mult_left_mono less_imp_le)
              have h_sum_lb: "(1 - t) * \<theta>x + t * \<theta>y \<ge> (1 - t) * \<theta>q + t * \<theta>q"
                using h_lb1 h_lb2 by (by100 linarith)
              have h_sum_eq: "(1 - t) * \<theta>q + t * \<theta>q = \<theta>q"
                by (simp add: algebra_simps)
              \<comment> \<open>Strict: if t < 1 then (1-t)*(theta_x - theta_q) > 0; if t > 0 then t*(theta_y - theta_q) > 0.\<close>
              have h_strict_lb: "(1 - t) * \<theta>x + t * \<theta>y > \<theta>q"
              proof (cases "t < 1")
                case True
                hence "1 - t > 0" by (by100 linarith)
                hence "(1 - t) * \<theta>x > (1 - t) * \<theta>q"
                  using h\<theta>x_range by (simp add: mult_strict_left_mono)
                thus ?thesis using h_lb2 h_sum_eq by (by100 linarith)
              next
                case False
                hence ht_eq: "t = 1" using ht1 by (by100 linarith)
                hence "t * \<theta>y > t * \<theta>q"
                  using h\<theta>y_range by (by100 simp)
                thus ?thesis using ht_eq by (by100 simp)
              qed
              \<comment> \<open>Upper bound: similar argument.\<close>
              have h_ub1: "(1 - t) * \<theta>x \<le> (1 - t) * (\<theta>q + 1)"
                using h1t h\<theta>x_range by (simp add: mult_left_mono less_imp_le)
              have h_ub2: "t * \<theta>y \<le> t * (\<theta>q + 1)"
                using ht0 h\<theta>y_range by (simp add: mult_left_mono less_imp_le)
              have h_sum_ub_eq: "(1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1) = \<theta>q + 1"
                by (simp add: algebra_simps)
              have h_strict_ub: "(1 - t) * \<theta>x + t * \<theta>y < \<theta>q + 1"
              proof (cases "t < 1")
                case True
                hence "1 - t > 0" by (by100 linarith)
                hence "(1 - t) * \<theta>x < (1 - t) * (\<theta>q + 1)"
                  using h\<theta>x_range by (simp add: mult_strict_left_mono)
                thus ?thesis using h_ub2 h_sum_ub_eq by (by100 linarith)
              next
                case False
                hence ht_eq: "t = 1" using ht1 by (by100 linarith)
                hence "t * \<theta>y < t * (\<theta>q + 1)"
                  using h\<theta>y_range by (by100 simp)
                thus ?thesis using ht_eq by (by100 simp)
              qed
              show "\<theta>q < (1 - t) * \<theta>x + t * \<theta>y \<and> (1 - t) * \<theta>x + t * \<theta>y < \<theta>q + 1"
                using h_strict_lb h_strict_ub by (by100 blast)
            qed
            \<comment> \<open>So R_to_S1((1-t)*\<theta>x + t*\<theta>y) \<noteq> q' for t \<in> [0,1].\<close>
            have h\<gamma>_avoids_q: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<noteq> q'"
            proof (intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              let ?\<theta> = "(1 - t) * \<theta>x + t * \<theta>y"
              have hrange: "\<theta>q < ?\<theta> \<and> ?\<theta> < \<theta>q + 1" using h\<gamma>_range ht by (by100 blast)
              show "top1_R_to_S1 ?\<theta> \<noteq> q'"
              proof
                assume heq: "top1_R_to_S1 ?\<theta> = q'"
                hence "top1_R_to_S1 ?\<theta> = top1_R_to_S1 \<theta>q" using h\<theta>q by (by100 simp)
                \<comment> \<open>By sin_cos_eq_iff: 2\<pi>*?\<theta> = 2\<pi>*\<theta>q + 2\<pi>*k for some integer k.\<close>
                hence "cos (2*pi*?\<theta>) = cos (2*pi*\<theta>q) \<and> sin (2*pi*?\<theta>) = sin (2*pi*\<theta>q)"
                  unfolding top1_R_to_S1_def by (by100 simp)
                hence "sin (2*pi*?\<theta>) = sin (2*pi*\<theta>q) \<and> cos (2*pi*?\<theta>) = cos (2*pi*\<theta>q)"
                  by (by100 blast)
                then obtain k :: int where hk: "2*pi*?\<theta> = 2*pi*\<theta>q + 2*pi*of_int k"
                  using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                hence "2*pi*?\<theta> - 2*pi*\<theta>q = 2*pi*of_int k" by (by100 linarith)
                hence h_diff: "2*pi*(?\<theta> - \<theta>q) = 2*pi*of_int k"
                  by (simp add: algebra_simps)
                hence "?\<theta> - \<theta>q = of_int k" using pi_gt_zero by (by100 simp)
                \<comment> \<open>But ?\<theta> - \<theta>q \<in> (0, 1), so k must be 0, contradiction.\<close>
                moreover have "?\<theta> - \<theta>q > 0 \<and> ?\<theta> - \<theta>q < 1" using hrange by (by100 linarith)
                ultimately have hk_bounds: "of_int k > (0::real) \<and> of_int k < (1::real)" by (by100 linarith)
                hence "k > 0 \<and> k < 1" by (by100 linarith)
                thus False by (by100 linarith)
              qed
            qed
            \<comment> \<open>So \<gamma> maps [0,1] into S1 - {q'}, hence into W(alpha).\<close>
            have h\<gamma>_in_S1: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<in> top1_S1"
            proof (intro allI impI)
              fix t :: real assume "0 \<le> t \<and> t \<le> 1"
              show "top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<in> top1_S1"
                unfolding top1_R_to_S1_def top1_S1_def
                using sin_squared_eq by (by100 simp)
            qed
            have h\<gamma>_in_S1_minus: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
                top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<in> top1_S1 - {q'}"
            proof (intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              show "top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<in> top1_S1 - {q'}"
                using h\<gamma>_in_S1[rule_format, OF ht] h\<gamma>_avoids_q[rule_format, OF ht] by (by100 blast)
            qed
            have h\<gamma>_in_W: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> \<gamma> t \<in> W \<alpha>"
            proof (intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              have "top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y) \<in> top1_S1 - {q'}"
                using h\<gamma>_in_S1_minus ht by (by100 blast)
              hence "h (top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y)) \<in> h ` (top1_S1 - {q'})"
                by (by100 blast)
              thus "\<gamma> t \<in> W \<alpha>" unfolding \<gamma>_def hW_eq by (by100 blast)
            qed
            \<comment> \<open>gamma is continuous: composition of continuous functions.\<close>
            have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (W \<alpha>) (subspace_topology X TX (W \<alpha>)) \<gamma>"
            proof -
              \<comment> \<open>Step 1: linear map t \<mapsto> (1-t)*\<theta>x + t*\<theta>y is continuous [0,1] \<rightarrow> R.\<close>
              have hlin_cont_on: "continuous_on UNIV (\<lambda>t::real. (1 - t) * \<theta>x + t * \<theta>y)"
                by (intro continuous_intros)
              have hlin_map: "\<And>t::real. t \<in> top1_unit_interval \<Longrightarrow>
                  (1 - t) * \<theta>x + t * \<theta>y \<in> (UNIV::real set)" by (by100 blast)
              have hlin: "top1_continuous_map_on top1_unit_interval
                  (subspace_topology UNIV top1_open_sets top1_unit_interval)
                  (UNIV::real set) (subspace_topology UNIV top1_open_sets UNIV)
                  (\<lambda>t. (1 - t) * \<theta>x + t * \<theta>y)"
                by (rule top1_continuous_map_on_real_subspace_open_sets[OF hlin_map hlin_cont_on])
              have hUNIV_sub: "subspace_topology (UNIV::real set) (top1_open_sets::real set set) UNIV = top1_open_sets"
                by (rule subspace_topology_UNIV_self)
              have hlin': "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (UNIV::real set) top1_open_sets (\<lambda>t. (1 - t) * \<theta>x + t * \<theta>y)"
                using hlin unfolding top1_unit_interval_topology_def hUNIV_sub by (by100 simp)
              \<comment> \<open>Step 2: R_to_S1 is continuous R \<rightarrow> S1.\<close>
              have hR_S1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                  top1_S1 top1_S1_topology top1_R_to_S1"
                by (rule top1_covering_map_on_continuous[OF Theorem_53_1])
              \<comment> \<open>Step 3: compose linear + R_to_S1: [0,1] \<rightarrow> S1.\<close>
              have hcomp1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_S1 top1_S1_topology (top1_R_to_S1 \<circ> (\<lambda>t. (1 - t) * \<theta>x + t * \<theta>y))"
                by (rule top1_continuous_map_on_comp[OF hlin' hR_S1])
              have hcomp1': "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_S1 top1_S1_topology (\<lambda>t. top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y))"
              proof -
                have heq: "\<forall>t\<in>top1_unit_interval.
                    (top1_R_to_S1 \<circ> (\<lambda>t. (1 - t) * \<theta>x + t * \<theta>y)) t =
                    (\<lambda>t. top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y)) t"
                  by (by100 simp)
                thus ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq]] hcomp1 by (by100 blast)
              qed
              \<comment> \<open>Step 4: compose with h: [0,1] \<rightarrow> C(alpha).\<close>
              have hcomp2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>))
                  (h \<circ> (\<lambda>t. top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y)))"
                by (rule top1_continuous_map_on_comp[OF hcomp1' hcont_h])
              have hcomp2': "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) \<gamma>"
              proof -
                have heq2: "\<forall>t\<in>top1_unit_interval.
                    (h \<circ> (\<lambda>t. top1_R_to_S1 ((1 - t) * \<theta>x + t * \<theta>y))) t = \<gamma> t"
                  unfolding \<gamma>_def by (by100 simp)
                thus ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq2]] hcomp2 by (by100 blast)
              qed
              \<comment> \<open>Step 5: shrink codomain from C(alpha) to W(alpha).\<close>
              have h\<gamma>_img: "\<gamma> ` top1_unit_interval \<subseteq> W \<alpha>"
              proof (rule image_subsetI)
                fix t assume "t \<in> top1_unit_interval"
                hence "0 \<le> t \<and> t \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                thus "\<gamma> t \<in> W \<alpha>" using h\<gamma>_in_W by (by100 blast)
              qed
              have hW_sub_C: "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
              have h\<gamma>_shrunk: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (W \<alpha>) (subspace_topology (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (W \<alpha>)) \<gamma>"
                by (rule top1_continuous_map_on_codomain_shrink[OF hcomp2' h\<gamma>_img hW_sub_C])
              \<comment> \<open>By subspace_topology_trans: subspace C(alpha) (subspace X TX C(alpha)) W(alpha)
                 = subspace X TX W(alpha).\<close>
              have hsub_trans: "subspace_topology (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (W \<alpha>)
                  = subspace_topology X TX (W \<alpha>)"
                by (rule subspace_topology_trans[OF hW_sub_C])
              show ?thesis using h\<gamma>_shrunk hsub_trans by (by100 simp)
            qed
            \<comment> \<open>\<gamma> 0 = x, \<gamma> 1 = y.\<close>
            have h\<gamma>_0: "\<gamma> 0 = x"
              unfolding \<gamma>_def using h\<theta>x hx'_recover by (by100 simp)
            have h\<gamma>_1: "\<gamma> 1 = y"
              unfolding \<gamma>_def using h\<theta>y hy'_recover by (by100 simp)
            have "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) x y \<gamma>"
              unfolding top1_is_path_on_def using h\<gamma>_cont h\<gamma>_0 h\<gamma>_1 by (by100 blast)
            thus "\<exists>f. top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) x y f"
              by (by100 blast)
          qed
        qed
        \<comment> \<open>Helper: p \<in> W \<alpha> for all \<alpha> < n.\<close>
        have hp_W: "\<forall>\<alpha>\<in>{..<n}. p \<in> W \<alpha>"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
          have "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
          moreover have "p \<noteq> q \<alpha>" using hq h\<alpha> by (by100 blast)
          ultimately show "p \<in> W \<alpha>" unfolding W_def by (by100 blast)
        qed
        \<comment> \<open>Helper: W \<alpha> \<subseteq> C \<alpha> \<subseteq> X.\<close>
        have hW_sub_C: "\<forall>\<alpha>\<in>{..<n}. W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
        have hW_sub_X: "\<forall>\<alpha>\<in>{..<n}. W \<alpha> \<subseteq> X"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
          have "W \<alpha> \<subseteq> C \<alpha>" using hW_sub_C h\<alpha> by (by100 blast)
          moreover have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
          ultimately show "W \<alpha> \<subseteq> X" by (by100 blast)
        qed
        \<comment> \<open>Helper: U_def \<subseteq> X and V_def \<subseteq> X.\<close>
        have hU_sub: "U_def \<subseteq> X"
        proof -
          have "(\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<subseteq> X" using hX'_sub by (by100 blast)
          moreover have "W (n-1) \<subseteq> X" using hW_sub_X hn1_in by (by100 blast)
          ultimately show ?thesis unfolding U_def_def by (by100 blast)
        qed
        have hV_sub: "V_def \<subseteq> X"
        proof -
          have "(\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>) \<subseteq> X"
          proof (rule UN_least)
            fix \<alpha> assume "\<alpha> \<in> {..<(n-1)}"
            hence "\<alpha> \<in> {..<n}" using hn2 by (by100 simp)
            thus "W \<alpha> \<subseteq> X" using hW_sub_X by (by100 blast)
          qed
          moreover have "C (n-1) \<subseteq> X" using hCn_sub .
          ultimately show ?thesis unfolding V_def_def by (by100 blast)
        qed
        \<comment> \<open>Helper: p \<in> U_def and p \<in> V_def.\<close>
        have hp_U: "p \<in> U_def" unfolding U_def_def using hp_X' by (by100 blast)
        have hp_V: "p \<in> V_def" unfolding V_def_def using hp_Cn by (by100 blast)
        \<comment> \<open>Helper: C \<alpha> \<subseteq> U_def for \<alpha> < n-1.\<close>
        have hC_sub_U: "\<forall>\<alpha>\<in>{..<(n-1)}. C \<alpha> \<subseteq> U_def"
          unfolding U_def_def by (by100 blast)
        \<comment> \<open>Helper: W(n-1) \<subseteq> U_def.\<close>
        have hWn_sub_U: "W (n-1) \<subseteq> U_def" unfolding U_def_def by (by100 blast)
        \<comment> \<open>Helper: W \<alpha> \<subseteq> V_def for \<alpha> < n-1.\<close>
        have hW_sub_V: "\<forall>\<alpha>\<in>{..<(n-1)}. W \<alpha> \<subseteq> V_def"
          unfolding V_def_def by (by100 blast)
        \<comment> \<open>Helper: C(n-1) \<subseteq> V_def.\<close>
        have hCn_sub_V: "C (n-1) \<subseteq> V_def" unfolding V_def_def by (by100 blast)
        \<comment> \<open>U_def \<inter> V_def = \<Union>{W \<alpha> | \<alpha> < n}.\<close>
        have hUV_eq: "U_def \<inter> V_def = (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)"
        proof (intro set_eqI iffI)
          fix x assume hx: "x \<in> U_def \<inter> V_def"
          hence hxU: "x \<in> U_def" and hxV: "x \<in> V_def" by (by100 blast)+
          show "x \<in> (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)"
          proof -
            from hxU have "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<or> x \<in> W (n-1)"
              unfolding U_def_def by (by100 blast)
            thus ?thesis
            proof
              assume "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>)"
              then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<(n-1)}" and hx\<alpha>: "x \<in> C \<alpha>" by (by100 blast)
              have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
              \<comment> \<open>x \<in> V_def, so x \<in> (\<Union>\<beta><n-1. W \<beta>) \<union> C(n-1).
                 If x \<in> C(n-1), then x \<in> C \<alpha> \<inter> C(n-1) = {p}, so x = p.
                 p \<in> W \<alpha> (since p \<noteq> q \<alpha>).\<close>
              show ?thesis
              proof (cases "x \<in> (\<Union>\<beta>\<in>{..<(n-1)}. W \<beta>)")
                case True
                then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hx\<beta>: "x \<in> W \<beta>" by (by100 blast)
                have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
                thus ?thesis using hx\<beta> by (by100 blast)
              next
                case False
                hence "x \<in> C (n-1)" using hxV unfolding V_def_def by (by100 blast)
                hence "x \<in> C \<alpha> \<inter> C (n-1)" using hx\<alpha> by (by100 blast)
                hence "x = p" using hC_inter h\<alpha>n hn1_in
                proof -
                  have h\<alpha>_ne: "\<alpha> \<noteq> n - 1" using h\<alpha> by (by100 simp)
                  have "C \<alpha> \<inter> C (n-1) = {p}" using hC_inter h\<alpha>n hn1_in h\<alpha>_ne by (by100 blast)
                  thus ?thesis using \<open>x \<in> C \<alpha> \<inter> C (n-1)\<close> by (by100 blast)
                qed
                hence "x \<in> W \<alpha>" using hp_W h\<alpha>n by (by100 blast)
                thus ?thesis using h\<alpha>n by (by100 blast)
              qed
            next
              assume "x \<in> W (n-1)"
              thus ?thesis using hn1_in by (by100 blast)
            qed
          qed
        next
          fix x assume hx: "x \<in> (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)"
          then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<n}" and hx\<alpha>: "x \<in> W \<alpha>" by (by100 blast)
          show "x \<in> U_def \<inter> V_def"
          proof (cases "\<alpha> \<in> {..<(n-1)}")
            case True
            \<comment> \<open>W \<alpha> \<subseteq> C \<alpha> \<subseteq> U_def, and W \<alpha> \<subseteq> V_def.\<close>
            have "x \<in> U_def" using hx\<alpha> hW_sub_C h\<alpha> hC_sub_U True by (by100 blast)
            moreover have "x \<in> V_def" using hx\<alpha> hW_sub_V True by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          next
            case False
            hence h\<alpha>_eq: "\<alpha> = n - 1" using h\<alpha> by (by100 simp)
            \<comment> \<open>W(n-1) \<subseteq> U_def, and W(n-1) \<subseteq> C(n-1) \<subseteq> V_def.\<close>
            have "x \<in> U_def" using hx\<alpha> hWn_sub_U h\<alpha>_eq by (by100 blast)
            moreover have "x \<in> V_def"
            proof -
              have "x \<in> W \<alpha>" using hx\<alpha> by (by100 blast)
              hence "x \<in> C \<alpha>" using hW_sub_C h\<alpha> by (by100 blast)
              hence "x \<in> C (n-1)" using h\<alpha>_eq by (by100 simp)
              thus ?thesis using hCn_sub_V by (by100 blast)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
        qed
        \<comment> \<open>Simply connected proof for U_def \<inter> V_def = \<Union>W(\<alpha>).\<close>
        have hUV_sub: "U_def \<inter> V_def \<subseteq> X"
          using hU_sub hV_sub by (by100 blast)
        have hTUV: "is_topology_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def))"
          by (rule subspace_topology_is_topology_on[OF hTX hUV_sub])
        have hp_UV: "p \<in> U_def \<inter> V_def"
          using hp_U hp_V by (by100 blast)
        show "top1_simply_connected_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def))"
        proof (rule top1_simply_connected_from_one_point[OF hTUV _ hp_UV])
          \<comment> \<open>Part 1: U_def \<inter> V_def is path-connected.\<close>
          show "top1_path_connected_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def))"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def))"
              using hTUV .
          next
            fix x y assume hx: "x \<in> U_def \<inter> V_def" and hy: "y \<in> U_def \<inter> V_def"
            \<comment> \<open>x \<in> \<Union>W(\<alpha>), so x \<in> W(\<alpha>) for some \<alpha>. Get path x \<rightarrow> p in W(\<alpha>).\<close>
            have hx_W: "x \<in> (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)" using hx hUV_eq by (by100 blast)
            then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<n}" and hx\<alpha>: "x \<in> W \<alpha>" by (by100 blast)
            have hp\<alpha>: "p \<in> W \<alpha>" using hp_W h\<alpha> by (by100 blast)
            obtain f1 where hf1: "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) x p f1"
              using hW_pc h\<alpha> hx\<alpha> hp\<alpha> unfolding top1_path_connected_on_def by (by100 blast)
            \<comment> \<open>Lift path from W(\<alpha>) to U_def \<inter> V_def.\<close>
            have hcont_f1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (W \<alpha>) (subspace_topology X TX (W \<alpha>)) f1"
              using hf1 unfolding top1_is_path_on_def by (by100 blast)
            have hW\<alpha>_sub_UV: "W \<alpha> \<subseteq> U_def \<inter> V_def"
              using hUV_eq h\<alpha> by (by100 blast)
            have hcont_UV1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) f1"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f1 hW\<alpha>_sub_UV hUV_sub])
            have hf1_0: "f1 0 = x" and hf1_1: "f1 1 = p"
              using hf1 unfolding top1_is_path_on_def by (by100 blast)+
            have hpath_xp: "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) x p f1"
              unfolding top1_is_path_on_def using hcont_UV1 hf1_0 hf1_1 by (by100 blast)
            \<comment> \<open>Similarly y \<rightarrow> p.\<close>
            have hy_W: "y \<in> (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)" using hy hUV_eq by (by100 blast)
            then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<n}" and hy\<beta>: "y \<in> W \<beta>" by (by100 blast)
            have hp\<beta>: "p \<in> W \<beta>" using hp_W h\<beta> by (by100 blast)
            obtain f2 where hf2: "top1_is_path_on (W \<beta>) (subspace_topology X TX (W \<beta>)) p y f2"
              using hW_pc h\<beta> hp\<beta> hy\<beta> unfolding top1_path_connected_on_def by (by100 blast)
            have hcont_f2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (W \<beta>) (subspace_topology X TX (W \<beta>)) f2"
              using hf2 unfolding top1_is_path_on_def by (by100 blast)
            have hW\<beta>_sub_UV: "W \<beta> \<subseteq> U_def \<inter> V_def"
              using hUV_eq h\<beta> by (by100 blast)
            have hcont_UV2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) f2"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f2 hW\<beta>_sub_UV hUV_sub])
            have hf2_0: "f2 0 = p" and hf2_1: "f2 1 = y"
              using hf2 unfolding top1_is_path_on_def by (by100 blast)+
            have hpath_py: "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p y f2"
              unfolding top1_is_path_on_def using hcont_UV2 hf2_0 hf2_1 by (by100 blast)
            \<comment> \<open>Concatenate: x \<rightarrow> p \<rightarrow> y.\<close>
            show "\<exists>f. top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) x y f"
              using top1_is_path_on_append[OF hTUV hpath_xp hpath_py] by (by100 blast)
          qed
        next
          \<comment> \<open>Part 2: Every loop at p in U_def \<inter> V_def is nulhomotopic.
             Key idea: Each W(\<alpha>) is simply connected (homeomorphic to R via
             the covering map parameterization). Any loop at p in \<Union>W(\<alpha>) can
             be decomposed into sub-loops each staying in a single W(\<alpha>).
             Each sub-loop is nulhomotopic since W(\<alpha>) is simply connected.
             The product of nulhomotopic loops is nulhomotopic.\<close>
          \<comment> \<open>Helper: Each W(\<alpha>) is simply connected.
             W(\<alpha>) is homeomorphic to an open interval in R (via the covering map
             parameterization). R is simply connected. The straight-line homotopy
             in R stays within the open interval, hence transfers to W(\<alpha>).\<close>
          have hW_sc: "\<forall>\<alpha>\<in>{..<n}. top1_simply_connected_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
            have hW\<alpha>_sub: "W \<alpha> \<subseteq> X" using hW_sub_X h\<alpha> by (by100 blast)
            have hTW\<alpha>: "is_topology_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
              by (rule subspace_topology_is_topology_on[OF hTX hW\<alpha>_sub])
            have hp\<alpha>: "p \<in> W \<alpha>" using hp_W h\<alpha> by (by100 blast)
            have hW_pc\<alpha>: "top1_path_connected_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
              using hW_pc h\<alpha> by (by100 blast)
            show "top1_simply_connected_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
            proof (rule top1_simply_connected_from_one_point[OF hTW\<alpha> hW_pc\<alpha> hp\<alpha>])
              \<comment> \<open>Every loop at p in W(\<alpha>) is nulhomotopic.
                 Use the covering map parameterization: a loop at p maps to a
                 loop in the interval (\<theta>_q, \<theta>_q + 1) which contracts via
                 straight-line homotopy.\<close>
              show "\<forall>f. top1_is_loop_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p f \<longrightarrow>
                  top1_path_homotopic_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p p f (top1_constant_path p)"
              proof (intro allI impI)
                fix f assume hloop: "top1_is_loop_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p f"
                \<comment> \<open>Get homeomorphism h: S1 -> C(\<alpha>) and covering map parameterization.\<close>
                obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
                  using hC_props h\<alpha> by (by100 blast)
                have hbij: "bij_betw h top1_S1 (C \<alpha>)"
                  using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                have hcont_h: "top1_continuous_map_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h"
                  using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                let ?hinv = "inv_into top1_S1 h"
                have hhinv: "top1_homeomorphism_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))
                    top1_S1 top1_S1_topology ?hinv"
                  by (rule homeomorphism_inverse[OF hh])
                have hbij_inv: "bij_betw ?hinv (C \<alpha>) top1_S1"
                  using hhinv unfolding top1_homeomorphism_on_def by (by100 blast)
                have hcont_hinv: "top1_continuous_map_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))
                    top1_S1 top1_S1_topology ?hinv"
                  using hhinv unfolding top1_homeomorphism_on_def by (by100 blast)
                \<comment> \<open>q' = h^{-1}(q(\<alpha>)), the removed point in S1.\<close>
                have hq_in: "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
                define q' where "q' = ?hinv (q \<alpha>)"
                have hq'_S1: "q' \<in> top1_S1"
                  using hbij_inv hq_in unfolding q'_def bij_betw_def by (by100 blast)
                \<comment> \<open>p' = h^{-1}(p), the basepoint in S1.\<close>
                have hp_C: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                define p' where "p' = ?hinv p"
                have hp'_S1: "p' \<in> top1_S1"
                  using hbij_inv hp_C unfolding p'_def bij_betw_def by (by100 blast)
                have hp'_ne_q': "p' \<noteq> q'"
                proof
                  assume "p' = q'"
                  hence "?hinv p = ?hinv (q \<alpha>)" unfolding p'_def q'_def .
                  hence "h (?hinv p) = h (?hinv (q \<alpha>))" by (by100 simp)
                  hence "p = q \<alpha>"
                    using bij_betw_inv_into_right[OF hbij hp_C]
                          bij_betw_inv_into_right[OF hbij hq_in] by (by100 simp)
                  thus False using hq h\<alpha> by (by100 blast)
                qed
                \<comment> \<open>Get angle parameters for q' and p'.\<close>
                obtain \<theta>q where h\<theta>q: "top1_R_to_S1 \<theta>q = q'"
                proof -
                  have heq: "fst q' ^ 2 + snd q' ^ 2 = 1" using hq'_S1 unfolding top1_S1_def by (by100 simp)
                  obtain \<theta> where "fst q' = cos \<theta>" "snd q' = sin \<theta>"
                    using sincos_total_2pi heq by (by100 metis)
                  hence "top1_R_to_S1 (\<theta> / (2 * pi)) = q'"
                    unfolding top1_R_to_S1_def by (simp add: prod_eq_iff)
                  thus ?thesis using that by (by100 blast)
                qed
                obtain \<theta>p where h\<theta>p: "top1_R_to_S1 \<theta>p = p'" and h\<theta>p_range: "\<theta>q < \<theta>p \<and> \<theta>p < \<theta>q + 1"
                proof -
                  have heq: "fst p' ^ 2 + snd p' ^ 2 = 1" using hp'_S1 unfolding top1_S1_def by (by100 simp)
                  obtain \<theta>0_raw where hcos: "fst p' = cos \<theta>0_raw" and hsin: "snd p' = sin \<theta>0_raw"
                    using sincos_total_2pi heq by (by100 metis)
                  define \<theta>0 where "\<theta>0 = \<theta>0_raw / (2 * pi)"
                  have h\<theta>0: "top1_R_to_S1 \<theta>0 = p'"
                    unfolding top1_R_to_S1_def \<theta>0_def using hcos hsin by (simp add: prod_eq_iff)
                  define k where "k = \<lfloor>\<theta>0 - \<theta>q\<rfloor>"
                  define \<theta>a where "\<theta>a = \<theta>0 - of_int k"
                  have h\<theta>a_R: "top1_R_to_S1 \<theta>a = p'"
                  proof -
                    have "top1_R_to_S1 \<theta>a = top1_R_to_S1 (\<theta>0 + of_int (-k))"
                      unfolding \<theta>a_def by (by100 simp)
                    also have "... = top1_R_to_S1 \<theta>0" by (rule top1_R_to_S1_int_shift_early)
                    finally show ?thesis using h\<theta>0 by (by100 simp)
                  qed
                  have h_floor_lb: "of_int k \<le> \<theta>0 - \<theta>q" unfolding k_def using of_int_floor_le by (by100 linarith)
                  have h_floor_ub: "\<theta>0 - \<theta>q < of_int k + 1"
                  proof -
                    have "\<lfloor>\<theta>0 - \<theta>q\<rfloor> < \<lfloor>\<theta>0 - \<theta>q\<rfloor> + 1" by (by100 linarith)
                    thus ?thesis unfolding k_def using floor_less_iff by (by100 linarith)
                  qed
                  have h\<theta>a_ge: "\<theta>a \<ge> \<theta>q" and h\<theta>a_lt: "\<theta>a < \<theta>q + 1"
                    unfolding \<theta>a_def using h_floor_lb h_floor_ub by (by100 linarith)+
                  have h\<theta>a_ne: "\<theta>a \<noteq> \<theta>q"
                  proof
                    assume "\<theta>a = \<theta>q"
                    hence "top1_R_to_S1 \<theta>a = top1_R_to_S1 \<theta>q" by (by100 simp)
                    hence "p' = q'" using h\<theta>a_R h\<theta>q by (by100 simp)
                    thus False using hp'_ne_q' by (by100 blast)
                  qed
                  hence "\<theta>q < \<theta>a" using h\<theta>a_ge by (by100 linarith)
                  thus ?thesis using that h\<theta>a_R h\<theta>a_lt by (by100 blast)
                qed
                \<comment> \<open>The loop f maps I to W(\<alpha>) with f(0) = f(1) = p.
                   Compose with h^{-1} to get a loop in S1 - {q'}.
                   Lift to get a path in (\<theta>_q, \<theta>_q + 1) starting and ending at \<theta>_p.
                   Use straight-line homotopy in R to contract to constant \<theta>_p.
                   Push forward through h \<circ> R_to_S1 to get null-homotopy in W(\<alpha>).\<close>
                \<comment> \<open>Step A: h^{-1} \<circ> f is a loop in S1 at p'.\<close>
                have hf_path: "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p p f"
                  using hloop unfolding top1_is_loop_on_def .
                have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    (W \<alpha>) (subspace_topology X TX (W \<alpha>)) f"
                  using hf_path unfolding top1_is_path_on_def by (by100 blast)
                have hf0: "f 0 = p" and hf1: "f 1 = p"
                  using hf_path unfolding top1_is_path_on_def by (by100 blast)+
                \<comment> \<open>f maps to W \<alpha> \<subseteq> C \<alpha>, so composing with h^{-1} gives a path in S1.\<close>
                have hW_sub_C_here: "W \<alpha> \<subseteq> C \<alpha>" using hW_sub_C h\<alpha> by (by100 blast)
                have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                have hTC\<alpha>: "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
                  by (rule subspace_topology_is_topology_on[OF hTX hC\<alpha>_sub])
                \<comment> \<open>Enlarge codomain of f from W \<alpha> to C \<alpha>.\<close>
                have hf_C: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) f"
                  by (rule top1_continuous_map_on_codomain_enlarge[OF hf_cont hW_sub_C_here hC\<alpha>_sub])
                \<comment> \<open>h^{-1} \<circ> f is continuous [0,1] \<rightarrow> S1.\<close>
                have hhinvf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    top1_S1 top1_S1_topology (?hinv \<circ> f)"
                  by (rule top1_continuous_map_on_comp[OF hf_C hcont_hinv])
                have hhinvf_0: "(?hinv \<circ> f) 0 = p'"
                  unfolding p'_def using hf0 by (by100 simp)
                have hhinvf_1: "(?hinv \<circ> f) 1 = p'"
                  unfolding p'_def using hf1 by (by100 simp)
                have hhinvf_path: "top1_is_path_on top1_S1 top1_S1_topology p' p' (?hinv \<circ> f)"
                  unfolding top1_is_path_on_def using hhinvf_cont hhinvf_0 hhinvf_1 by (by100 blast)
                \<comment> \<open>Step B: Lift h^{-1} \<circ> f to a path g_tilde in R starting at \<theta>p.\<close>
                have hTS1: "is_topology_on top1_S1 top1_S1_topology"
                  using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
                have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
                  by (rule top1_open_sets_is_topology_on_UNIV)
                have h\<theta>p_UNIV: "\<theta>p \<in> (UNIV::real set)" by (by100 blast)
                have hR_to_S1_\<theta>p: "top1_R_to_S1 \<theta>p = p'" using h\<theta>p by (by100 blast)
                obtain g_tilde where hgtilde_path: "top1_is_path_on (UNIV::real set) top1_open_sets
                    \<theta>p (g_tilde 1) g_tilde"
                    and hgtilde_proj: "\<forall>s\<in>I_set. top1_R_to_S1 (g_tilde s) = (?hinv \<circ> f) s"
                  using Lemma_54_1_path_lifting[OF Theorem_53_1 h\<theta>p_UNIV hR_to_S1_\<theta>p
                      hhinvf_path hTS1 hTR] by (by100 blast)
                have hgtilde_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    (UNIV::real set) top1_open_sets g_tilde"
                  using hgtilde_path unfolding top1_is_path_on_def by (by100 blast)
                have hgtilde_0: "g_tilde 0 = \<theta>p"
                  using hgtilde_path unfolding top1_is_path_on_def by (by100 blast)
                \<comment> \<open>Step C: Show g_tilde stays in (\<theta>q, \<theta>q + 1).
                   Key: f maps to W \<alpha> = C \<alpha> - {q \<alpha>}, so h^{-1}(f(s)) \<in> S1 - {q'}.
                   Hence R_to_S1(g_tilde(s)) \<noteq> q' for all s.
                   By connectedness + IVT, g_tilde stays in (\<theta>q, \<theta>q + 1).\<close>
                have hgtilde_avoids_q: "\<forall>s\<in>I_set. top1_R_to_S1 (g_tilde s) \<noteq> q'"
                proof (intro ballI)
                  fix s assume hs: "s \<in> I_set"
                  have "top1_R_to_S1 (g_tilde s) = (?hinv \<circ> f) s" using hgtilde_proj hs by (by100 blast)
                  also have "... = ?hinv (f s)" by (by100 simp)
                  finally have hR: "top1_R_to_S1 (g_tilde s) = ?hinv (f s)" .
                  \<comment> \<open>f(s) \<in> W \<alpha> = C \<alpha> - {q \<alpha>}, so f(s) \<noteq> q \<alpha>.\<close>
                  have hfs_W: "f s \<in> W \<alpha>"
                    using hf_cont hs unfolding top1_continuous_map_on_def by (by100 blast)
                  hence "f s \<noteq> q \<alpha>" unfolding W_def by (by100 blast)
                  hence "?hinv (f s) \<noteq> ?hinv (q \<alpha>)"
                  proof -
                    have hfs_C: "f s \<in> C \<alpha>" using hfs_W hW_sub_C_here by (by100 blast)
                    assume hne: "f s \<noteq> q \<alpha>"
                    show "?hinv (f s) \<noteq> ?hinv (q \<alpha>)"
                    proof
                      assume "?hinv (f s) = ?hinv (q \<alpha>)"
                      hence "h (?hinv (f s)) = h (?hinv (q \<alpha>))" by (by100 simp)
                      hence "f s = q \<alpha>"
                        using bij_betw_inv_into_right[OF hbij hfs_C]
                              bij_betw_inv_into_right[OF hbij hq_in] by (by100 simp)
                      thus False using hne by (by100 blast)
                    qed
                  qed
                  hence "?hinv (f s) \<noteq> q'" unfolding q'_def .
                  thus "top1_R_to_S1 (g_tilde s) \<noteq> q'" using hR by (by100 simp)
                qed
                \<comment> \<open>Get continuous_on for g_tilde on I_set (needed for IVT).\<close>
                have hgtilde_cont_on: "continuous_on I_set g_tilde"
                proof -
                  have h: "top1_continuous_map_on I_set I_top UNIV top1_open_sets g_tilde"
                    using hgtilde_cont unfolding top1_unit_interval_topology_def .
                  show ?thesis unfolding continuous_on_open_invariant
                  proof (intro allI impI)
                    fix B :: "real set" assume hBo: "open B"
                    have "B \<in> top1_open_sets" using hBo unfolding top1_open_sets_def by (by100 blast)
                    hence "{s \<in> I_set. g_tilde s \<in> B} \<in> I_top"
                      using h unfolding top1_continuous_map_on_def by (by100 blast)
                    hence "{s \<in> I_set. g_tilde s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
                      unfolding top1_unit_interval_topology_def .
                    then obtain W where hW: "W \<in> top1_open_sets" and heq: "{s \<in> I_set. g_tilde s \<in> B} = I_set \<inter> W"
                      unfolding subspace_topology_def by (by100 blast)
                    have "open W" using hW unfolding top1_open_sets_def by (by100 blast)
                    moreover have "W \<inter> I_set = g_tilde -` B \<inter> I_set" using heq by (by100 blast)
                    ultimately show "\<exists>A. open A \<and> A \<inter> I_set = g_tilde -` B \<inter> I_set" by (by100 blast)
                  qed
                qed
                \<comment> \<open>g_tilde stays in (\<theta>q, \<theta>q + 1): since g_tilde(0) = \<theta>p \<in> (\<theta>q, \<theta>q+1),
                   and g_tilde is continuous, and g_tilde never hits \<theta>q + k (any integer k)
                   (because R_to_S1 would equal q'), by IVT g_tilde stays in (\<theta>q, \<theta>q + 1).\<close>
                \<comment> \<open>g_tilde avoids \<theta>q + k for ALL integers k.\<close>
                have hgtilde_avoids_lattice: "\<forall>s\<in>I_set. \<forall>k::int. g_tilde s \<noteq> \<theta>q + of_int k"
                proof (intro ballI allI)
                  fix s :: real and k :: int assume hs: "s \<in> I_set"
                  show "g_tilde s \<noteq> \<theta>q + of_int k"
                  proof
                    assume heq: "g_tilde s = \<theta>q + of_int k"
                    hence "top1_R_to_S1 (g_tilde s) = top1_R_to_S1 (\<theta>q + of_int k)" by (by100 simp)
                    also have "... = top1_R_to_S1 \<theta>q" by (rule top1_R_to_S1_int_shift_early)
                    also have "... = q'" using h\<theta>q .
                    finally have "top1_R_to_S1 (g_tilde s) = q'" .
                    thus False using hgtilde_avoids_q hs by (by100 blast)
                  qed
                qed
                have hgtilde_range: "\<forall>s\<in>I_set. \<theta>q < g_tilde s \<and> g_tilde s < \<theta>q + 1"
                proof (intro ballI)
                  fix s assume hs: "s \<in> I_set"
                  have hs_range: "0 \<le> s \<and> s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 simp)
                  \<comment> \<open>Lower bound: g_tilde(s) > \<theta>q.\<close>
                  have h_lb: "g_tilde s > \<theta>q"
                  proof (rule ccontr)
                    assume "\<not> \<theta>q < g_tilde s"
                    hence hle: "g_tilde s \<le> \<theta>q" by (by100 linarith)
                    \<comment> \<open>g_tilde(0) = \<theta>p > \<theta>q and g_tilde(s) \<le> \<theta>q.
                       By IVT, \<exists>s' \<in> [0, s] with g_tilde(s') = \<theta>q.\<close>
                    have hg0: "g_tilde 0 = \<theta>p" using hgtilde_0 .
                    have hg0_gt: "g_tilde 0 > \<theta>q" using hg0 h\<theta>p_range by (by100 linarith)
                    have hs_le1: "s \<le> 1" using hs_range by (by100 blast)
                    have h0_le_s: "0 \<le> s" using hs_range by (by100 blast)
                    have h_cont_seg: "continuous_on {0..s} g_tilde"
                    proof (rule continuous_on_subset[OF hgtilde_cont_on])
                      show "{0..s} \<subseteq> I_set" using hs_range unfolding top1_unit_interval_def by (by100 auto)
                    qed
                    have "g_tilde s \<le> \<theta>q" using hle .
                    moreover have "\<theta>q \<le> g_tilde 0" using hg0_gt by (by100 linarith)
                    ultimately obtain s' where hs': "0 \<le> s' \<and> s' \<le> s" and hgs': "g_tilde s' = \<theta>q"
                      using IVT2'[OF _ _ h0_le_s h_cont_seg] by (by100 blast)
                    have "s' \<in> I_set" using hs' hs_range unfolding top1_unit_interval_def by (by100 auto)
                    hence "g_tilde s' \<noteq> \<theta>q + of_int 0"
                      using hgtilde_avoids_lattice by (by100 blast)
                    hence "g_tilde s' \<noteq> \<theta>q" by (by100 simp)
                    thus False using hgs' by (by100 blast)
                  qed
                  \<comment> \<open>Upper bound: g_tilde(s) < \<theta>q + 1.\<close>
                  have h_ub: "g_tilde s < \<theta>q + 1"
                  proof (rule ccontr)
                    assume "\<not> g_tilde s < \<theta>q + 1"
                    hence hge: "g_tilde s \<ge> \<theta>q + 1" by (by100 linarith)
                    have hg0: "g_tilde 0 = \<theta>p" using hgtilde_0 .
                    have hg0_lt: "g_tilde 0 < \<theta>q + 1" using hg0 h\<theta>p_range by (by100 linarith)
                    have h0_le_s: "0 \<le> s" using hs_range by (by100 blast)
                    have h_cont_seg: "continuous_on {0..s} g_tilde"
                    proof (rule continuous_on_subset[OF hgtilde_cont_on])
                      show "{0..s} \<subseteq> I_set" using hs_range unfolding top1_unit_interval_def by (by100 auto)
                    qed
                    have "g_tilde 0 \<le> \<theta>q + 1" using hg0_lt by (by100 linarith)
                    moreover have "\<theta>q + 1 \<le> g_tilde s" using hge by (by100 linarith)
                    ultimately obtain s' where hs': "0 \<le> s' \<and> s' \<le> s" and hgs': "g_tilde s' = \<theta>q + 1"
                      using IVT'[OF _ _ h0_le_s h_cont_seg] by (by100 blast)
                    have "s' \<in> I_set" using hs' hs_range unfolding top1_unit_interval_def by (by100 auto)
                    hence "g_tilde s' \<noteq> \<theta>q + of_int 1"
                      using hgtilde_avoids_lattice by (by100 blast)
                    hence "g_tilde s' \<noteq> \<theta>q + 1" by (by100 simp)
                    thus False using hgs' by (by100 blast)
                  qed
                  show "\<theta>q < g_tilde s \<and> g_tilde s < \<theta>q + 1"
                    using h_lb h_ub by (by100 blast)
                qed
                \<comment> \<open>Step D: g_tilde(1) = \<theta>p (lift of loop is a loop in (\<theta>q, \<theta>q + 1)).\<close>
                have hgtilde_1: "g_tilde 1 = \<theta>p"
                proof -
                  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have "top1_R_to_S1 (g_tilde 1) = (?hinv \<circ> f) 1"
                    using hgtilde_proj h1I by (by100 blast)
                  also have "... = ?hinv (f 1)" by (by100 simp)
                  also have "... = ?hinv p" using hf1 by (by100 simp)
                  also have "... = p'" unfolding p'_def by (by100 simp)
                  finally have hR1: "top1_R_to_S1 (g_tilde 1) = p'" .
                  \<comment> \<open>g_tilde(1) \<in> (\<theta>q, \<theta>q+1) and R_to_S1(g_tilde(1)) = p' = R_to_S1(\<theta>p).
                     By injectivity of R_to_S1 on (\<theta>q, \<theta>q + 1), g_tilde(1) = \<theta>p.\<close>
                  have hg1_range: "\<theta>q < g_tilde 1 \<and> g_tilde 1 < \<theta>q + 1"
                    using hgtilde_range h1I by (by100 blast)
                  have hR1_eq: "top1_R_to_S1 (g_tilde 1) = top1_R_to_S1 \<theta>p"
                    using hR1 h\<theta>p by (by100 simp)
                  \<comment> \<open>cos(2\<pi> g_tilde(1)) = cos(2\<pi> \<theta>p) and sin(2\<pi> g_tilde(1)) = sin(2\<pi> \<theta>p).\<close>
                  have "cos (2*pi* g_tilde 1) = cos (2*pi*\<theta>p) \<and> sin (2*pi* g_tilde 1) = sin (2*pi*\<theta>p)"
                    using hR1_eq unfolding top1_R_to_S1_def by (by100 simp)
                  hence "sin (2*pi*g_tilde 1) = sin (2*pi*\<theta>p) \<and> cos (2*pi*g_tilde 1) = cos (2*pi*\<theta>p)"
                    by (by100 blast)
                  then obtain k :: int where hk: "2*pi*g_tilde 1 = 2*pi*\<theta>p + 2*pi*of_int k"
                    using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                  hence h_diff: "2*pi*(g_tilde 1 - \<theta>p) = 2*pi*of_int k"
                    by (simp add: algebra_simps)
                  hence "g_tilde 1 - \<theta>p = of_int k"
                    using pi_gt_zero by (by100 simp)
                  moreover have "g_tilde 1 - \<theta>p > -1 \<and> g_tilde 1 - \<theta>p < 1"
                    using hg1_range h\<theta>p_range by (by100 linarith)
                  ultimately have "of_int k > (-1::real) \<and> of_int k < (1::real)" by (by100 linarith)
                  hence "k = 0" by (by100 linarith)
                  thus "g_tilde 1 = \<theta>p" using \<open>g_tilde 1 - \<theta>p = of_int k\<close> by (by100 simp)
                qed
                \<comment> \<open>Step E: Construct the homotopy F = h \<circ> R_to_S1 \<circ> SLH(g_tilde, \<theta>p).
                   SLH(s,t) = (1-t)*g_tilde(s) + t*\<theta>p stays in (\<theta>q, \<theta>q + 1) by convexity.\<close>
                \<comment> \<open>Construct the straight-line homotopy extension.\<close>
                define SLH where "SLH = top1_slh_ext g_tilde \<theta>p"
                have hSLH_cont: "continuous_on UNIV SLH"
                  unfolding SLH_def by (rule top1_slh_ext_continuous[OF hgtilde_cont_on])
                \<comment> \<open>SLH agrees with (1-t)*g_tilde(s) + t*\<theta>p on I \<times> I.\<close>
                have hSLH_agrees: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow>
                    SLH (s, t) = (1 - t) * g_tilde s + t * \<theta>p"
                proof -
                  fix s t :: real assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
                  have "(s, t) \<in> top1_unit_interval \<times> top1_unit_interval"
                    using hs ht unfolding top1_unit_interval_def by (by100 blast)
                  thus "SLH (s, t) = (1 - t) * g_tilde s + t * \<theta>p"
                    unfolding SLH_def using top1_slh_ext_agrees[of "(s, t)"]
                    unfolding top1_unit_interval_def by (by100 auto)
                qed
                \<comment> \<open>SLH on I \<times> I stays in (\<theta>q, \<theta>q + 1): convex combination of points in the interval.\<close>
                have hSLH_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. \<theta>q < SLH (s, t) \<and> SLH (s, t) < \<theta>q + 1"
                proof (intro ballI)
                  fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
                  have hSLH_eq: "SLH (s, t) = (1 - t) * g_tilde s + t * \<theta>p"
                    using hSLH_agrees hs ht .
                  have hgs: "\<theta>q < g_tilde s \<and> g_tilde s < \<theta>q + 1"
                    using hgtilde_range hs by (by100 blast)
                  have ht_range: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)
                  have h1t: "0 \<le> 1 - t" using ht_range by (by100 linarith)
                  \<comment> \<open>Lower bound: (1-t)*g(s) + t*\<theta>p > (1-t)*\<theta>q + t*\<theta>q = \<theta>q.\<close>
                  have hlb1: "(1 - t) * g_tilde s > (1 - t) * \<theta>q \<or> t > 0"
                  proof (cases "t < 1")
                    case True
                    hence "1 - t > 0" by (by100 linarith)
                    hence "(1 - t) * g_tilde s > (1 - t) * \<theta>q"
                      using hgs by (simp add: mult_strict_left_mono)
                    thus ?thesis by (by100 blast)
                  next
                    case False
                    hence "t = 1" using ht_range by (by100 linarith)
                    hence "t > 0" by (by100 linarith)
                    thus ?thesis by (by100 blast)
                  qed
                  have h_lb: "SLH (s, t) > \<theta>q"
                  proof (cases "t < 1")
                    case True
                    hence "1 - t > 0" by (by100 linarith)
                    hence "(1 - t) * g_tilde s > (1 - t) * \<theta>q"
                      using hgs by (simp add: mult_strict_left_mono)
                    moreover have "t * \<theta>p \<ge> t * \<theta>q"
                      using ht_range h\<theta>p_range by (simp add: mult_left_mono less_imp_le)
                    ultimately have "(1 - t) * g_tilde s + t * \<theta>p > (1 - t) * \<theta>q + t * \<theta>q"
                      by (by100 linarith)
                    moreover have "(1 - t) * \<theta>q + t * \<theta>q = \<theta>q" by (simp add: algebra_simps)
                    ultimately show ?thesis using hSLH_eq by (by100 linarith)
                  next
                    case False
                    hence "t = 1" using ht_range by (by100 linarith)
                    hence "SLH (s, t) = \<theta>p" using hSLH_eq by (by100 simp)
                    thus ?thesis using h\<theta>p_range by (by100 linarith)
                  qed
                  \<comment> \<open>Upper bound: similar.\<close>
                  have h_ub: "SLH (s, t) < \<theta>q + 1"
                  proof (cases "t < 1")
                    case True
                    hence "1 - t > 0" by (by100 linarith)
                    hence "(1 - t) * g_tilde s < (1 - t) * (\<theta>q + 1)"
                      using hgs by (simp add: mult_strict_left_mono)
                    moreover have "t * \<theta>p \<le> t * (\<theta>q + 1)"
                      using ht_range h\<theta>p_range by (simp add: mult_left_mono less_imp_le)
                    ultimately have "(1 - t) * g_tilde s + t * \<theta>p < (1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1)"
                      by (by100 linarith)
                    moreover have "(1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1) = \<theta>q + 1"
                      by (simp add: algebra_simps)
                    ultimately show ?thesis using hSLH_eq by (by100 linarith)
                  next
                    case False
                    hence "t = 1" using ht_range by (by100 linarith)
                    hence "SLH (s, t) = \<theta>p" using hSLH_eq by (by100 simp)
                    thus ?thesis using h\<theta>p_range by (by100 linarith)
                  qed
                  show "\<theta>q < SLH (s, t) \<and> SLH (s, t) < \<theta>q + 1"
                    using h_lb h_ub by (by100 blast)
                qed
                \<comment> \<open>Step F: Push forward through h \<circ> R_to_S1: define F(s,t) = h(R_to_S1(SLH(s,t))).\<close>
                define F where "F st = h (top1_R_to_S1 (SLH st))" for st :: "real \<times> real"
                \<comment> \<open>F is continuous I\<times>I \<rightarrow> C \<alpha>.\<close>
                have hF_cont_C: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) F"
                proof -
                  \<comment> \<open>SLH is continuous UNIV \<rightarrow> UNIV.\<close>
                  have hSLH_cont_map: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                      (UNIV::real set) top1_open_sets SLH"
                    by (rule top1_continuous_map_on_II_to_UNIV[OF hSLH_cont])
                  \<comment> \<open>R_to_S1 is continuous UNIV \<rightarrow> S1.\<close>
                  have hR_S1_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                      top1_S1 top1_S1_topology top1_R_to_S1"
                    by (rule top1_covering_map_on_continuous[OF Theorem_53_1])
                  \<comment> \<open>R_to_S1 \<circ> SLH: I\<times>I \<rightarrow> S1.\<close>
                  have hR_SLH: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                      top1_S1 top1_S1_topology (top1_R_to_S1 \<circ> SLH)"
                    by (rule top1_continuous_map_on_comp[OF hSLH_cont_map hR_S1_cont])
                  \<comment> \<open>h \<circ> (R_to_S1 \<circ> SLH): I\<times>I \<rightarrow> C \<alpha>.\<close>
                  have hF_eq: "\<forall>st\<in>I_set \<times> I_set. (h \<circ> (top1_R_to_S1 \<circ> SLH)) st = F st"
                    unfolding F_def by (by100 simp)
                  have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h \<circ> (top1_R_to_S1 \<circ> SLH))"
                    by (rule top1_continuous_map_on_comp[OF hR_SLH hcont_h])
                  show ?thesis using iffD1[OF top1_continuous_map_on_cong[OF hF_eq]] hcomp by (by100 blast)
                qed
                \<comment> \<open>F maps I\<times>I to W \<alpha> (since SLH stays in (\<theta>q, \<theta>q+1), R_to_S1 avoids q', h avoids q \<alpha>).\<close>
                have hF_range: "\<forall>st\<in>I_set \<times> I_set. F st \<in> W \<alpha>"
                proof (intro ballI)
                  fix st assume hst: "st \<in> I_set \<times> I_set"
                  obtain s t where hst_eq: "st = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
                    using hst by (by100 blast)
                  have hSLH_in: "\<theta>q < SLH (s, t) \<and> SLH (s, t) < \<theta>q + 1"
                    using hSLH_range hs ht by (by100 blast)
                  \<comment> \<open>R_to_S1(SLH(s,t)) \<in> S1 - {q'}.\<close>
                  have hR_in_S1: "top1_R_to_S1 (SLH (s, t)) \<in> top1_S1"
                    unfolding top1_R_to_S1_def top1_S1_def using sin_squared_eq by (by100 simp)
                  have hR_ne_q': "top1_R_to_S1 (SLH (s, t)) \<noteq> q'"
                  proof
                    assume heq: "top1_R_to_S1 (SLH (s, t)) = q'"
                    hence "top1_R_to_S1 (SLH (s, t)) = top1_R_to_S1 \<theta>q" using h\<theta>q by (by100 simp)
                    hence "cos (2*pi*SLH(s,t)) = cos (2*pi*\<theta>q) \<and> sin (2*pi*SLH(s,t)) = sin (2*pi*\<theta>q)"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin (2*pi*SLH(s,t)) = sin (2*pi*\<theta>q) \<and> cos (2*pi*SLH(s,t)) = cos (2*pi*\<theta>q)"
                      by (by100 blast)
                    then obtain k :: int where hk2: "2*pi*SLH(s,t) = 2*pi*\<theta>q + 2*pi*of_int k"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    hence "2*pi*(SLH(s,t) - \<theta>q) = 2*pi*of_int k" by (simp add: algebra_simps)
                    hence "SLH(s,t) - \<theta>q = of_int k" using pi_gt_zero by (by100 simp)
                    moreover have "SLH(s,t) - \<theta>q > 0 \<and> SLH(s,t) - \<theta>q < 1"
                      using hSLH_in by (by100 linarith)
                    ultimately have "of_int k > (0::real) \<and> of_int k < (1::real)" by (by100 linarith)
                    hence "k > 0 \<and> k < 1" by (by100 linarith)
                    thus False by (by100 linarith)
                  qed
                  \<comment> \<open>h(R_to_S1(SLH(s,t))) \<in> C \<alpha> - {q \<alpha>} = W \<alpha>.\<close>
                  have hh_in_C: "h (top1_R_to_S1 (SLH (s, t))) \<in> C \<alpha>"
                    using hbij hR_in_S1 unfolding bij_betw_def by (by100 blast)
                  have hh_ne_q: "h (top1_R_to_S1 (SLH (s, t))) \<noteq> q \<alpha>"
                  proof
                    assume "h (top1_R_to_S1 (SLH (s, t))) = q \<alpha>"
                    hence "h (top1_R_to_S1 (SLH (s, t))) = h q'"
                      using bij_betw_inv_into_right[OF hbij hq_in]
                      unfolding q'_def by (by100 simp)
                    hence "top1_R_to_S1 (SLH (s, t)) = q'"
                      using hbij hR_in_S1 hq'_S1 unfolding bij_betw_def inj_on_def by (by100 blast)
                    thus False using hR_ne_q' by (by100 blast)
                  qed
                  show "F st \<in> W \<alpha>"
                    unfolding F_def hst_eq W_def using hh_in_C hh_ne_q by (by100 blast)
                qed
                \<comment> \<open>Shrink codomain from C \<alpha> to W \<alpha>.\<close>
                have hF_cont_W: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                    (W \<alpha>) (subspace_topology X TX (W \<alpha>)) F"
                proof -
                  have hF_img: "F ` (I_set \<times> I_set) \<subseteq> W \<alpha>"
                    using hF_range by (by100 blast)
                  have hW_sub_C': "W \<alpha> \<subseteq> C \<alpha>" using hW_sub_C_here .
                  have hF_shrunk: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                      (W \<alpha>) (subspace_topology (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (W \<alpha>)) F"
                    by (rule top1_continuous_map_on_codomain_shrink[OF hF_cont_C hF_img hW_sub_C'])
                  have hsub_trans: "subspace_topology (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (W \<alpha>)
                      = subspace_topology X TX (W \<alpha>)"
                    by (rule subspace_topology_trans[OF hW_sub_C'])
                  show ?thesis using hF_shrunk hsub_trans by (by100 simp)
                qed
                \<comment> \<open>Step G: Verify boundary conditions.\<close>
                have hF_s0: "\<forall>s\<in>I_set. F (s, 0) = f s"
                proof (intro ballI)
                  fix s assume hs: "s \<in> I_set"
                  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have "SLH (s, 0) = (1 - 0) * g_tilde s + 0 * \<theta>p"
                    using hSLH_agrees hs h0I by (by100 blast)
                  hence "SLH (s, 0) = g_tilde s" by (by100 simp)
                  hence "F (s, 0) = h (top1_R_to_S1 (g_tilde s))" unfolding F_def by (by100 simp)
                  also have "... = h ((?hinv \<circ> f) s)" using hgtilde_proj hs by (by100 simp)
                  also have "... = h (?hinv (f s))" by (by100 simp)
                  also have "... = f s"
                  proof -
                    have "f s \<in> W \<alpha>" using hf_cont hs unfolding top1_continuous_map_on_def by (by100 blast)
                    hence "f s \<in> C \<alpha>" using hW_sub_C_here by (by100 blast)
                    thus ?thesis using bij_betw_inv_into_right[OF hbij] by (by100 blast)
                  qed
                  finally show "F (s, 0) = f s" .
                qed
                have hF_s1: "\<forall>s\<in>I_set. F (s, 1) = p"
                proof (intro ballI)
                  fix s assume hs: "s \<in> I_set"
                  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have "SLH (s, 1) = (1 - 1) * g_tilde s + 1 * \<theta>p"
                    using hSLH_agrees hs h1I by (by100 blast)
                  hence "SLH (s, 1) = \<theta>p" by (by100 simp)
                  hence "F (s, 1) = h (top1_R_to_S1 \<theta>p)" unfolding F_def by (by100 simp)
                  also have "... = h p'" using h\<theta>p by (by100 simp)
                  also have "... = p"
                    unfolding p'_def using bij_betw_inv_into_right[OF hbij hp_C] by (by100 blast)
                  finally show "F (s, 1) = p" .
                qed
                have hF_0t: "\<forall>t\<in>I_set. F (0, t) = p"
                proof (intro ballI)
                  fix t assume ht: "t \<in> I_set"
                  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have "SLH (0, t) = (1 - t) * g_tilde 0 + t * \<theta>p"
                    using hSLH_agrees h0I ht by (by100 blast)
                  hence "SLH (0, t) = (1 - t) * \<theta>p + t * \<theta>p" using hgtilde_0 by (by100 simp)
                  hence "SLH (0, t) = \<theta>p" by (simp add: algebra_simps)
                  hence "F (0, t) = h (top1_R_to_S1 \<theta>p)" unfolding F_def by (by100 simp)
                  also have "... = h p'" using h\<theta>p by (by100 simp)
                  also have "... = p"
                    unfolding p'_def using bij_betw_inv_into_right[OF hbij hp_C] by (by100 blast)
                  finally show "F (0, t) = p" .
                qed
                have hF_1t: "\<forall>t\<in>I_set. F (1, t) = p"
                proof (intro ballI)
                  fix t assume ht: "t \<in> I_set"
                  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                  have "SLH (1, t) = (1 - t) * g_tilde 1 + t * \<theta>p"
                    using hSLH_agrees h1I ht by (by100 blast)
                  hence "SLH (1, t) = (1 - t) * \<theta>p + t * \<theta>p" using hgtilde_1 by (by100 simp)
                  hence "SLH (1, t) = \<theta>p" by (simp add: algebra_simps)
                  hence "F (1, t) = h (top1_R_to_S1 \<theta>p)" unfolding F_def by (by100 simp)
                  also have "... = h p'" using h\<theta>p by (by100 simp)
                  also have "... = p"
                    unfolding p'_def using bij_betw_inv_into_right[OF hbij hp_C] by (by100 blast)
                  finally show "F (1, t) = p" .
                qed
                \<comment> \<open>Step H: Assemble the path homotopy.\<close>
                have hf_path_W: "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p p f"
                  using hloop unfolding top1_is_loop_on_def .
                have hconst_path: "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p p (top1_constant_path p)"
                proof -
                  have hW\<alpha>_sub_X: "W \<alpha> \<subseteq> X" using hW_sub_X h\<alpha> by (by100 blast)
                  have hTW: "is_topology_on (W \<alpha>) (subspace_topology X TX (W \<alpha>))"
                    by (rule subspace_topology_is_topology_on[OF hTX hW\<alpha>_sub_X])
                  show ?thesis by (rule top1_constant_path_is_path[OF hTW hp\<alpha>])
                qed
                have hF_s1_const: "\<forall>s\<in>I_set. F (s, 1) = top1_constant_path p s"
                proof (intro ballI)
                  fix s assume hs: "s \<in> I_set"
                  show "F (s, 1) = top1_constant_path p s"
                    using hF_s1 hs unfolding top1_constant_path_def by (by100 simp)
                qed
                show "top1_path_homotopic_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) p p f (top1_constant_path p)"
                  unfolding top1_path_homotopic_on_def
                  using hf_path_W hconst_path hF_cont_W hF_s0 hF_s1_const hF_0t hF_1t by (by100 blast)
              qed
            qed
          qed
          \<comment> \<open>Main result: every loop at p in U_def \<inter> V_def is nulhomotopic.
             Decompose the loop into sub-loops each in a single W(\<alpha>) using the
             weak-topology open cover, contract each in W(\<alpha>), and concatenate.
             Key: the connected components of (\<Union>W \<alpha>) \\ {p} are precisely
             the W \<alpha> \\ {p}, so the loop decomposes naturally at passages through p.\<close>
          \<comment> \<open>Helper: path homotopy in a subspace transfers to a superspace.\<close>
          have hph_enlarge: "\<And>A f g. A \<subseteq> U_def \<inter> V_def \<Longrightarrow> A \<subseteq> X \<Longrightarrow>
              top1_path_homotopic_on A (subspace_topology X TX A) p p f g \<Longrightarrow>
              top1_path_homotopic_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f g"
          proof -
            fix A f g
            assume hA_UV: "A \<subseteq> U_def \<inter> V_def" and hA_X: "A \<subseteq> X"
            assume hph: "top1_path_homotopic_on A (subspace_topology X TX A) p p f g"
            from hph obtain F where
                hf_path: "top1_is_path_on A (subspace_topology X TX A) p p f"
                and hg_path: "top1_is_path_on A (subspace_topology X TX A) p p g"
                and hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology A (subspace_topology X TX A) F"
                and hF_s0: "\<forall>s\<in>I_set. F (s, 0) = f s"
                and hF_s1: "\<forall>s\<in>I_set. F (s, 1) = g s"
                and hF_0t: "\<forall>t\<in>I_set. F (0, t) = p"
                and hF_1t: "\<forall>t\<in>I_set. F (1, t) = p"
              unfolding top1_path_homotopic_on_def by blast
            \<comment> \<open>Enlarge F's codomain from A to U_def \<inter> V_def.\<close>
            have hF_cont': "top1_continuous_map_on (I_set \<times> I_set) II_topology
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) F"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hF_cont hA_UV hUV_sub])
            \<comment> \<open>Enlarge f and g as paths in the larger space.\<close>
            have hf_cont_A: "top1_continuous_map_on I_set I_top A (subspace_topology X TX A) f"
              using hf_path unfolding top1_is_path_on_def by (by100 blast)
            have hf_cont': "top1_continuous_map_on I_set I_top
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) f"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hf_cont_A hA_UV hUV_sub])
            have hf0: "f 0 = p" and hf1: "f 1 = p"
              using hf_path unfolding top1_is_path_on_def by (by100 blast)+
            have hf_path': "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f"
              unfolding top1_is_path_on_def using hf_cont' hf0 hf1 by (by100 blast)
            have hg_cont_A: "top1_continuous_map_on I_set I_top A (subspace_topology X TX A) g"
              using hg_path unfolding top1_is_path_on_def by (by100 blast)
            have hg_cont': "top1_continuous_map_on I_set I_top
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) g"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hg_cont_A hA_UV hUV_sub])
            have hg0: "g 0 = p" and hg1: "g 1 = p"
              using hg_path unfolding top1_is_path_on_def by (by100 blast)+
            have hg_path': "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p g"
              unfolding top1_is_path_on_def using hg_cont' hg0 hg1 by (by100 blast)
            show "top1_path_homotopic_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f g"
              unfolding top1_path_homotopic_on_def
              using hf_path' hg_path' hF_cont' hF_s0 hF_s1 hF_0t hF_1t by (by100 blast)
          qed
          \<comment> \<open>W(\<alpha>) overlap data: W(\<alpha>) \<inter> W(\<beta>) = {p} for \<alpha> \<noteq> \<beta>.\<close>
          have hW_inter: "\<And>\<alpha> \<beta>. \<alpha> \<in> {..<n} \<Longrightarrow> \<beta> \<in> {..<n} \<Longrightarrow> \<alpha> \<noteq> \<beta> \<Longrightarrow> W \<alpha> \<inter> W \<beta> = {p}"
          proof -
            fix \<alpha> \<beta> assume h\<alpha>: "\<alpha> \<in> {..<n}" and h\<beta>: "\<beta> \<in> {..<n}" and hne: "\<alpha> \<noteq> \<beta>"
            have "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha> h\<beta> hne by (by100 blast)
            moreover have "W \<alpha> \<subseteq> C \<alpha>" and "W \<beta> \<subseteq> C \<beta>" using hW_sub_C h\<alpha> h\<beta> by (by100 blast)+
            moreover have "p \<in> W \<alpha>" and "p \<in> W \<beta>" using hp_W h\<alpha> h\<beta> by (by100 blast)+
            ultimately show "W \<alpha> \<inter> W \<beta> = {p}" by (by100 blast)
          qed
          show "\<forall>f. top1_is_loop_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p f \<longrightarrow>
              top1_path_homotopic_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f (top1_constant_path p)"
          proof (intro allI impI)
            fix f assume hloop: "top1_is_loop_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p f"
            \<comment> \<open>f is a path from p to p in U_def \<inter> V_def = \<Union>W(\<alpha>).\<close>
            have hf_path: "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f"
              using hloop unfolding top1_is_loop_on_def .
            have hf_cont: "top1_continuous_map_on I_set I_top
                (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) f"
              using hf_path unfolding top1_is_path_on_def by (by100 blast)
            have hf_range: "\<forall>s\<in>I_set. f s \<in> U_def \<inter> V_def"
              using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
            have hf0: "f 0 = p" and hf1: "f 1 = p"
              using hf_path unfolding top1_is_path_on_def by (by100 blast)+
            \<comment> \<open>The key claim: the loop decomposes into sub-loops, each in a single W(\<alpha>),
               and each is nulhomotopic. This follows from:
               1. f\<inverse>({p}) is closed in [0,1] (preimage of closed set)
               2. [0,1] \\ f\<inverse>({p}) is open, hence a union of open intervals
               3. On each connected component (a,b) of [0,1] \\ f\<inverse>({p}),
                  f maps (a,b) to some W(\<alpha>)\\ {p} (by connectivity + disjointness of W's away from p)
               4. f|_{[a,b]} is a loop at p in W(\<alpha>)
               5. By simple connectedness of W(\<alpha>), each sub-loop is nulhomotopic
               6. The concatenation of nulhomotopic loops is nulhomotopic
               7. f is path-homotopic to this concatenation, which is nulhomotopic.
               By compactness, only finitely many components, so finite concatenation.\<close>
            \<comment> \<open>We use the simply-connected W(\<alpha>) pieces plus the path homotopy enlargement.
               For each W(\<alpha>), loops at p in W(\<alpha>) are nulhomotopic (hW_sc).
               By hph_enlarge, they are nulhomotopic in \<Union>W(\<alpha>).
               The general loop decomposes into such sub-loops.\<close>
            show "top1_path_homotopic_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p f (top1_constant_path p)"
            proof -
              \<comment> \<open>Strategy: deformation retract \<Union>W(\<alpha>) to {p} via angle interpolation.
                 Define F(s,t) = H(f(s),t) where H contracts each W(\<alpha>) to p.
                 H(x,t) = h_fam(\<alpha>)(R_to_S1((1-t)*angle(\<alpha>)(x) + t*\<theta>p(\<alpha>))) for x \<in> W(\<alpha>).
                 For x = p this gives p regardless of \<alpha>.\<close>
              \<comment> \<open>Step 1: Obtain parameterization family.\<close>
              have hparam_all: "\<forall>\<alpha>\<in>{..<n}. \<exists>h_\<alpha> \<theta>q_\<alpha> \<theta>p_\<alpha>.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>
                \<and> top1_R_to_S1 \<theta>q_\<alpha> = inv_into top1_S1 h_\<alpha> (q \<alpha>)
                \<and> top1_R_to_S1 \<theta>p_\<alpha> = inv_into top1_S1 h_\<alpha> p
                \<and> \<theta>q_\<alpha> < \<theta>p_\<alpha> \<and> \<theta>p_\<alpha> < \<theta>q_\<alpha> + 1"
              proof (intro ballI)
                fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                obtain h_\<alpha> where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>"
                  using hC_props h\<alpha> by (by100 blast)
                have hbij: "bij_betw h_\<alpha> top1_S1 (C \<alpha>)"
                  using hh unfolding top1_homeomorphism_on_def by (by100 blast)
                let ?hinv = "inv_into top1_S1 h_\<alpha>"
                have hbij_inv: "bij_betw ?hinv (C \<alpha>) top1_S1"
                  using homeomorphism_inverse[OF hh] unfolding top1_homeomorphism_on_def by (by100 blast)
                have hq_in: "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
                have hp_in: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                define q' where "q' = ?hinv (q \<alpha>)"
                have hq'_S1: "q' \<in> top1_S1"
                  using hbij_inv hq_in unfolding q'_def bij_betw_def by (by100 blast)
                define p' where "p' = ?hinv p"
                have hp'_S1: "p' \<in> top1_S1"
                  using hbij_inv hp_in unfolding p'_def bij_betw_def by (by100 blast)
                have hp'_ne_q': "p' \<noteq> q'"
                proof
                  assume "p' = q'"
                  hence "?hinv p = ?hinv (q \<alpha>)" unfolding p'_def q'_def .
                  hence "h_\<alpha> (?hinv p) = h_\<alpha> (?hinv (q \<alpha>))" by (by100 simp)
                  hence "p = q \<alpha>"
                    using bij_betw_inv_into_right[OF hbij hp_in]
                          bij_betw_inv_into_right[OF hbij hq_in] by (by100 simp)
                  thus False using hq h\<alpha> by (by100 blast)
                qed
                obtain \<theta>q' where h\<theta>q': "top1_R_to_S1 \<theta>q' = q'"
                proof -
                  have "fst q' ^ 2 + snd q' ^ 2 = 1" using hq'_S1 unfolding top1_S1_def by (by100 simp)
                  then obtain \<theta> where "fst q' = cos \<theta>" "snd q' = sin \<theta>"
                    using sincos_total_2pi by (by100 metis)
                  hence "top1_R_to_S1 (\<theta> / (2 * pi)) = q'"
                    unfolding top1_R_to_S1_def by (simp add: prod_eq_iff)
                  thus ?thesis using that by (by100 blast)
                qed
                obtain \<theta>p' where h\<theta>p': "top1_R_to_S1 \<theta>p' = p'"
                    and h\<theta>p'_range: "\<theta>q' < \<theta>p' \<and> \<theta>p' < \<theta>q' + 1"
                proof -
                  have "fst p' ^ 2 + snd p' ^ 2 = 1" using hp'_S1 unfolding top1_S1_def by (by100 simp)
                  then obtain \<theta>r where hcos: "fst p' = cos \<theta>r" and hsin: "snd p' = sin \<theta>r"
                    using sincos_total_2pi by (by100 metis)
                  define \<theta>0 where "\<theta>0 = \<theta>r / (2 * pi)"
                  have h\<theta>0: "top1_R_to_S1 \<theta>0 = p'"
                    unfolding top1_R_to_S1_def \<theta>0_def using hcos hsin by (simp add: prod_eq_iff)
                  define k where "k = \<lfloor>\<theta>0 - \<theta>q'\<rfloor>"
                  define \<theta>a where "\<theta>a = \<theta>0 - of_int k"
                  have h\<theta>a_R: "top1_R_to_S1 \<theta>a = p'"
                  proof -
                    have "top1_R_to_S1 \<theta>a = top1_R_to_S1 (\<theta>0 + of_int (-k))"
                      unfolding \<theta>a_def by (by100 simp)
                    also have "\<dots> = top1_R_to_S1 \<theta>0" by (rule top1_R_to_S1_int_shift_early)
                    also have "\<dots> = p'" by (rule h\<theta>0)
                    finally show ?thesis .
                  qed
                  have "\<theta>q' \<le> \<theta>a \<and> \<theta>a < \<theta>q' + 1"
                    unfolding \<theta>a_def k_def by linarith
                  moreover have "\<theta>a \<noteq> \<theta>q'"
                  proof
                    assume "\<theta>a = \<theta>q'"
                    hence "top1_R_to_S1 \<theta>a = top1_R_to_S1 \<theta>q'" by (by100 simp)
                    hence "p' = q'" using h\<theta>a_R h\<theta>q' by (by100 simp)
                    thus False using hp'_ne_q' by (by100 blast)
                  qed
                  ultimately have "\<theta>q' < \<theta>a \<and> \<theta>a < \<theta>q' + 1" by (by100 linarith)
                  thus ?thesis using that h\<theta>a_R by (by100 blast)
                qed
                show "\<exists>h_\<alpha> \<theta>q_\<alpha> \<theta>p_\<alpha>.
                    top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>
                  \<and> top1_R_to_S1 \<theta>q_\<alpha> = inv_into top1_S1 h_\<alpha> (q \<alpha>)
                  \<and> top1_R_to_S1 \<theta>p_\<alpha> = inv_into top1_S1 h_\<alpha> p
                  \<and> \<theta>q_\<alpha> < \<theta>p_\<alpha> \<and> \<theta>p_\<alpha> < \<theta>q_\<alpha> + 1"
                  using hh h\<theta>q' h\<theta>p' h\<theta>p'_range
                  unfolding q'_def p'_def by (by100 blast)
              qed
              \<comment> \<open>Step 2: Choose parameterizations via Skolem.\<close>
              obtain h_fam :: "nat \<Rightarrow> (real \<times> real) \<Rightarrow> 'a"
                  and \<theta>q_fam \<theta>p_fam :: "nat \<Rightarrow> real" where
                  hfam: "\<forall>\<alpha>\<in>{..<n}. top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h_fam \<alpha>)
                    \<and> top1_R_to_S1 (\<theta>q_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) (q \<alpha>)
                    \<and> top1_R_to_S1 (\<theta>p_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) p
                    \<and> \<theta>q_fam \<alpha> < \<theta>p_fam \<alpha> \<and> \<theta>p_fam \<alpha> < \<theta>q_fam \<alpha> + 1"
              proof -
                from hparam_all
                obtain hf where hhf: "\<forall>\<alpha>\<in>{..<n}. \<exists>\<theta>q' \<theta>p'.
                    top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                  \<and> top1_R_to_S1 \<theta>q' = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                  \<and> top1_R_to_S1 \<theta>p' = inv_into top1_S1 (hf \<alpha>) p
                  \<and> \<theta>q' < \<theta>p' \<and> \<theta>p' < \<theta>q' + 1"
                  by (by100 metis)
                then obtain tqf where htqf: "\<forall>\<alpha>\<in>{..<n}. \<exists>\<theta>p'.
                    top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                  \<and> top1_R_to_S1 (tqf \<alpha>) = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                  \<and> top1_R_to_S1 \<theta>p' = inv_into top1_S1 (hf \<alpha>) p
                  \<and> tqf \<alpha> < \<theta>p' \<and> \<theta>p' < tqf \<alpha> + 1"
                  by (by100 metis)
                then obtain tpf where htpf: "\<forall>\<alpha>\<in>{..<n}.
                    top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                  \<and> top1_R_to_S1 (tqf \<alpha>) = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                  \<and> top1_R_to_S1 (tpf \<alpha>) = inv_into top1_S1 (hf \<alpha>) p
                  \<and> tqf \<alpha> < tpf \<alpha> \<and> tpf \<alpha> < tqf \<alpha> + 1"
                  by (by100 metis)
                thus ?thesis using that[of hf tqf tpf] by (by100 blast)
              qed
              \<comment> \<open>Step 3: Define angle function and prove its spec.\<close>
              define angle_fam :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
                "angle_fam \<alpha> x = (THE \<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1
                  \<and> top1_R_to_S1 \<theta> = inv_into top1_S1 (h_fam \<alpha>) x)" for \<alpha> x
              have hangle_spec: "\<And>\<alpha> x. \<alpha> \<in> {..<n} \<Longrightarrow> x \<in> W \<alpha> \<Longrightarrow>
                  \<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1 \<and>
                  top1_R_to_S1 (angle_fam \<alpha> x) = inv_into top1_S1 (h_fam \<alpha>) x"
              proof -
                fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> {..<n}" and hxW: "x \<in> W \<alpha>"
                have hx_C: "x \<in> C \<alpha>" using hxW unfolding W_def by (by100 blast)
                let ?hinv' = "inv_into top1_S1 (h_fam \<alpha>)"
                have hh\<alpha>: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h_fam \<alpha>)"
                  using hfam h\<alpha> by (by100 blast)
                have hbij': "bij_betw (h_fam \<alpha>) top1_S1 (C \<alpha>)"
                  using hh\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                have hbij_inv': "bij_betw ?hinv' (C \<alpha>) top1_S1"
                  using homeomorphism_inverse[OF hh\<alpha>]
                  unfolding top1_homeomorphism_on_def by (by100 blast)
                have hhinv'_x: "?hinv' x \<in> top1_S1"
                  using hbij_inv' hx_C unfolding bij_betw_def by (by100 blast)
                have hx_neq_q: "x \<noteq> q \<alpha>" using hxW unfolding W_def by (by100 blast)
                have hq_in': "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
                have hhinv'_x_ne_q: "?hinv' x \<noteq> ?hinv' (q \<alpha>)"
                proof
                  assume heqq: "?hinv' x = ?hinv' (q \<alpha>)"
                  hence "h_fam \<alpha> (?hinv' x) = h_fam \<alpha> (?hinv' (q \<alpha>))" by (by100 simp)
                  hence "x = q \<alpha>"
                    using bij_betw_inv_into_right[OF hbij' hx_C]
                          bij_betw_inv_into_right[OF hbij' hq_in'] by (by100 simp)
                  thus False using hx_neq_q by (by100 blast)
                qed
                have h\<theta>q_eq: "top1_R_to_S1 (\<theta>q_fam \<alpha>) = ?hinv' (q \<alpha>)"
                  using hfam h\<alpha> by (by100 blast)
                \<comment> \<open>Get raw angle for hinv(x).\<close>
                have heq_x: "fst (?hinv' x) ^ 2 + snd (?hinv' x) ^ 2 = 1"
                  using hhinv'_x unfolding top1_S1_def by (by100 simp)
                obtain \<theta>r where hcos_x: "fst (?hinv' x) = cos \<theta>r" and hsin_x: "snd (?hinv' x) = sin \<theta>r"
                  using sincos_total_2pi heq_x by (by100 metis)
                define \<theta>_raw where "\<theta>_raw = \<theta>r / (2 * pi)"
                have h_raw: "top1_R_to_S1 \<theta>_raw = ?hinv' x"
                  unfolding top1_R_to_S1_def \<theta>_raw_def using hcos_x hsin_x by (simp add: prod_eq_iff)
                define k_x where "k_x = \<lfloor>\<theta>_raw - \<theta>q_fam \<alpha>\<rfloor>"
                define \<theta>0_x where "\<theta>0_x = \<theta>_raw - of_int k_x"
                have h\<theta>0_x_R: "top1_R_to_S1 \<theta>0_x = ?hinv' x"
                proof -
                  have "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 (\<theta>_raw + of_int (-k_x))"
                    unfolding \<theta>0_x_def by (by100 simp)
                  also have "\<dots> = top1_R_to_S1 \<theta>_raw" by (rule top1_R_to_S1_int_shift_early)
                  also have "\<dots> = ?hinv' x" by (rule h_raw)
                  finally show ?thesis .
                qed
                have h\<theta>0_x_range: "\<theta>q_fam \<alpha> \<le> \<theta>0_x \<and> \<theta>0_x < \<theta>q_fam \<alpha> + 1"
                  unfolding \<theta>0_x_def k_x_def by linarith
                have "\<theta>0_x \<noteq> \<theta>q_fam \<alpha>"
                proof
                  assume "\<theta>0_x = \<theta>q_fam \<alpha>"
                  hence "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 (\<theta>q_fam \<alpha>)" by (by100 simp)
                  hence "?hinv' x = ?hinv' (q \<alpha>)" using h\<theta>0_x_R h\<theta>q_eq by (by100 simp)
                  thus False using hhinv'_x_ne_q by (by100 blast)
                qed
                hence h\<theta>0_x_strict: "\<theta>q_fam \<alpha> < \<theta>0_x" using h\<theta>0_x_range by (by100 linarith)
                have h\<theta>0_x: "\<theta>q_fam \<alpha> < \<theta>0_x \<and> \<theta>0_x < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta>0_x = ?hinv' x"
                  using h\<theta>0_x_strict h\<theta>0_x_range h\<theta>0_x_R by (by100 blast)
                \<comment> \<open>Uniqueness of angle in the interval.\<close>
                have huniq: "\<And>\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x \<Longrightarrow> \<theta> = \<theta>0_x"
                proof -
                  fix \<theta> assume h\<theta>: "\<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                  hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>0_x" using h\<theta>0_x_R by (by100 simp)
                  hence "cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x) \<and> sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x)"
                    unfolding top1_R_to_S1_def by (by100 simp)
                  hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x)"
                    by (by100 blast)
                  then obtain j :: int where hj: "2*pi*\<theta> = 2*pi*\<theta>0_x + 2*pi*of_int j"
                    using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                  have "2*pi*(\<theta> - \<theta>0_x) = 2*pi*of_int j" using hj by (simp only: right_diff_distrib)
                  hence "\<theta> - \<theta>0_x = of_int j" using pi_gt_zero by (by100 simp)
                  moreover have "\<theta> - \<theta>0_x > -1 \<and> \<theta> - \<theta>0_x < 1" using h\<theta> h\<theta>0_x by (by100 linarith)
                  ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                  hence "j = 0" by (by100 linarith)
                  thus "\<theta> = \<theta>0_x" using \<open>\<theta> - \<theta>0_x = of_int j\<close> by (by100 simp)
                qed
                \<comment> \<open>THE gives \<theta>0_x.\<close>
                have hex1: "\<exists>!\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                proof (rule ex_ex1I)
                  show "\<exists>\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                    using h\<theta>0_x by (by100 blast)
                next
                  fix a b assume ha: "\<theta>q_fam \<alpha> < a \<and> a < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 a = ?hinv' x"
                      and hb: "\<theta>q_fam \<alpha> < b \<and> b < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 b = ?hinv' x"
                  show "a = b" using huniq[OF ha] huniq[OF hb] by (by100 simp)
                qed
                have hthe: "(THE \<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x) = \<theta>0_x"
                  by (rule the1_equality[OF hex1 h\<theta>0_x])
                show "\<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1 \<and>
                    top1_R_to_S1 (angle_fam \<alpha> x) = inv_into top1_S1 (h_fam \<alpha>) x"
                  unfolding angle_fam_def using hthe h\<theta>0_x by (by100 simp)
              qed
              \<comment> \<open>Key property: angle_fam \<alpha> p = \<theta>p_fam \<alpha>.\<close>
              have hangle_p: "\<And>\<alpha>. \<alpha> \<in> {..<n} \<Longrightarrow> angle_fam \<alpha> p = \<theta>p_fam \<alpha>"
              proof -
                fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                have hp_W_\<alpha>: "p \<in> W \<alpha>" using hp_W h\<alpha> by (by100 blast)
                have h_spec: "\<theta>q_fam \<alpha> < angle_fam \<alpha> p \<and> angle_fam \<alpha> p < \<theta>q_fam \<alpha> + 1 \<and>
                    top1_R_to_S1 (angle_fam \<alpha> p) = inv_into top1_S1 (h_fam \<alpha>) p"
                  using hangle_spec[OF h\<alpha> hp_W_\<alpha>] .
                have h\<theta>p: "top1_R_to_S1 (\<theta>p_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) p"
                  using hfam h\<alpha> by (by100 blast)
                have h\<theta>p_range: "\<theta>q_fam \<alpha> < \<theta>p_fam \<alpha> \<and> \<theta>p_fam \<alpha> < \<theta>q_fam \<alpha> + 1"
                  using hfam h\<alpha> by (by100 blast)
                \<comment> \<open>Both angle_fam \<alpha> p and \<theta>p_fam \<alpha> satisfy the same specification, unique.\<close>
                have "top1_R_to_S1 (angle_fam \<alpha> p) = top1_R_to_S1 (\<theta>p_fam \<alpha>)"
                  using h_spec h\<theta>p by (by100 simp)
                hence "cos (2*pi*angle_fam \<alpha> p) = cos (2*pi*\<theta>p_fam \<alpha>) \<and>
                       sin (2*pi*angle_fam \<alpha> p) = sin (2*pi*\<theta>p_fam \<alpha>)"
                  unfolding top1_R_to_S1_def by (by100 simp)
                hence "sin (2*pi*angle_fam \<alpha> p) = sin (2*pi*\<theta>p_fam \<alpha>) \<and>
                       cos (2*pi*angle_fam \<alpha> p) = cos (2*pi*\<theta>p_fam \<alpha>)"
                  by (by100 blast)
                then obtain j :: int where hj: "2*pi*angle_fam \<alpha> p = 2*pi*\<theta>p_fam \<alpha> + 2*pi*of_int j"
                  using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                have "2*pi*(angle_fam \<alpha> p - \<theta>p_fam \<alpha>) = 2*pi*of_int j"
                  using hj by (simp only: right_diff_distrib)
                hence "angle_fam \<alpha> p - \<theta>p_fam \<alpha> = of_int j"
                  using pi_gt_zero by (by100 simp)
                moreover have "angle_fam \<alpha> p - \<theta>p_fam \<alpha> > -1 \<and> angle_fam \<alpha> p - \<theta>p_fam \<alpha> < 1"
                  using h_spec h\<theta>p_range by (by100 linarith)
                ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                hence "j = 0" by (by100 linarith)
                thus "angle_fam \<alpha> p = \<theta>p_fam \<alpha>"
                  using \<open>angle_fam \<alpha> p - \<theta>p_fam \<alpha> = of_int j\<close> by (by100 simp)
              qed
              \<comment> \<open>Key property: h_fam \<alpha> (R_to_S1 (\<theta>p_fam \<alpha>)) = p.\<close>
              have hh_fam_p: "\<And>\<alpha>. \<alpha> \<in> {..<n} \<Longrightarrow> h_fam \<alpha> (top1_R_to_S1 (\<theta>p_fam \<alpha>)) = p"
              proof -
                fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                have hp_C: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                have hbij: "bij_betw (h_fam \<alpha>) top1_S1 (C \<alpha>)"
                  using hfam h\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                have h\<theta>p: "top1_R_to_S1 (\<theta>p_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) p"
                  using hfam h\<alpha> by (by100 blast)
                show "h_fam \<alpha> (top1_R_to_S1 (\<theta>p_fam \<alpha>)) = p"
                  using h\<theta>p bij_betw_inv_into_right[OF hbij hp_C] by (by100 simp)
              qed
              \<comment> \<open>Key property: h_fam \<alpha> (hinv_\<alpha> x) = x for x \<in> C(\<alpha>).\<close>
              have hh_fam_recover: "\<And>\<alpha> x. \<alpha> \<in> {..<n} \<Longrightarrow> x \<in> W \<alpha> \<Longrightarrow>
                  h_fam \<alpha> (top1_R_to_S1 (angle_fam \<alpha> x)) = x"
              proof -
                fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> {..<n}" and hxW: "x \<in> W \<alpha>"
                have hx_C: "x \<in> C \<alpha>" using hxW unfolding W_def by (by100 blast)
                have hbij: "bij_betw (h_fam \<alpha>) top1_S1 (C \<alpha>)"
                  using hfam h\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                have "top1_R_to_S1 (angle_fam \<alpha> x) = inv_into top1_S1 (h_fam \<alpha>) x"
                  using hangle_spec[OF h\<alpha> hxW] by (by100 blast)
                thus "h_fam \<alpha> (top1_R_to_S1 (angle_fam \<alpha> x)) = x"
                  using bij_betw_inv_into_right[OF hbij hx_C] by (by100 simp)
              qed
              \<comment> \<open>Step 4: For each s \<in> I, f(s) \<in> some W(\<alpha>). Choose \<alpha>(s).\<close>
              have hf_in_W: "\<And>s. s \<in> I_set \<Longrightarrow> \<exists>\<alpha>\<in>{..<n}. f s \<in> W \<alpha>"
              proof -
                fix s assume hs: "s \<in> I_set"
                have "f s \<in> U_def \<inter> V_def" using hf_range hs by (by100 blast)
                hence "f s \<in> (\<Union>\<alpha>\<in>{..<n}. W \<alpha>)" using hUV_eq by (by100 blast)
                thus "\<exists>\<alpha>\<in>{..<n}. f s \<in> W \<alpha>" by (by100 blast)
              qed
              define \<alpha>_of :: "real \<Rightarrow> nat" where
                "\<alpha>_of s = (SOME \<alpha>. \<alpha> \<in> {..<n} \<and> f s \<in> W \<alpha>)" for s
              have h\<alpha>_of_spec: "\<And>s. s \<in> I_set \<Longrightarrow> \<alpha>_of s \<in> {..<n} \<and> f s \<in> W (\<alpha>_of s)"
              proof -
                fix s assume hs: "s \<in> I_set"
                from hf_in_W[OF hs] obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<n}" and hf\<alpha>: "f s \<in> W \<alpha>" by (by100 blast)
                hence "\<exists>\<alpha>. \<alpha> \<in> {..<n} \<and> f s \<in> W \<alpha>" by (by100 blast)
                thus "\<alpha>_of s \<in> {..<n} \<and> f s \<in> W (\<alpha>_of s)"
                  unfolding \<alpha>_of_def using someI_ex[of "\<lambda>\<alpha>. \<alpha> \<in> {..<n} \<and> f s \<in> W \<alpha>"] by (by100 blast)
              qed
              \<comment> \<open>Step 5: Define the homotopy F(s,t).
                 F(s,t) = h_fam(\<alpha>(s))(R_to_S1((1-t)*angle(\<alpha>(s))(f(s)) + t*\<theta>p(\<alpha>(s))))
                 This works regardless of the choice of \<alpha>(s), since for f(s) = p all branches give p.\<close>
              define F :: "real \<times> real \<Rightarrow> 'a" where
                "F st = h_fam (\<alpha>_of (fst st))
                   (top1_R_to_S1 ((1 - snd st) * angle_fam (\<alpha>_of (fst st)) (f (fst st))
                                  + snd st * \<theta>p_fam (\<alpha>_of (fst st))))" for st
              \<comment> \<open>Step 6: Verify boundary conditions.\<close>
              have hF_s0: "\<forall>s\<in>I_set. F (s, 0) = f s"
              proof (intro ballI)
                fix s assume hs: "s \<in> I_set"
                have h\<alpha>s: "\<alpha>_of s \<in> {..<n}" and hfs: "f s \<in> W (\<alpha>_of s)"
                  using h\<alpha>_of_spec[OF hs] by (by100 blast)+
                have "F (s, 0) = h_fam (\<alpha>_of s) (top1_R_to_S1 ((1 - 0) * angle_fam (\<alpha>_of s) (f s) + 0 * \<theta>p_fam (\<alpha>_of s)))"
                  unfolding F_def by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of s) (top1_R_to_S1 (angle_fam (\<alpha>_of s) (f s)))"
                  by (by100 simp)
                also have "\<dots> = f s"
                  using hh_fam_recover[OF h\<alpha>s hfs] .
                finally show "F (s, 0) = f s" .
              qed
              have hF_s1: "\<forall>s\<in>I_set. F (s, 1) = top1_constant_path p s"
              proof (intro ballI)
                fix s assume hs: "s \<in> I_set"
                have h\<alpha>s: "\<alpha>_of s \<in> {..<n}"
                  using h\<alpha>_of_spec[OF hs] by (by100 blast)
                have "F (s, 1) = h_fam (\<alpha>_of s) (top1_R_to_S1 ((1 - 1) * angle_fam (\<alpha>_of s) (f s) + 1 * \<theta>p_fam (\<alpha>_of s)))"
                  unfolding F_def by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of s) (top1_R_to_S1 (\<theta>p_fam (\<alpha>_of s)))"
                  by (by100 simp)
                also have "\<dots> = p"
                  using hh_fam_p[OF h\<alpha>s] .
                finally show "F (s, 1) = top1_constant_path p s"
                  unfolding top1_constant_path_def by (by100 simp)
              qed
              have hF_0t: "\<forall>t\<in>I_set. F (0, t) = p"
              proof (intro ballI)
                fix t assume ht: "t \<in> I_set"
                have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                have h\<alpha>0: "\<alpha>_of 0 \<in> {..<n}" and hf0W: "f 0 \<in> W (\<alpha>_of 0)"
                  using h\<alpha>_of_spec[OF h0I] by (by100 blast)+
                have "F (0, t) = h_fam (\<alpha>_of 0) (top1_R_to_S1 ((1 - t) * angle_fam (\<alpha>_of 0) (f 0) + t * \<theta>p_fam (\<alpha>_of 0)))"
                  unfolding F_def by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 0) (top1_R_to_S1 ((1 - t) * angle_fam (\<alpha>_of 0) p + t * \<theta>p_fam (\<alpha>_of 0)))"
                  using hf0 by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 0) (top1_R_to_S1 ((1 - t) * \<theta>p_fam (\<alpha>_of 0) + t * \<theta>p_fam (\<alpha>_of 0)))"
                  using hangle_p[OF h\<alpha>0] by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 0) (top1_R_to_S1 (\<theta>p_fam (\<alpha>_of 0)))"
                  by (simp add: algebra_simps)
                also have "\<dots> = p"
                  using hh_fam_p[OF h\<alpha>0] .
                finally show "F (0, t) = p" .
              qed
              have hF_1t: "\<forall>t\<in>I_set. F (1, t) = p"
              proof (intro ballI)
                fix t assume ht: "t \<in> I_set"
                have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                have h\<alpha>1: "\<alpha>_of 1 \<in> {..<n}" and hf1W: "f 1 \<in> W (\<alpha>_of 1)"
                  using h\<alpha>_of_spec[OF h1I] by (by100 blast)+
                have "F (1, t) = h_fam (\<alpha>_of 1) (top1_R_to_S1 ((1 - t) * angle_fam (\<alpha>_of 1) (f 1) + t * \<theta>p_fam (\<alpha>_of 1)))"
                  unfolding F_def by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 1) (top1_R_to_S1 ((1 - t) * angle_fam (\<alpha>_of 1) p + t * \<theta>p_fam (\<alpha>_of 1)))"
                  using hf1 by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 1) (top1_R_to_S1 ((1 - t) * \<theta>p_fam (\<alpha>_of 1) + t * \<theta>p_fam (\<alpha>_of 1)))"
                  using hangle_p[OF h\<alpha>1] by (by100 simp)
                also have "\<dots> = h_fam (\<alpha>_of 1) (top1_R_to_S1 (\<theta>p_fam (\<alpha>_of 1)))"
                  by (simp add: algebra_simps)
                also have "\<dots> = p"
                  using hh_fam_p[OF h\<alpha>1] .
                finally show "F (1, t) = p" .
              qed
              \<comment> \<open>Step 7: Continuity of F. This is the hard part.
                 F restricted to f\<inverse>(W(\<alpha>)\{p}) \<times> I is continuous (angle interpolation).
                 At points where f(s) = p, all branches give p, and F is continuous
                 by the convergence angle_fam(\<alpha>)(x) \<rightarrow> \<theta>p_fam(\<alpha>) as x \<rightarrow> p in W(\<alpha>).
                 Global continuity follows from the weak topology on \<Union>W(\<alpha>):
                 W(\<alpha>)\{p} are open in \<Union>W(\<alpha>), and {p} is closed.\<close>
              \<comment> \<open>Key fact: W(\<alpha>) is closed in \<Union>W(\<alpha>) = U_def \<inter> V_def.
                 Proof: C(\<alpha>) is closed in X (by weak topology: C(\<alpha>) \<inter> C(\<beta>) = {p} is closed in C(\<beta>) for \<beta>\<noteq>\<alpha>,
                 and C(\<alpha>) \<inter> C(\<alpha>) = C(\<alpha>) is closed in C(\<alpha>)). Then W(\<alpha>) = C(\<alpha>) \<inter> \<Union>W(\<beta>)
                 is the intersection of a closed set with the subspace, hence closed in the subspace.\<close>
              have hW_closed_UV: "\<And>\<alpha>. \<alpha> \<in> {..<n} \<Longrightarrow> closedin_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) (W \<alpha>)"
              proof -
                fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                \<comment> \<open>C(\<alpha>) is closed in X.\<close>
                have hC\<alpha>_closed_X: "closedin_on X TX (C \<alpha>)"
                proof -
                  have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                  have hall: "\<forall>\<beta>\<in>{..<n}. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                  proof (intro ballI)
                    fix \<beta> assume h\<beta>: "\<beta> \<in> {..<n}"
                    show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                    proof (cases "\<beta> = \<alpha>")
                      case True
                      hence "C \<beta> \<inter> C \<alpha> = C \<beta>" by (by100 blast)
                      moreover have "is_topology_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                        by (rule subspace_topology_is_topology_on[OF hTX])
                           (use hC_props h\<beta> in \<open>by100 blast\<close>)
                      ultimately show ?thesis
                        by (simp add: closedin_on_def is_topology_on_def)
                    next
                      case False
                      have hC\<beta>\<alpha>_eq: "C \<beta> \<inter> C \<alpha> = {p}" using hC_inter h\<beta> h\<alpha> False by (by100 blast)
                      \<comment> \<open>{p} is closed in C(\<beta>) since X is Hausdorff, hence {p} closed in X,
                         hence {p} \<inter> C(\<beta>) = {p} is closed in C(\<beta>) by Theorem 17.2.\<close>
                      have hp_closed_X: "closedin_on X TX {p}"
                      proof -
                        have hp_X: "p \<in> X" using hC_props h\<alpha> by (by100 blast)
                        have hH: "is_hausdorff_on X TX"
                          using hwedge unfolding top1_is_wedge_of_circles_on_def by (by100 blast)
                        show ?thesis by (rule singleton_closed_in_hausdorff[OF hH hp_X])
                      qed
                      have hC\<beta>_sub: "C \<beta> \<subseteq> X" using hC_props h\<beta> by (by100 blast)
                      have hp_C\<beta>: "p \<in> C \<beta>" using hC_props h\<beta> by (by100 blast)
                      have "{p} = {p} \<inter> C \<beta>" using hp_C\<beta> by (by100 blast)
                      hence "\<exists>D. closedin_on X TX D \<and> {p} = D \<inter> C \<beta>"
                        using hp_closed_X by (by100 blast)
                      hence "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) {p}"
                        using iffD2[OF Theorem_17_2[OF hTX hC\<beta>_sub, of "{p}"]]
                        by (by100 blast)
                      thus ?thesis using hC\<beta>\<alpha>_eq by (by100 simp)
                    qed
                  qed
                  show ?thesis using iffD2[OF hC_weak[rule_format, OF hC\<alpha>_sub]] hall by (by100 blast)
                qed
                \<comment> \<open>W(\<alpha>) = C(\<alpha>) \<inter> (U_def \<inter> V_def)\<close>
                have hW_eq_inter: "W \<alpha> = C \<alpha> \<inter> (U_def \<inter> V_def)"
                proof (intro set_eqI iffI)
                  fix x assume hx: "x \<in> W \<alpha>"
                  have "x \<in> C \<alpha>" using hx unfolding W_def by (by100 blast)
                  moreover have "x \<in> U_def \<inter> V_def" using hUV_eq h\<alpha> hx by (by100 blast)
                  ultimately show "x \<in> C \<alpha> \<inter> (U_def \<inter> V_def)" by (by100 blast)
                next
                  fix x assume hx: "x \<in> C \<alpha> \<inter> (U_def \<inter> V_def)"
                  hence hx_C: "x \<in> C \<alpha>" and hx_UV: "x \<in> U_def \<inter> V_def" by (by100 blast)+
                  have "x \<in> (\<Union>\<beta>\<in>{..<n}. W \<beta>)" using hx_UV hUV_eq by (by100 blast)
                  then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<n}" and hx_W\<beta>: "x \<in> W \<beta>" by (by100 blast)
                  have hx_C\<beta>: "x \<in> C \<beta>" using hx_W\<beta> unfolding W_def by (by100 blast)
                  show "x \<in> W \<alpha>"
                  proof (cases "\<alpha> = \<beta>")
                    case True thus ?thesis using hx_W\<beta> by (by100 simp)
                  next
                    case False
                    hence "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha> h\<beta> by (by100 blast)
                    hence "x = p" using hx_C hx_C\<beta> by (by100 blast)
                    thus "x \<in> W \<alpha>" using hp_W h\<alpha> by (by100 blast)
                  qed
                qed
                \<comment> \<open>Closed set \<inter> subspace = closed in subspace topology.\<close>
                show "closedin_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) (W \<alpha>)"
                  using iffD2[OF Theorem_17_2[OF hTX hUV_sub, of "W \<alpha>"]]
                        hC\<alpha>_closed_X hW_eq_inter by (by100 blast)
              qed
              \<comment> \<open>Step 7: Continuity of F.
                 Strategy: show F^{-1}(D) is closed for every closed D in the codomain.
                 {W(\<alpha>) | \<alpha> < n} is a finite closed cover of \<Union>W(\<alpha>).
                 f^{-1}(W(\<alpha>)) is closed in I (preimage of closed under continuous f).
                 f^{-1}(W(\<alpha>)) \<times> I is closed in I\<times>I.
                 F restricted to f^{-1}(W(\<alpha>)) \<times> I is continuous (composition of continuous maps).
                 F^{-1}(D) = \<Union>_\<alpha> (D-preimage on f^{-1}(W(\<alpha>))\<times>I), finite union of closed = closed.\<close>
              have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                  (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) F"
                sorry \<comment> \<open>Finite closed pasting argument.
                   Key ingredients already established:
                   (1) hW_closed_UV: each W(\<alpha>) is closed in \<Union>W(\<alpha>)
                   (2) hfam: h_fam and angle_fam give per-piece continuous contraction
                   (3) hf_cont: f is continuous I \<rightarrow> \<Union>W(\<alpha>)
                   (4) F on f^{-1}(W(\<alpha>))\<times>I equals h_fam(\<alpha>) \<circ> R_to_S1 \<circ> (linear interp with angle_fam)
                   which is a composition of continuous maps.
                   The proof uses Theorem_18_1(2) (preimage of closed is closed)
                   + closedin_Union_finite + Theorem_17_3.\<close>
              \<comment> \<open>Step 8: Assemble the path homotopy.\<close>
              have hconst_path: "top1_is_path_on (U_def \<inter> V_def) (subspace_topology X TX (U_def \<inter> V_def)) p p (top1_constant_path p)"
                by (rule top1_constant_path_is_path[OF hTUV hp_UV])
              show ?thesis
                unfolding top1_path_homotopic_on_def
                using hf_path hconst_path hF_cont hF_s0 hF_s1 hF_0t hF_1t by (by100 blast)
            qed
          qed
        qed
        \<comment> \<open>Key lemma: path in a piece lifts to a path in U_def or V_def.\<close>
        \<comment> \<open>If f is a path in A w.r.t. subspace_topology X TX A, and A \<subseteq> B \<subseteq> X,
            then f is a path in B w.r.t. subspace_topology X TX B.\<close>
        show "top1_path_connected_on U_def (subspace_topology X TX U_def)"
          unfolding top1_path_connected_on_def
        proof (intro conjI ballI)
          show "is_topology_on U_def (subspace_topology X TX U_def)"
            by (rule subspace_topology_is_topology_on[OF hTX hU_sub])
        next
          fix x y assume hx: "x \<in> U_def" and hy: "y \<in> U_def"
          \<comment> \<open>Get path from x to p in some piece of U_def.\<close>
          have "\<exists>f. top1_is_path_on U_def (subspace_topology X TX U_def) x p f"
          proof -
            \<comment> \<open>x is in some C(\<alpha>) with \<alpha> < n-1, or in W(n-1).\<close>
            have "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<or> x \<in> W (n-1)"
              using hx unfolding U_def_def by (by100 blast)
            thus ?thesis
            proof
              assume "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>)"
              then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<(n-1)}" and hx\<alpha>: "x \<in> C \<alpha>" by (by100 blast)
              have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
              \<comment> \<open>Path from x to p in C(\<alpha>).\<close>
              have hp\<alpha>: "p \<in> C \<alpha>" using hC_props h\<alpha>n by (by100 blast)
              obtain f where hf: "top1_is_path_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) x p f"
                using hC_pc h\<alpha>n hx\<alpha> hp\<alpha> unfolding top1_path_connected_on_def by (by100 blast)
              \<comment> \<open>Lift path from C(\<alpha>) to U_def using codomain_enlarge.\<close>
              have hcont_f: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) f"
                using hf unfolding top1_is_path_on_def by (by100 blast)
              have hC\<alpha>_sub_U: "C \<alpha> \<subseteq> U_def" using hC_sub_U h\<alpha> by (by100 blast)
              have hcont_U: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  U_def (subspace_topology X TX U_def) f"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f hC\<alpha>_sub_U hU_sub])
              have hf0: "f 0 = x" and hf1: "f 1 = p"
                using hf unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on U_def (subspace_topology X TX U_def) x p f"
                unfolding top1_is_path_on_def using hcont_U hf0 hf1 by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              assume hxW: "x \<in> W (n-1)"
              \<comment> \<open>Path from x to p in W(n-1).\<close>
              have hp_Wn: "p \<in> W (n-1)" using hp_W hn1_in by (by100 blast)
              obtain f where hf: "top1_is_path_on (W (n-1)) (subspace_topology X TX (W (n-1))) x p f"
                using hW_pc hn1_in hxW hp_Wn unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_f: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (W (n-1)) (subspace_topology X TX (W (n-1))) f"
                using hf unfolding top1_is_path_on_def by (by100 blast)
              have hcont_U: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  U_def (subspace_topology X TX U_def) f"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f hWn_sub_U hU_sub])
              have hf0: "f 0 = x" and hf1: "f 1 = p"
                using hf unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on U_def (subspace_topology X TX U_def) x p f"
                unfolding top1_is_path_on_def using hcont_U hf0 hf1 by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
          qed
          then obtain f1 where hf1: "top1_is_path_on U_def (subspace_topology X TX U_def) x p f1"
            by (by100 blast)
          \<comment> \<open>Get path from p to y in some piece of U_def.\<close>
          have "\<exists>f. top1_is_path_on U_def (subspace_topology X TX U_def) p y f"
          proof -
            have "y \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>) \<or> y \<in> W (n-1)"
              using hy unfolding U_def_def by (by100 blast)
            thus ?thesis
            proof
              assume "y \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. C \<alpha>)"
              then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hy\<beta>: "y \<in> C \<beta>" by (by100 blast)
              have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
              have hp\<beta>: "p \<in> C \<beta>" using hC_props h\<beta>n by (by100 blast)
              obtain g where hg: "top1_is_path_on (C \<beta>) (subspace_topology X TX (C \<beta>)) p y g"
                using hC_pc h\<beta>n hp\<beta> hy\<beta> unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_g: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C \<beta>) (subspace_topology X TX (C \<beta>)) g"
                using hg unfolding top1_is_path_on_def by (by100 blast)
              have hC\<beta>_sub_U: "C \<beta> \<subseteq> U_def" using hC_sub_U h\<beta> by (by100 blast)
              have hcont_U: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  U_def (subspace_topology X TX U_def) g"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_g hC\<beta>_sub_U hU_sub])
              have hg0: "g 0 = p" and hg1: "g 1 = y"
                using hg unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on U_def (subspace_topology X TX U_def) p y g"
                unfolding top1_is_path_on_def using hcont_U hg0 hg1 by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              assume hyW: "y \<in> W (n-1)"
              have hp_Wn: "p \<in> W (n-1)" using hp_W hn1_in by (by100 blast)
              obtain g where hg: "top1_is_path_on (W (n-1)) (subspace_topology X TX (W (n-1))) p y g"
                using hW_pc hn1_in hp_Wn hyW unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_g: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (W (n-1)) (subspace_topology X TX (W (n-1))) g"
                using hg unfolding top1_is_path_on_def by (by100 blast)
              have hcont_U: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  U_def (subspace_topology X TX U_def) g"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_g hWn_sub_U hU_sub])
              have hg0: "g 0 = p" and hg1: "g 1 = y"
                using hg unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on U_def (subspace_topology X TX U_def) p y g"
                unfolding top1_is_path_on_def using hcont_U hg0 hg1 by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
          qed
          then obtain f2 where hf2: "top1_is_path_on U_def (subspace_topology X TX U_def) p y f2"
            by (by100 blast)
          \<comment> \<open>Concatenate paths x \<rightarrow> p and p \<rightarrow> y.\<close>
          have hTU: "is_topology_on U_def (subspace_topology X TX U_def)"
            by (rule subspace_topology_is_topology_on[OF hTX hU_sub])
          show "\<exists>f. top1_is_path_on U_def (subspace_topology X TX U_def) x y f"
            using top1_is_path_on_append[OF hTU hf1 hf2] by (by100 blast)
        qed
        show "top1_path_connected_on V_def (subspace_topology X TX V_def)"
          unfolding top1_path_connected_on_def
        proof (intro conjI ballI)
          show "is_topology_on V_def (subspace_topology X TX V_def)"
            by (rule subspace_topology_is_topology_on[OF hTX hV_sub])
        next
          fix x y assume hx: "x \<in> V_def" and hy: "y \<in> V_def"
          \<comment> \<open>Get path from x to p in some piece of V_def.\<close>
          have "\<exists>f. top1_is_path_on V_def (subspace_topology X TX V_def) x p f"
          proof -
            have "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>) \<or> x \<in> C (n-1)"
              using hx unfolding V_def_def by (by100 blast)
            thus ?thesis
            proof
              assume "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>)"
              then obtain \<alpha> where h\<alpha>: "\<alpha> \<in> {..<(n-1)}" and hx\<alpha>: "x \<in> W \<alpha>" by (by100 blast)
              have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
              have hp\<alpha>: "p \<in> W \<alpha>" using hp_W h\<alpha>n by (by100 blast)
              obtain f where hf: "top1_is_path_on (W \<alpha>) (subspace_topology X TX (W \<alpha>)) x p f"
                using hW_pc h\<alpha>n hx\<alpha> hp\<alpha> unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_f: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (W \<alpha>) (subspace_topology X TX (W \<alpha>)) f"
                using hf unfolding top1_is_path_on_def by (by100 blast)
              have hW\<alpha>_sub_V: "W \<alpha> \<subseteq> V_def" using hW_sub_V h\<alpha> by (by100 blast)
              have hcont_V: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  V_def (subspace_topology X TX V_def) f"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f hW\<alpha>_sub_V hV_sub])
              have hf0: "f 0 = x" and hf1: "f 1 = p"
                using hf unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on V_def (subspace_topology X TX V_def) x p f"
                unfolding top1_is_path_on_def using hcont_V hf0 hf1 by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              assume hxCn: "x \<in> C (n-1)"
              have hp_Cn': "p \<in> C (n-1)" using hp_Cn .
              obtain f where hf: "top1_is_path_on (C (n-1)) (subspace_topology X TX (C (n-1))) x p f"
                using hC_pc hn1_in hxCn hp_Cn' unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_f: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C (n-1)) (subspace_topology X TX (C (n-1))) f"
                using hf unfolding top1_is_path_on_def by (by100 blast)
              have hcont_V: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  V_def (subspace_topology X TX V_def) f"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_f hCn_sub_V hV_sub])
              have hf0: "f 0 = x" and hf1: "f 1 = p"
                using hf unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on V_def (subspace_topology X TX V_def) x p f"
                unfolding top1_is_path_on_def using hcont_V hf0 hf1 by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
          qed
          then obtain f1 where hf1: "top1_is_path_on V_def (subspace_topology X TX V_def) x p f1"
            by (by100 blast)
          \<comment> \<open>Get path from p to y.\<close>
          have "\<exists>f. top1_is_path_on V_def (subspace_topology X TX V_def) p y f"
          proof -
            have "y \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>) \<or> y \<in> C (n-1)"
              using hy unfolding V_def_def by (by100 blast)
            thus ?thesis
            proof
              assume "y \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>)"
              then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hy\<beta>: "y \<in> W \<beta>" by (by100 blast)
              have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
              have hp\<beta>: "p \<in> W \<beta>" using hp_W h\<beta>n by (by100 blast)
              obtain g where hg: "top1_is_path_on (W \<beta>) (subspace_topology X TX (W \<beta>)) p y g"
                using hW_pc h\<beta>n hp\<beta> hy\<beta> unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_g: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (W \<beta>) (subspace_topology X TX (W \<beta>)) g"
                using hg unfolding top1_is_path_on_def by (by100 blast)
              have hW\<beta>_sub_V: "W \<beta> \<subseteq> V_def" using hW_sub_V h\<beta> by (by100 blast)
              have hcont_V: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  V_def (subspace_topology X TX V_def) g"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_g hW\<beta>_sub_V hV_sub])
              have hg0: "g 0 = p" and hg1: "g 1 = y"
                using hg unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on V_def (subspace_topology X TX V_def) p y g"
                unfolding top1_is_path_on_def using hcont_V hg0 hg1 by (by100 blast)
              thus ?thesis by (by100 blast)
            next
              assume hyCn: "y \<in> C (n-1)"
              have hp_Cn': "p \<in> C (n-1)" using hp_Cn .
              obtain g where hg: "top1_is_path_on (C (n-1)) (subspace_topology X TX (C (n-1))) p y g"
                using hC_pc hn1_in hp_Cn' hyCn unfolding top1_path_connected_on_def by (by100 blast)
              have hcont_g: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  (C (n-1)) (subspace_topology X TX (C (n-1))) g"
                using hg unfolding top1_is_path_on_def by (by100 blast)
              have hcont_V: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  V_def (subspace_topology X TX V_def) g"
                by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_g hCn_sub_V hV_sub])
              have hg0: "g 0 = p" and hg1: "g 1 = y"
                using hg unfolding top1_is_path_on_def by (by100 blast)+
              have "top1_is_path_on V_def (subspace_topology X TX V_def) p y g"
                unfolding top1_is_path_on_def using hcont_V hg0 hg1 by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
          qed
          then obtain f2 where hf2: "top1_is_path_on V_def (subspace_topology X TX V_def) p y f2"
            by (by100 blast)
          \<comment> \<open>Concatenate paths x \<rightarrow> p and p \<rightarrow> y.\<close>
          have hTV: "is_topology_on V_def (subspace_topology X TX V_def)"
            by (rule subspace_topology_is_topology_on[OF hTX hV_sub])
          show "\<exists>f. top1_is_path_on V_def (subspace_topology X TX V_def) x y f"
            using top1_is_path_on_append[OF hTV hf1 hf2] by (by100 blast)
        qed
        show "p \<in> U_def \<inter> V_def"
        proof -
          have "p \<in> U_def"
            unfolding U_def_def using hp_X' by (by100 blast)
          moreover have "p \<in> V_def"
          proof -
            have "p \<in> C (n-1)" using hp_Cn .
            thus ?thesis unfolding V_def_def by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        show "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier U_def (subspace_topology X TX U_def) p)
            (top1_fundamental_group_mul U_def (subspace_topology X TX U_def) p)
            (top1_fundamental_group_carrier ?X' ?TX' p)
            (top1_fundamental_group_mul ?X' ?TX' p)"
        proof -
          have hdef_U: "top1_deformation_retract_of_on U_def (subspace_topology X TX U_def) ?X'"
          proof -
            \<comment> \<open>Step 1: X' \<subseteq> U_def.\<close>
            have hX'_sub_U: "?X' \<subseteq> U_def" unfolding U_def_def by (by100 blast)
            \<comment> \<open>Step 2: Build the deformation retraction homotopy H.
               For x \<in> X': H(x,t) = x (fixed).
               For x \<in> W(n-1): contract x toward p along the arc parameterization.
               These agree on X' \<inter> W(n-1) = {p} since p maps to \<theta>_p.\<close>
            \<comment> \<open>Get homeomorphism h: S1 \<rightarrow> C(n-1) and angle parameterization.\<close>
            obtain h_n where hh_n: "top1_homeomorphism_on top1_S1 top1_S1_topology
                ?Cn (subspace_topology X TX ?Cn) h_n"
              using hC_props hn1_in by (by100 blast)
            have hbij_n: "bij_betw h_n top1_S1 ?Cn"
              using hh_n unfolding top1_homeomorphism_on_def by (by100 blast)
            let ?hinv_n = "inv_into top1_S1 h_n"
            have hhinv_n: "top1_homeomorphism_on ?Cn (subspace_topology X TX ?Cn)
                top1_S1 top1_S1_topology ?hinv_n"
              by (rule homeomorphism_inverse[OF hh_n])
            have hbij_inv_n: "bij_betw ?hinv_n ?Cn top1_S1"
              using hhinv_n unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>q' = hinv(q(n-1)), removed point in S1.\<close>
            have hq_in_n: "q (n-1) \<in> ?Cn" using hq hn1_in by (by100 blast)
            define q'_n where "q'_n = ?hinv_n (q (n-1))"
            have hq'_S1: "q'_n \<in> top1_S1"
              using hbij_inv_n hq_in_n unfolding q'_n_def bij_betw_def by (by100 blast)
            \<comment> \<open>p' = hinv(p), basepoint in S1.\<close>
            define p'_n where "p'_n = ?hinv_n p"
            have hp'_S1: "p'_n \<in> top1_S1"
              using hbij_inv_n hp_Cn unfolding p'_n_def bij_betw_def by (by100 blast)
            have hp'_ne_q': "p'_n \<noteq> q'_n"
            proof
              assume "p'_n = q'_n"
              hence "?hinv_n p = ?hinv_n (q (n-1))" unfolding p'_n_def q'_n_def .
              hence "h_n (?hinv_n p) = h_n (?hinv_n (q (n-1)))" by (by100 simp)
              hence "p = q (n-1)"
                using bij_betw_inv_into_right[OF hbij_n hp_Cn]
                      bij_betw_inv_into_right[OF hbij_n hq_in_n] by (by100 simp)
              thus False using hq hn1_in by (by100 blast)
            qed
            \<comment> \<open>Get angle \<theta>_q for q' and \<theta>_p for p' in (\<theta>_q, \<theta>_q + 1).\<close>
            obtain \<theta>q_n where h\<theta>q_n: "top1_R_to_S1 \<theta>q_n = q'_n"
            proof -
              have heq: "fst q'_n ^ 2 + snd q'_n ^ 2 = 1" using hq'_S1 unfolding top1_S1_def by (by100 simp)
              obtain \<theta> where "fst q'_n = cos \<theta>" "snd q'_n = sin \<theta>"
                using sincos_total_2pi heq by (by100 metis)
              hence "top1_R_to_S1 (\<theta> / (2 * pi)) = q'_n"
                unfolding top1_R_to_S1_def by (simp add: prod_eq_iff)
              thus ?thesis using that by (by100 blast)
            qed
            obtain \<theta>p_n where h\<theta>p_n: "top1_R_to_S1 \<theta>p_n = p'_n"
                and h\<theta>p_range: "\<theta>q_n < \<theta>p_n \<and> \<theta>p_n < \<theta>q_n + 1"
            proof -
              have heq: "fst p'_n ^ 2 + snd p'_n ^ 2 = 1" using hp'_S1 unfolding top1_S1_def by (by100 simp)
              obtain \<theta>0_raw where hcos: "fst p'_n = cos \<theta>0_raw" and hsin: "snd p'_n = sin \<theta>0_raw"
                using sincos_total_2pi heq by (by100 metis)
              define \<theta>0 where "\<theta>0 = \<theta>0_raw / (2 * pi)"
              have h\<theta>0: "top1_R_to_S1 \<theta>0 = p'_n"
                unfolding top1_R_to_S1_def \<theta>0_def using hcos hsin by (simp add: prod_eq_iff)
              define k where "k = \<lfloor>\<theta>0 - \<theta>q_n\<rfloor>"
              define \<theta>a where "\<theta>a = \<theta>0 - of_int k"
              have h\<theta>a_R: "top1_R_to_S1 \<theta>a = p'_n"
              proof -
                have "top1_R_to_S1 \<theta>a = top1_R_to_S1 (\<theta>0 + of_int (-k))"
                  unfolding \<theta>a_def by (by100 simp)
                also have "\<dots> = top1_R_to_S1 \<theta>0"
                  by (rule top1_R_to_S1_int_shift_early)
                also have "\<dots> = p'_n" by (rule h\<theta>0)
                finally show ?thesis .
              qed
              have h\<theta>a_range: "\<theta>q_n \<le> \<theta>a \<and> \<theta>a < \<theta>q_n + 1"
              proof -
                have "of_int k \<le> \<theta>0 - \<theta>q_n \<and> \<theta>0 - \<theta>q_n < of_int k + 1"
                  unfolding k_def by linarith
                thus ?thesis unfolding \<theta>a_def by (by100 linarith)
              qed
              \<comment> \<open>Need \<theta>a \<noteq> \<theta>q_n (since p' \<noteq> q').\<close>
              have h\<theta>a_ne: "\<theta>a \<noteq> \<theta>q_n"
              proof
                assume "\<theta>a = \<theta>q_n"
                hence "top1_R_to_S1 \<theta>a = top1_R_to_S1 \<theta>q_n" by (by100 simp)
                hence "p'_n = q'_n" using h\<theta>a_R h\<theta>q_n by (by100 simp)
                thus False using hp'_ne_q' by (by100 blast)
              qed
              hence h\<theta>a_strict: "\<theta>q_n < \<theta>a" using h\<theta>a_range by (by100 linarith)
              have "\<theta>q_n < \<theta>a \<and> \<theta>a < \<theta>q_n + 1" using h\<theta>a_strict h\<theta>a_range by (by100 linarith)
              thus ?thesis using that h\<theta>a_R by (by100 blast)
            qed
            \<comment> \<open>The angle function: for x \<in> W(n-1), map to the unique angle in (\<theta>_q, \<theta>_q+1).\<close>
            \<comment> \<open>Define \<theta>: W(n-1) \<rightarrow> (\<theta>_q, \<theta>_q+1) by composing hinv with R_to_S1^{-1}.\<close>
            \<comment> \<open>Every point in W(n-1) maps to S1 - {q'}, which lifts to (\<theta>_q, \<theta>_q+1).\<close>
            define angle_n :: "'a \<Rightarrow> real" where
              "angle_n x = (THE \<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x)" for x
            \<comment> \<open>For the deformation retraction, define H on U_def \<times> I.\<close>
            define H_U :: "'a \<times> real \<Rightarrow> 'a" where
              "H_U = (\<lambda>(x, t). if x \<in> ?X' then x
                     else h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
            \<comment> \<open>Key property of angle_n: for x \<in> W(n-1), angle_n x \<in> (\<theta>q, \<theta>q+1).\<close>
            have hangle_n_spec: "\<And>x. x \<in> W (n-1) \<Longrightarrow>
                \<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1 \<and>
                top1_R_to_S1 (angle_n x) = ?hinv_n x"
            proof -
              fix x assume hxW: "x \<in> W (n-1)"
              hence hx_Cn: "x \<in> ?Cn" unfolding W_def by (by100 blast)
              have hhinv_x: "?hinv_n x \<in> top1_S1"
                using hbij_inv_n hx_Cn unfolding bij_betw_def by (by100 blast)
              have hhinv_x_ne_q': "?hinv_n x \<noteq> q'_n"
              proof
                assume "?hinv_n x = q'_n"
                hence "h_n (?hinv_n x) = h_n q'_n" by (by100 simp)
                hence "x = q (n-1)"
                  using bij_betw_inv_into_right[OF hbij_n hx_Cn]
                  unfolding q'_n_def using bij_betw_inv_into_right[OF hbij_n hq_in_n] by (by100 simp)
                moreover have "x \<noteq> q (n-1)" using hxW unfolding W_def by (by100 blast)
                ultimately show False by (by100 blast)
              qed
              \<comment> \<open>Step 1: get \<theta>0 with R_to_S1(\<theta>0) = hinv(x) and \<theta>q_n < \<theta>0 < \<theta>q_n + 1.\<close>
              have heq_x: "fst (?hinv_n x) ^ 2 + snd (?hinv_n x) ^ 2 = 1"
                using hhinv_x unfolding top1_S1_def by (by100 simp)
              obtain \<theta>r where hcos_x: "fst (?hinv_n x) = cos \<theta>r" and hsin_x: "snd (?hinv_n x) = sin \<theta>r"
                using sincos_total_2pi heq_x by (by100 metis)
              define \<theta>_raw_x where "\<theta>_raw_x = \<theta>r / (2 * pi)"
              have h_raw_x: "top1_R_to_S1 \<theta>_raw_x = ?hinv_n x"
                unfolding top1_R_to_S1_def \<theta>_raw_x_def using hcos_x hsin_x by (simp add: prod_eq_iff)
              define k_x where "k_x = \<lfloor>\<theta>_raw_x - \<theta>q_n\<rfloor>"
              define \<theta>0_x where "\<theta>0_x = \<theta>_raw_x - of_int k_x"
              have h\<theta>0_x_R: "top1_R_to_S1 \<theta>0_x = ?hinv_n x"
              proof -
                have "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 (\<theta>_raw_x + of_int (-k_x))"
                  unfolding \<theta>0_x_def by (by100 simp)
                also have "\<dots> = top1_R_to_S1 \<theta>_raw_x" by (rule top1_R_to_S1_int_shift_early)
                also have "\<dots> = ?hinv_n x" by (rule h_raw_x)
                finally show ?thesis .
              qed
              have h\<theta>0_x_range: "\<theta>q_n \<le> \<theta>0_x \<and> \<theta>0_x < \<theta>q_n + 1"
                unfolding \<theta>0_x_def k_x_def by linarith
              have "\<theta>0_x \<noteq> \<theta>q_n"
              proof
                assume "\<theta>0_x = \<theta>q_n"
                hence "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 \<theta>q_n" by (by100 simp)
                hence "?hinv_n x = q'_n" using h\<theta>0_x_R h\<theta>q_n by (by100 simp)
                thus False using hhinv_x_ne_q' by (by100 blast)
              qed
              hence h\<theta>0_x_strict: "\<theta>q_n < \<theta>0_x" using h\<theta>0_x_range by (by100 linarith)
              have h\<theta>0_x: "\<theta>q_n < \<theta>0_x \<and> \<theta>0_x < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta>0_x = ?hinv_n x"
                using h\<theta>0_x_strict h\<theta>0_x_range h\<theta>0_x_R by (by100 blast)
              \<comment> \<open>Uniqueness.\<close>
              have huniq_x: "\<And>\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x \<Longrightarrow> \<theta> = \<theta>0_x"
              proof -
                fix \<theta> assume h\<theta>: "\<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
                hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>0_x" using h\<theta>0_x_R by (by100 simp)
                hence "cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x) \<and> sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x)"
                  unfolding top1_R_to_S1_def by (by100 simp)
                hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x)"
                  by (by100 blast)
                then obtain j :: int where hj: "2*pi*\<theta> = 2*pi*\<theta>0_x + 2*pi*of_int j"
                  using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                have "2*pi*\<theta> - 2*pi*\<theta>0_x = 2*pi*of_int j" using hj by (by100 linarith)
                hence hd: "2*pi*(\<theta> - \<theta>0_x) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                hence "2*pi \<noteq> 0" by (by100 linarith)
                hence "\<theta> - \<theta>0_x = of_int j" using hd by (by100 simp)
                moreover have "\<theta> - \<theta>0_x > -1 \<and> \<theta> - \<theta>0_x < 1" using h\<theta> h\<theta>0_x by (by100 linarith)
                ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                hence "j = 0" by (by100 linarith)
                thus "\<theta> = \<theta>0_x" using \<open>\<theta> - \<theta>0_x = of_int j\<close> by (by100 simp)
              qed
              \<comment> \<open>THE gives the unique \<theta>0_x.\<close>
              have hex1_x: "\<exists>!\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
              proof (rule ex_ex1I)
                show "\<exists>\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
                  using h\<theta>0_x by (by100 blast)
              next
                fix a b assume ha: "\<theta>q_n < a \<and> a < \<theta>q_n + 1 \<and> top1_R_to_S1 a = ?hinv_n x"
                    and hb: "\<theta>q_n < b \<and> b < \<theta>q_n + 1 \<and> top1_R_to_S1 b = ?hinv_n x"
                show "a = b" using huniq_x[OF ha] huniq_x[OF hb] by (by100 simp)
              qed
              have hthe_x: "(THE \<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x) = \<theta>0_x"
                by (rule the1_equality[OF hex1_x h\<theta>0_x])
              show "\<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1 \<and>
                  top1_R_to_S1 (angle_n x) = ?hinv_n x"
                unfolding angle_n_def using hthe_x h\<theta>0_x by (by100 simp)
            qed
            \<comment> \<open>Note: for x \<in> X' \<inter> W(n-1) = {p}, both branches agree:
               x = p, and angle_n p = \<theta>p_n, so
               h_n(R_to_S1((1-t)*\<theta>p_n + t*\<theta>p_n)) = h_n(R_to_S1(\<theta>p_n)) = h_n(p'_n) = p.\<close>
            have hh_n_p'_eq: "h_n p'_n = p"
              unfolding p'_n_def using bij_betw_inv_into_right[OF hbij_n hp_Cn] .
            \<comment> \<open>Properties of H_U.\<close>
            have hH_U_0: "\<forall>x\<in>U_def. H_U (x, 0) = x"
            proof (intro ballI)
              fix x assume hx: "x \<in> U_def"
              show "H_U (x, 0) = x"
              proof (cases "x \<in> ?X'")
                case True thus ?thesis unfolding H_U_def by (by100 simp)
              next
                case False
                hence hxW: "x \<in> W (n-1)" using hx unfolding U_def_def by (by100 blast)
                hence hx_Cn: "x \<in> ?Cn" unfolding W_def by (by100 blast)
                \<comment> \<open>angle_n x is the unique \<theta> with R_to_S1 \<theta> = hinv x, and h(hinv(x)) = x.\<close>
                have hhinv_x: "?hinv_n x \<in> top1_S1"
                  using hbij_inv_n hx_Cn unfolding bij_betw_def by (by100 blast)
                have hhinv_x_ne_q': "?hinv_n x \<noteq> q'_n"
                proof
                  assume "?hinv_n x = q'_n"
                  hence "h_n (?hinv_n x) = h_n q'_n" by (by100 simp)
                  hence "x = q (n-1)"
                    using bij_betw_inv_into_right[OF hbij_n hx_Cn]
                    unfolding q'_n_def using bij_betw_inv_into_right[OF hbij_n hq_in_n] by (by100 simp)
                  moreover have "x \<noteq> q (n-1)" using hxW unfolding W_def by (by100 blast)
                  ultimately show False by (by100 blast)
                qed
                \<comment> \<open>angle_n x satisfies R_to_S1(angle_n x) = hinv x.\<close>
                have h_angle_spec: "\<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1 \<and>
                    top1_R_to_S1 (angle_n x) = ?hinv_n x"
                proof -
                  \<comment> \<open>Step 1: get \<theta>0 with R_to_S1(\<theta>0) = hinv(x) and \<theta>q_n < \<theta>0 < \<theta>q_n + 1.\<close>
                  have heq: "fst (?hinv_n x) ^ 2 + snd (?hinv_n x) ^ 2 = 1"
                    using hhinv_x unfolding top1_S1_def by (by100 simp)
                  obtain \<theta>r where hcos: "fst (?hinv_n x) = cos \<theta>r" and hsin: "snd (?hinv_n x) = sin \<theta>r"
                    using sincos_total_2pi heq by (by100 metis)
                  define \<theta>_raw where "\<theta>_raw = \<theta>r / (2 * pi)"
                  have h_raw: "top1_R_to_S1 \<theta>_raw = ?hinv_n x"
                    unfolding top1_R_to_S1_def \<theta>_raw_def using hcos hsin by (simp add: prod_eq_iff)
                  define k where "k = \<lfloor>\<theta>_raw - \<theta>q_n\<rfloor>"
                  define \<theta>0 where "\<theta>0 = \<theta>_raw - of_int k"
                  have h\<theta>0_R: "top1_R_to_S1 \<theta>0 = ?hinv_n x"
                  proof -
                    have "top1_R_to_S1 \<theta>0 = top1_R_to_S1 (\<theta>_raw + of_int (-k))"
                      unfolding \<theta>0_def by (by100 simp)
                    also have "\<dots> = top1_R_to_S1 \<theta>_raw" by (rule top1_R_to_S1_int_shift_early)
                    also have "\<dots> = ?hinv_n x" by (rule h_raw)
                    finally show ?thesis .
                  qed
                  have h\<theta>0_range: "\<theta>q_n \<le> \<theta>0 \<and> \<theta>0 < \<theta>q_n + 1"
                    unfolding \<theta>0_def k_def by linarith
                  have "\<theta>0 \<noteq> \<theta>q_n"
                  proof
                    assume "\<theta>0 = \<theta>q_n"
                    hence "top1_R_to_S1 \<theta>0 = top1_R_to_S1 \<theta>q_n" by (by100 simp)
                    hence "?hinv_n x = q'_n" using h\<theta>0_R h\<theta>q_n by (by100 simp)
                    thus False using hhinv_x_ne_q' by (by100 blast)
                  qed
                  hence h\<theta>0_strict: "\<theta>q_n < \<theta>0" using h\<theta>0_range by (by100 linarith)
                  have h\<theta>0: "\<theta>q_n < \<theta>0 \<and> \<theta>0 < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta>0 = ?hinv_n x"
                    using h\<theta>0_strict h\<theta>0_range h\<theta>0_R by (by100 blast)
                  \<comment> \<open>Step 2: uniqueness: any \<theta> in (\<theta>q_n, \<theta>q_n+1) with R_to_S1 \<theta> = hinv(x) equals \<theta>0.\<close>
                  have huniq: "\<And>\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x \<Longrightarrow> \<theta> = \<theta>0"
                  proof -
                    fix \<theta> assume h\<theta>: "\<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
                    hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>0" using h\<theta>0_R by (by100 simp)
                    hence "cos (2*pi*\<theta>) = cos (2*pi*\<theta>0) \<and> sin (2*pi*\<theta>) = sin (2*pi*\<theta>0)"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>0) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>0)"
                      by (by100 blast)
                    then obtain j :: int where hj: "2*pi*\<theta> = 2*pi*\<theta>0 + 2*pi*of_int j"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    have "2*pi*\<theta> - 2*pi*\<theta>0 = 2*pi*of_int j" using hj by (by100 linarith)
                    hence hd: "2*pi*(\<theta> - \<theta>0) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                    have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                    hence "2*pi \<noteq> 0" by (by100 linarith)
                    hence "\<theta> - \<theta>0 = of_int j" using hd by (by100 simp)
                    moreover have "\<theta> - \<theta>0 > -1 \<and> \<theta> - \<theta>0 < 1" using h\<theta> h\<theta>0 by (by100 linarith)
                    ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "j = 0" by (by100 linarith)
                    thus "\<theta> = \<theta>0" using \<open>\<theta> - \<theta>0 = of_int j\<close> by (by100 simp)
                  qed
                  \<comment> \<open>Step 3: THE gives the unique \<theta>0.\<close>
                  have hex1: "\<exists>!\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
                  proof (rule ex_ex1I)
                    show "\<exists>\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x"
                      using h\<theta>0 by (by100 blast)
                  next
                    fix a b assume ha: "\<theta>q_n < a \<and> a < \<theta>q_n + 1 \<and> top1_R_to_S1 a = ?hinv_n x"
                        and hb: "\<theta>q_n < b \<and> b < \<theta>q_n + 1 \<and> top1_R_to_S1 b = ?hinv_n x"
                    show "a = b" using huniq[OF ha] huniq[OF hb] by (by100 simp)
                  qed
                  have hthe: "(THE \<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n x) = \<theta>0"
                    by (rule the1_equality[OF hex1 h\<theta>0])
                  show ?thesis unfolding angle_n_def using hthe h\<theta>0 by (by100 simp)
                qed
                hence "H_U (x, 0) = h_n (top1_R_to_S1 ((1 - 0) * angle_n x + 0 * \<theta>p_n))"
                  using False unfolding H_U_def by (by100 simp)
                also have "(1 - 0) * angle_n x + 0 * \<theta>p_n = angle_n x" by (by100 simp)
                also have "top1_R_to_S1 (angle_n x) = ?hinv_n x" using h_angle_spec by (by100 blast)
                also have "h_n (?hinv_n x) = x"
                  using bij_betw_inv_into_right[OF hbij_n hx_Cn] .
                finally show ?thesis .
              qed
            qed
            have hH_U_1: "\<forall>x\<in>U_def. H_U (x, 1) \<in> ?X'"
            proof (intro ballI)
              fix x assume hx: "x \<in> U_def"
              show "H_U (x, 1) \<in> ?X'"
              proof (cases "x \<in> ?X'")
                case True thus ?thesis unfolding H_U_def by (by100 simp)
              next
                case False
                hence "H_U (x, 1) = h_n (top1_R_to_S1 ((1 - 1) * angle_n x + 1 * \<theta>p_n))"
                  unfolding H_U_def by (by100 simp)
                also have "(1 - 1) * angle_n x + 1 * \<theta>p_n = \<theta>p_n" by (by100 simp)
                also have "top1_R_to_S1 \<theta>p_n = p'_n" using h\<theta>p_n .
                also have "h_n p'_n = p" using hh_n_p'_eq .
                finally show ?thesis using hp_X' by (by100 simp)
              qed
            qed
            have hH_U_A: "\<forall>a\<in>?X'. \<forall>t\<in>I_set. H_U (a, t) = a"
            proof (intro ballI)
              fix a t assume ha: "a \<in> ?X'" and ht: "t \<in> I_set"
              show "H_U (a, t) = a" unfolding H_U_def using ha by (by100 simp)
            qed
            \<comment> \<open>The continuity of H_U w.r.t. the subspace (weak) topology is the hard part.
               H_U is continuous on X' \<times> I (trivially, identity) and on W(n-1) \<times> I
               (composition of continuous maps). The gluing is continuous because
               X' \<inter> W(n-1) = {p} and both branches agree there.
               Continuity w.r.t. the weak topology follows from the coherent topology
               condition: a set is open iff its intersection with each C(\<alpha>) is open.\<close>
            have hH_U_cont: "top1_continuous_map_on (U_def \<times> I_set)
                (product_topology_on (subspace_topology X TX U_def) I_top)
                U_def (subspace_topology X TX U_def) H_U"
            proof -
              let ?TU = "subspace_topology X TX U_def"
              let ?TI = "I_top"
              let ?TUI = "product_topology_on ?TU ?TI"
              have hTI: "is_topology_on I_set ?TI"
                by (rule top1_unit_interval_topology_is_topology_on)
              have hTU: "is_topology_on U_def ?TU"
                by (rule subspace_topology_is_topology_on[OF hTX hU_sub])
              have hTUI: "is_topology_on (U_def \<times> I_set) ?TUI"
                by (rule product_topology_on_is_topology_on[OF hTU hTI])
              \<comment> \<open>Step 1: X' is closed in X (via coherent topology).\<close>
              have hX'_closed_X: "closedin_on X TX ?X'"
              proof -
                have hX'_sub_X: "?X' \<subseteq> X" using hX'_sub .
                have hall: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?X')"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                  show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?X')"
                  proof (cases "\<alpha> \<in> {..<(n-1)}")
                    case True
                    hence "C \<alpha> \<inter> ?X' = C \<alpha>" by (by100 blast)
                    moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha>)"
                    proof (rule closedin_intro)
                      show "C \<alpha> \<subseteq> C \<alpha>" by (by100 blast)
                      show "C \<alpha> - C \<alpha> \<in> subspace_topology X TX (C \<alpha>)"
                      proof -
                        have "C \<alpha> - C \<alpha> = {}" by (by100 blast)
                        moreover have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                        moreover have "{} \<in> subspace_topology X TX (C \<alpha>)"
                          using subspace_topology_is_topology_on[OF hTX \<open>C \<alpha> \<subseteq> X\<close>]
                          unfolding is_topology_on_def by (by100 blast)
                        ultimately show ?thesis by (by100 simp)
                      qed
                    qed
                    ultimately show ?thesis by (by100 simp)
                  next
                    case False
                    hence h\<alpha>_eq: "\<alpha> = n - 1" using h\<alpha> hn2 by (by100 simp)
                    hence "C \<alpha> \<inter> ?X' = {p}"
                    proof -
                      have "C (n-1) \<inter> ?X' = {p}"
                      proof -
                        have "p \<in> C (n-1) \<inter> ?X'" using hp_Cn hp_X' by (by100 blast)
                        moreover have "\<forall>x. x \<in> C (n-1) \<inter> ?X' \<longrightarrow> x = p"
                        proof (intro allI impI)
                          fix x assume "x \<in> C (n-1) \<inter> ?X'"
                          hence hxCn: "x \<in> C (n-1)" and hxX': "x \<in> ?X'" by (by100 blast)+
                          from hxX' obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hx\<beta>: "x \<in> C \<beta>" by (by100 blast)
                          have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
                          have "\<beta> \<noteq> n - 1" using h\<beta> by (by100 simp)
                          hence "C \<beta> \<inter> C (n-1) = {p}" using hC_inter h\<beta>n hn1_in by (by100 blast)
                          thus "x = p" using hx\<beta> hxCn by (by100 blast)
                        qed
                        ultimately show ?thesis by (by100 blast)
                      qed
                      thus ?thesis using h\<alpha>_eq by (by100 simp)
                    qed
                    moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) {p}"
                    proof -
                      have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                      have hp_C\<alpha>: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                      have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
                        by (rule hausdorff_subspace[OF hHausdorff hC\<alpha>_sub])
                      thus ?thesis using hp_C\<alpha>
                        by (rule singleton_closed_in_hausdorff)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                qed
                show ?thesis using iffD2[OF hC_weak[rule_format, OF hX'_sub_X] hall] .
              qed
              \<comment> \<open>Step 2: C(n-1) is closed in X.\<close>
              have hCn_closed_X: "closedin_on X TX ?Cn"
              proof -
                have hCn_sub_X: "?Cn \<subseteq> X" using hCn_sub .
                have hall: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?Cn)"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                  show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?Cn)"
                  proof (cases "\<alpha> = n - 1")
                    case True
                    hence "C \<alpha> \<inter> ?Cn = C \<alpha>" by (by100 simp)
                    moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha>)"
                    proof (rule closedin_intro)
                      show "C \<alpha> \<subseteq> C \<alpha>" by (by100 blast)
                      show "C \<alpha> - C \<alpha> \<in> subspace_topology X TX (C \<alpha>)"
                      proof -
                        have "C \<alpha> - C \<alpha> = {}" by (by100 blast)
                        moreover have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                        moreover have "{} \<in> subspace_topology X TX (C \<alpha>)"
                          using subspace_topology_is_topology_on[OF hTX \<open>C \<alpha> \<subseteq> X\<close>]
                          unfolding is_topology_on_def by (by100 blast)
                        ultimately show ?thesis by (by100 simp)
                      qed
                    qed
                    ultimately show ?thesis by (by100 simp)
                  next
                    case False
                    hence h\<alpha>_ne: "\<alpha> \<noteq> n - 1" .
                    hence "C \<alpha> \<inter> ?Cn = {p}" using hC_inter h\<alpha> hn1_in by (by100 blast)
                    moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) {p}"
                    proof -
                      have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                      have hp_C\<alpha>: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                      have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
                        by (rule hausdorff_subspace[OF hHausdorff hC\<alpha>_sub])
                      thus ?thesis using hp_C\<alpha>
                        by (rule singleton_closed_in_hausdorff)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                qed
                show ?thesis using iffD2[OF hC_weak[rule_format, OF hCn_sub_X] hall] .
              qed
              \<comment> \<open>Step 3: X' is closed in U_def.\<close>
              have hX'_closed_U: "closedin_on U_def ?TU ?X'"
              proof -
                have "?X' = ?X' \<inter> U_def"
                  using hX'_sub_U by (by100 blast)
                thus ?thesis
                  using iffD2[OF Theorem_17_2[OF hTX hU_sub]] hX'_closed_X by (by100 blast)
              qed
              \<comment> \<open>Step 4: W(n-1) is closed in U_def (since W(n-1) = C(n-1) \<inter> U_def and C(n-1) is closed in X).\<close>
              have hWn_closed_U: "closedin_on U_def ?TU (W (n-1))"
              proof -
                have "W (n-1) = ?Cn \<inter> U_def"
                proof -
                  have "W (n-1) = ?Cn - {q (n-1)}" unfolding W_def by (by100 simp)
                  moreover have "q (n-1) \<notin> U_def"
                  proof -
                    have "q (n-1) \<notin> ?X'"
                    proof
                      assume "q (n-1) \<in> ?X'"
                      then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hq\<beta>: "q (n-1) \<in> C \<beta>" by (by100 blast)
                      have h\<beta>n: "\<beta> \<in> {..<n}"
                      proof -
                        have "\<beta> < n - 1" using h\<beta> by (by100 simp)
                        hence "\<beta> < n" using hn2 by (by100 simp)
                        thus ?thesis by (by100 simp)
                      qed
                      have "\<beta> \<noteq> n - 1" using h\<beta> by (by100 simp)
                      hence "C \<beta> \<inter> ?Cn = {p}" using hC_inter h\<beta>n hn1_in by (by100 blast)
                      hence "q (n-1) = p" using hq\<beta> hq_in_n by (by100 blast)
                      thus False using hq hn1_in by (by100 blast)
                    qed
                    moreover have "q (n-1) \<notin> W (n-1)" unfolding W_def by (by100 blast)
                    ultimately show ?thesis unfolding U_def_def by (by100 blast)
                  qed
                  ultimately show ?thesis
                  proof -
                    have "W (n-1) \<subseteq> ?Cn" unfolding W_def by (by100 blast)
                    moreover have "W (n-1) \<subseteq> U_def" unfolding U_def_def by (by100 blast)
                    moreover have "\<forall>x. x \<in> ?Cn \<and> x \<in> U_def \<longrightarrow> x \<in> W (n-1)"
                    proof (intro allI impI)
                      fix x assume hx: "x \<in> ?Cn \<and> x \<in> U_def"
                      hence hxCn: "x \<in> ?Cn" and hxU: "x \<in> U_def" by (by100 blast)+
                      show "x \<in> W (n-1)"
                      proof (rule ccontr)
                        assume "x \<notin> W (n-1)"
                        hence "x = q (n-1)" using hxCn unfolding W_def by (by100 blast)
                        thus False using \<open>q (n-1) \<notin> U_def\<close> hxU by (by100 blast)
                      qed
                    qed
                    ultimately show ?thesis by (by100 blast)
                  qed
                qed
                thus ?thesis
                  using iffD2[OF Theorem_17_2[OF hTX hU_sub]] hCn_closed_X by (by100 blast)
              qed
              \<comment> \<open>Step 5: X' \<times> I_set \<union> W(n-1) \<times> I_set = U_def \<times> I_set.\<close>
              have hcover: "(?X' \<times> I_set) \<union> (W (n-1) \<times> I_set) = U_def \<times> I_set"
              proof -
                have "U_def = ?X' \<union> W (n-1)" unfolding U_def_def by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              \<comment> \<open>Step 6: X' \<times> I_set is closed in U_def \<times> I_set.\<close>
              have hX'I_closed: "closedin_on (U_def \<times> I_set) ?TUI (?X' \<times> I_set)"
              proof (rule closedin_intro)
                show "?X' \<times> I_set \<subseteq> U_def \<times> I_set" using hX'_sub_U by (by100 blast)
                have "U_def \<times> I_set - ?X' \<times> I_set = (U_def - ?X') \<times> I_set" by (by100 blast)
                moreover have "(U_def - ?X') \<in> ?TU"
                  using hX'_closed_U unfolding closedin_on_def by (by100 blast)
                moreover have "I_set \<in> ?TI"
                  using hTI unfolding is_topology_on_def by (by100 blast)
                ultimately show "U_def \<times> I_set - ?X' \<times> I_set \<in> ?TUI"
                  using product_rect_open by (by100 simp)
              qed
              \<comment> \<open>Step 7: W(n-1) \<times> I_set is closed in U_def \<times> I_set.\<close>
              have hWnI_closed: "closedin_on (U_def \<times> I_set) ?TUI (W (n-1) \<times> I_set)"
              proof (rule closedin_intro)
                show "W (n-1) \<times> I_set \<subseteq> U_def \<times> I_set"
                  unfolding U_def_def by (by100 blast)
                have "U_def \<times> I_set - W (n-1) \<times> I_set = (U_def - W (n-1)) \<times> I_set" by (by100 blast)
                moreover have "(U_def - W (n-1)) \<in> ?TU"
                  using hWn_closed_U unfolding closedin_on_def by (by100 blast)
                moreover have "I_set \<in> ?TI"
                  using hTI unfolding is_topology_on_def by (by100 blast)
                ultimately show "U_def \<times> I_set - W (n-1) \<times> I_set \<in> ?TUI"
                  using product_rect_open by (by100 simp)
              qed
              \<comment> \<open>Step 8: H_U maps U_def \<times> I_set into U_def.\<close>
              have hH_U_range: "\<forall>p\<in>U_def \<times> I_set. H_U p \<in> U_def"
              proof (intro ballI)
                fix xt assume hxt: "xt \<in> U_def \<times> I_set"
                obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> U_def" and ht: "t \<in> I_set"
                  using hxt by (by100 blast)
                show "H_U xt \<in> U_def"
                proof (cases "x \<in> ?X'")
                  case True
                  hence "H_U xt = x" unfolding hxt_eq H_U_def by (by100 simp)
                  thus ?thesis using True hX'_sub_U by (by100 blast)
                next
                  case False
                  hence hxW: "x \<in> W (n-1)" using hx unfolding U_def_def by (by100 blast)
                  hence hx_Cn: "x \<in> ?Cn" unfolding W_def by (by100 blast)
                  have "H_U xt = h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))"
                    unfolding hxt_eq H_U_def using False by (by100 simp)
                  \<comment> \<open>The interpolated angle stays in (\<theta>q, \<theta>q+1), so the image avoids q(n-1).\<close>
                  have hangle: "\<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1"
                    using hangle_n_spec[OF hxW] by (by100 blast)
                  have ht_range: "0 \<le> t \<and> t \<le> 1"
                    using ht unfolding top1_unit_interval_def by (by100 simp)
                  have h\<theta>p_range: "\<theta>q_n < \<theta>p_n \<and> \<theta>p_n < \<theta>q_n + 1"
                    using h\<theta>p_range .
                  \<comment> \<open>Convex combination of two values in (\<theta>q, \<theta>q+1) stays in (\<theta>q, \<theta>q+1).\<close>
                  have hinterp_range: "\<theta>q_n < (1 - t) * angle_n x + t * \<theta>p_n \<and>
                      (1 - t) * angle_n x + t * \<theta>p_n < \<theta>q_n + 1"
                  proof (intro conjI)
                    show "\<theta>q_n < (1 - t) * angle_n x + t * \<theta>p_n"
                    proof -
                      \<comment> \<open>\<theta>q = (1-t)*\<theta>q + t*\<theta>q < (1-t)*angle + t*\<theta>p since angle > \<theta>q and \<theta>p > \<theta>q.\<close>
                      have "(1 - t) * (angle_n x - \<theta>q_n) \<ge> 0"
                        using hangle ht_range by (by100 simp)
                      moreover have "t * (\<theta>p_n - \<theta>q_n) \<ge> 0"
                        using h\<theta>p_range ht_range by (by100 simp)
                      moreover have "(1 - t) * (angle_n x - \<theta>q_n) + t * (\<theta>p_n - \<theta>q_n) > 0"
                      proof (cases "t = 0")
                        case True thus ?thesis using hangle by (by100 simp)
                      next
                        case False hence "t > 0" using ht_range by (by100 linarith)
                        have "t * (\<theta>p_n - \<theta>q_n) > 0" using h\<theta>p_range \<open>t > 0\<close> by (by100 simp)
                        thus ?thesis using \<open>(1 - t) * (angle_n x - \<theta>q_n) \<ge> 0\<close> by (by100 linarith)
                      qed
                      hence "(1-t)*angle_n x + t*\<theta>p_n > (1-t)*\<theta>q_n + t*\<theta>q_n"
                        by (simp add: algebra_simps)
                      moreover have "(1-t)*\<theta>q_n + t*\<theta>q_n = \<theta>q_n"
                        by (simp add: algebra_simps)
                      ultimately show ?thesis by (by100 linarith)
                    qed
                    show "(1 - t) * angle_n x + t * \<theta>p_n < \<theta>q_n + 1"
                    proof -
                      have h_bound_upper: "angle_n x - (\<theta>q_n+1) \<le> 0" using hangle by (by100 linarith)
                      have h_1mt_nn: "0 \<le> 1 - t" using ht_range by (by100 linarith)
                      have "(1-t)*(angle_n x - (\<theta>q_n+1)) \<le> 0"
                        using mult_nonneg_nonpos[OF h_1mt_nn h_bound_upper] .
                      moreover have "t*(\<theta>p_n - (\<theta>q_n+1)) < 0 \<or> t = 0"
                      proof (cases "t = 0")
                        case True thus ?thesis by (by100 simp)
                      next
                        case False hence "t > 0" using ht_range by (by100 linarith)
                        have "\<theta>p_n - (\<theta>q_n+1) < 0" using h\<theta>p_range by (by100 linarith)
                        hence "t*(\<theta>p_n - (\<theta>q_n+1)) < 0"
                          using \<open>t > 0\<close> by (simp add: mult_pos_neg)
                        thus ?thesis by (by100 linarith)
                      qed
                      moreover have "(1-t)*(angle_n x - (\<theta>q_n+1)) + t*(\<theta>p_n - (\<theta>q_n+1)) < 0"
                      proof (cases "t = 0")
                        case True thus ?thesis using hangle by (by100 simp)
                      next
                        case False hence "t > 0" using ht_range by (by100 linarith)
                        have "\<theta>p_n - (\<theta>q_n+1) < 0" using h\<theta>p_range by (by100 linarith)
                        hence "t*(\<theta>p_n - (\<theta>q_n+1)) < 0"
                          using \<open>t > 0\<close> by (simp add: mult_pos_neg)
                        thus ?thesis using \<open>(1-t)*(angle_n x - (\<theta>q_n+1)) \<le> 0\<close> by (by100 linarith)
                      qed
                      hence "(1-t)*angle_n x + t*\<theta>p_n < (1-t)*(\<theta>q_n+1) + t*(\<theta>q_n+1)"
                        by (simp add: algebra_simps)
                      moreover have "(1-t)*(\<theta>q_n+1) + t*(\<theta>q_n+1) = \<theta>q_n + 1"
                        by (simp add: algebra_simps)
                      ultimately show ?thesis by (by100 linarith)
                    qed
                  qed
                  \<comment> \<open>R_to_S1 of angle in (\<theta>q, \<theta>q+1) avoids q'_n.\<close>
                  have hne_q': "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) \<noteq> q'_n"
                  proof
                    assume heq: "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = q'_n"
                    hence "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = top1_R_to_S1 \<theta>q_n"
                      using h\<theta>q_n by (by100 simp)
                    hence "cos (2*pi*((1-t)*angle_n x + t*\<theta>p_n)) = cos (2*pi*\<theta>q_n)
                        \<and> sin (2*pi*((1-t)*angle_n x + t*\<theta>p_n)) = sin (2*pi*\<theta>q_n)"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin (2*pi*((1-t)*angle_n x + t*\<theta>p_n)) = sin (2*pi*\<theta>q_n)
                        \<and> cos (2*pi*((1-t)*angle_n x + t*\<theta>p_n)) = cos (2*pi*\<theta>q_n)"
                      by (by100 blast)
                    then obtain j :: int where
                        hj: "2*pi*((1-t)*angle_n x + t*\<theta>p_n) = 2*pi*\<theta>q_n + 2*pi*of_int j"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    have "2*pi*((1-t)*angle_n x + t*\<theta>p_n) - 2*pi*\<theta>q_n = 2*pi*of_int j"
                      using hj by (by100 linarith)
                    hence hd: "2*pi*(((1-t)*angle_n x + t*\<theta>p_n) - \<theta>q_n) = 2*pi*of_int j"
                      by (simp only: right_diff_distrib)
                    have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                    hence "2*pi \<noteq> 0" by (by100 linarith)
                    hence "((1-t)*angle_n x + t*\<theta>p_n) - \<theta>q_n = of_int j" using hd by (by100 simp)
                    moreover have "((1-t)*angle_n x + t*\<theta>p_n) - \<theta>q_n > 0
                        \<and> ((1-t)*angle_n x + t*\<theta>p_n) - \<theta>q_n < 1"
                      using hinterp_range by (by100 linarith)
                    ultimately have hj_bound: "of_int j > (0::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "j > 0" by (by100 simp)
                    hence "j \<ge> 1" by (by100 simp)
                    hence "of_int j \<ge> (1::real)" by (by100 simp)
                    thus False using hj_bound by (by100 linarith)
                  qed
                  \<comment> \<open>h_n is injective, and h_n(q'_n) = q(n-1), so the image \<noteq> q(n-1).\<close>
                  have hresult_Cn: "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) \<in> ?Cn"
                  proof -
                    have "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) \<in> top1_S1"
                      unfolding top1_R_to_S1_def top1_S1_def by (simp add: sin_squared_eq)
                    thus ?thesis using hbij_n unfolding bij_betw_def by (by100 blast)
                  qed
                  have hresult_ne_q: "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) \<noteq> q (n-1)"
                  proof
                    assume "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) = q (n-1)"
                    hence "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) = h_n q'_n"
                      unfolding q'_n_def using bij_betw_inv_into_right[OF hbij_n hq_in_n] by (by100 simp)
                    moreover have "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) \<in> top1_S1"
                      unfolding top1_R_to_S1_def top1_S1_def by (simp add: sin_squared_eq)
                    moreover have "q'_n \<in> top1_S1" using hq'_S1 .
                    ultimately have "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = q'_n"
                      using hbij_n unfolding bij_betw_def inj_on_def by (by100 blast)
                    thus False using hne_q' by (by100 blast)
                  qed
                  have "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) \<in> W (n-1)"
                    using hresult_Cn hresult_ne_q unfolding W_def by (by100 blast)
                  hence "H_U xt \<in> W (n-1)"
                    using \<open>H_U xt = h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))\<close>
                    by (by100 simp)
                  thus ?thesis unfolding U_def_def by (by100 blast)
                qed
              qed
              \<comment> \<open>Step 9: H_U is continuous on X' \<times> I_set (identity/projection).\<close>
              have hH_U_X': "top1_continuous_map_on (?X' \<times> I_set)
                  (subspace_topology (U_def \<times> I_set) ?TUI (?X' \<times> I_set))
                  U_def ?TU H_U"
              proof -
                \<comment> \<open>H_U = pi1 on X' \<times> I_set.\<close>
                have heq: "\<forall>xt\<in>?X' \<times> I_set. H_U xt = pi1 xt"
                proof (intro ballI)
                  fix xt assume hxt: "xt \<in> ?X' \<times> I_set"
                  obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> ?X'" and ht: "t \<in> I_set"
                    using hxt by (by100 blast)
                  show "H_U xt = pi1 xt"
                    unfolding hxt_eq H_U_def pi1_def using hx by (by100 simp)
                qed
                \<comment> \<open>Subspace topology on X' \<times> I = product of subspace topologies.\<close>
                let ?TX' = "subspace_topology X TX ?X'"
                have hTX'eq: "subspace_topology (U_def \<times> I_set) ?TUI (?X' \<times> I_set)
                    = product_topology_on ?TX' ?TI"
                proof -
                  have hT163: "product_topology_on (subspace_topology U_def ?TU ?X') (subspace_topology I_set ?TI I_set)
                      = subspace_topology (U_def \<times> I_set) ?TUI (?X' \<times> I_set)"
                    by (rule Theorem_16_3[OF hTU hTI])
                  have "subspace_topology (U_def \<times> I_set) ?TUI (?X' \<times> I_set)
                      = product_topology_on (subspace_topology U_def ?TU ?X') (subspace_topology I_set ?TI I_set)"
                    using hT163[symmetric] .
                  moreover have "subspace_topology U_def ?TU ?X' = ?TX'"
                    by (rule subspace_topology_trans[OF hX'_sub_U])
                  moreover have "subspace_topology I_set ?TI I_set = ?TI"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>?TI. U \<subseteq> I_set"
                    proof (intro ballI)
                      fix U assume "U \<in> ?TI"
                      thus "U \<subseteq> I_set"
                        unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                    qed
                  qed
                  ultimately show ?thesis by (simp only:)
                qed
                \<comment> \<open>pi1 is continuous: X' \<times> I_set \<rightarrow> X'.\<close>
                have hTX': "is_topology_on ?X' ?TX'"
                  by (rule subspace_topology_is_topology_on[OF hTX hX'_sub])
                have hpi1_cont: "top1_continuous_map_on (?X' \<times> I_set)
                    (product_topology_on ?TX' ?TI) ?X' ?TX' pi1"
                  by (rule top1_continuous_pi1[OF hTX' hTI])
                \<comment> \<open>Enlarge codomain from X' to U_def.\<close>
                have hpi1_U: "top1_continuous_map_on (?X' \<times> I_set)
                    (product_topology_on ?TX' ?TI) U_def ?TU pi1"
                  by (rule top1_continuous_map_on_codomain_enlarge[OF hpi1_cont hX'_sub_U hU_sub])
                \<comment> \<open>Transfer from pi1 to H_U via cong.\<close>
                have "top1_continuous_map_on (?X' \<times> I_set)
                    (product_topology_on ?TX' ?TI) U_def ?TU H_U"
                  using iffD2[OF top1_continuous_map_on_cong[OF heq] hpi1_U] .
                thus ?thesis using hTX'eq by (by100 simp)
              qed
              \<comment> \<open>Step 10: H_U is continuous on W(n-1) \<times> I_set (angle interpolation composition).\<close>
              have hH_U_Wn: "top1_continuous_map_on (W (n-1) \<times> I_set)
                  (subspace_topology (U_def \<times> I_set) ?TUI (W (n-1) \<times> I_set))
                  U_def ?TU H_U"
              proof -
                let ?TWn = "subspace_topology X TX (W (n-1))"
                \<comment> \<open>Subspace topology on W(n-1) \<times> I_set = product of subspace topologies.\<close>
                have hWn_sub_U: "W (n-1) \<subseteq> U_def" unfolding U_def_def by (by100 blast)
                have hWn_sub_X: "W (n-1) \<subseteq> X" using hW_sub_X hn1_in by (by100 blast)
                have hTWn: "is_topology_on (W (n-1)) ?TWn"
                  by (rule subspace_topology_is_topology_on[OF hTX hWn_sub_X])
                have hTWnI_eq: "subspace_topology (U_def \<times> I_set) ?TUI (W (n-1) \<times> I_set)
                    = product_topology_on ?TWn ?TI"
                proof -
                  have hT163: "product_topology_on (subspace_topology U_def ?TU (W (n-1))) (subspace_topology I_set ?TI I_set)
                      = subspace_topology (U_def \<times> I_set) ?TUI (W (n-1) \<times> I_set)"
                    by (rule Theorem_16_3[OF hTU hTI])
                  have "subspace_topology (U_def \<times> I_set) ?TUI (W (n-1) \<times> I_set)
                      = product_topology_on (subspace_topology U_def ?TU (W (n-1))) (subspace_topology I_set ?TI I_set)"
                    using hT163[symmetric] .
                  moreover have "subspace_topology U_def ?TU (W (n-1)) = ?TWn"
                    by (rule subspace_topology_trans[OF hWn_sub_U])
                  moreover have "subspace_topology I_set ?TI I_set = ?TI"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>?TI. U \<subseteq> I_set"
                    proof (intro ballI)
                      fix U assume "U \<in> ?TI"
                      thus "U \<subseteq> I_set"
                        unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                    qed
                  qed
                  ultimately show ?thesis by (simp only:)
                qed
                \<comment> \<open>On W(n-1), H_U (x,t) = h_n (R_to_S1 ((1-t) * angle_n x + t * \<theta>p_n)).
                   We prove this is continuous as a composition of continuous maps.\<close>
                \<comment> \<open>Step A: angle_n is continuous W(n-1) \<rightarrow> R.
                   angle_n = (R_to_S1|_{(\<theta>q,\<theta>q+1)})^{-1} \<circ> hinv_n.
                   hinv_n is continuous (homeomorphism inverse).
                   R_to_S1 restricted to (\<theta>q,\<theta>q+1) is a homeomorphism onto S1-{q'_n}
                   (covering map + injectivity on length-1 interval).
                   So its inverse is continuous.\<close>
                \<comment> \<open>Step A+B combined: angle_n is continuous, and the interpolation map is continuous.
                   angle_n = (R_to_S1|_{(\<theta>q,\<theta>q+1)})^{-1} \<circ> hinv_n, where:
                   - hinv_n is continuous (homeomorphism inverse on C(n-1) to S1)
                   - R_to_S1 restricted to (\<theta>q_n, \<theta>q_n+1) is a homeomorphism onto
                     S1 - {q'_n} (covering map + injectivity on length-1 interval)
                   Then (x,t) \<mapsto> (1-t)*angle_n(x) + t*\<theta>p_n is continuous as
                   arithmetic combination of continuous maps on a product space.\<close>
                have hangle_n_cont: "top1_continuous_map_on (W (n-1)) ?TWn
                    (UNIV :: real set) top1_open_sets angle_n"
                proof (rule continuous_map_onI)
                  show "\<forall>x\<in>W (n-1). angle_n x \<in> (UNIV :: real set)" by (by100 blast)
                next
                  show "\<forall>V\<in>top1_open_sets. {x \<in> W (n-1). angle_n x \<in> V} \<in> ?TWn"
                  proof (intro ballI)
                    fix V assume hV: "V \<in> (top1_open_sets :: real set set)"
                    \<comment> \<open>We show the preimage is open via top1_open_of_local_subsets.\<close>
                    let ?pre = "{x \<in> W (n-1). angle_n x \<in> V}"
                    have hpre_sub: "?pre \<subseteq> W (n-1)" by (by100 blast)
                    show "?pre \<in> ?TWn"
                    proof (rule top1_open_of_local_subsets[OF hTWn hpre_sub])
                      show "\<forall>x\<in>?pre. \<exists>U\<in>?TWn. x \<in> U \<and> U \<subseteq> ?pre"
                      proof (intro ballI)
                        fix x assume hx_pre: "x \<in> ?pre"
                        hence hxW: "x \<in> W (n-1)" and hax_V: "angle_n x \<in> V" by (by100 blast)+
                        have hxC: "x \<in> ?Cn" using hxW unfolding W_def by (by100 blast)
                        have hx_ne_q: "x \<noteq> q (n-1)" using hxW unfolding W_def by (by100 blast)
                        \<comment> \<open>hinv_n x is in S1 and is not q'_n.\<close>
                        have hhinv_x_S1: "?hinv_n x \<in> top1_S1"
                          using hbij_inv_n hxC unfolding bij_betw_def by (by100 blast)
                        have hhinv_x_ne_q': "?hinv_n x \<noteq> q'_n"
                        proof
                          assume "?hinv_n x = q'_n"
                          hence "h_n (?hinv_n x) = h_n q'_n" by (by100 simp)
                          hence "x = q (n-1)"
                            using bij_betw_inv_into_right[OF hbij_n hxC]
                              bij_betw_inv_into_right[OF hbij_n hq_in_n]
                            unfolding q'_n_def by (by100 simp)
                          thus False using hx_ne_q by (by100 blast)
                        qed
                        \<comment> \<open>Get angle_n spec for x.\<close>
                        have hspec_x: "\<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1 \<and>
                            top1_R_to_S1 (angle_n x) = ?hinv_n x"
                          using hangle_n_spec[OF hxW] by (by100 blast)
                        \<comment> \<open>From covering map, get evenly covered neighborhood of hinv_n x.\<close>
                        obtain Ux where hhinv_x_Ux: "?hinv_n x \<in> Ux"
                            and hUx_ec: "top1_evenly_covered_on UNIV top1_open_sets
                                top1_S1 top1_S1_topology top1_R_to_S1 Ux"
                          using top1_covering_map_on_evenly_covered[OF Theorem_53_1 hhinv_x_S1]
                          by (by100 blast)
                        \<comment> \<open>Get the partition of sheets.\<close>
                        have hUx_ec_unf: "openin_on top1_S1 top1_S1_topology Ux \<and>
                            (\<exists>\<V>x.
                            (\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs) \<and>
                            (\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}) \<and>
                            {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x \<and>
                            (\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                (subspace_topology UNIV top1_open_sets Vs)
                                Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1))"
                          using hUx_ec unfolding top1_evenly_covered_on_def by (by100 fast)
                        obtain \<V>x where hVx_conj:
                            "(\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs) \<and>
                            (\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}) \<and>
                            {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x \<and>
                            (\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                (subspace_topology UNIV top1_open_sets Vs)
                                Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1)"
                          using conjunct2[OF hUx_ec_unf] by blast
                        have hVx_open: "\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs"
                          and hVx_disj: "\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}"
                          and hVx_union: "{t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x"
                          and hVx_homeo: "\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                (subspace_topology UNIV top1_open_sets Vs)
                                Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1"
                          using hVx_conj by (by100 blast)+
                        \<comment> \<open>angle_n x is in the preimage of Ux, so it's in some sheet.\<close>
                        have hax_preim: "angle_n x \<in> {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux}"
                          using hspec_x hhinv_x_Ux by (by100 simp)
                        hence "angle_n x \<in> \<Union>\<V>x" using hVx_union by (by100 simp)
                        then obtain Vsheet where hVs_in: "Vsheet \<in> \<V>x"
                            and hax_Vs: "angle_n x \<in> Vsheet"
                          by (by100 blast)
                        \<comment> \<open>R_to_S1 : Vsheet \<rightarrow> Ux is a homeomorphism.\<close>
                        have hVs_homeo: "top1_homeomorphism_on Vsheet
                            (subspace_topology UNIV top1_open_sets Vsheet)
                            Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1"
                          using hVx_homeo hVs_in by (by100 blast)
                        \<comment> \<open>Vsheet is open in R.\<close>
                        have hVs_open: "Vsheet \<in> top1_open_sets"
                          using hVx_open hVs_in unfolding openin_on_def by (by100 blast)
                        \<comment> \<open>inv_into Vsheet R_to_S1 is continuous Ux \<rightarrow> Vsheet.\<close>
                        have hVs_inv_cont: "top1_continuous_map_on Ux
                            (subspace_topology top1_S1 top1_S1_topology Ux)
                            Vsheet (subspace_topology UNIV top1_open_sets Vsheet)
                            (inv_into Vsheet top1_R_to_S1)"
                          using hVs_homeo unfolding top1_homeomorphism_on_def
                          by (by100 blast)
                        \<comment> \<open>The key open set in S1: points in Ux whose lift in Vsheet is in V \<inter> (\<theta>q, \<theta>q+1).\<close>
                        define I_interval where "I_interval = {\<theta>::real. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1}"
                        have hI_open: "I_interval \<in> top1_open_sets"
                        proof -
                          have "I_interval = {\<theta>q_n <..< \<theta>q_n + 1}"
                            unfolding I_interval_def by (by100 auto)
                          thus ?thesis unfolding top1_open_sets_def
                            using open_greaterThanLessThan[of \<theta>q_n "\<theta>q_n + 1"] by (by100 simp)
                        qed
                        \<comment> \<open>V \<inter> Vsheet \<inter> I_interval is open in R.\<close>
                        have hVVI_open: "V \<inter> Vsheet \<inter> I_interval \<in> top1_open_sets"
                        proof -
                          have h1: "V \<inter> Vsheet \<in> top1_open_sets"
                            using topology_inter2[OF top1_open_sets_is_topology_on_UNIV hV hVs_open] .
                          show ?thesis
                            using topology_inter2[OF top1_open_sets_is_topology_on_UNIV h1 hI_open] .
                        qed
                        have hax_in_VVI: "angle_n x \<in> V \<inter> Vsheet \<inter> I_interval"
                          using hax_V hax_Vs hspec_x unfolding I_interval_def by (by100 blast)
                        \<comment> \<open>R_to_S1 maps V \<inter> Vsheet \<inter> I_interval homeomorphically to an open subset of Ux.\<close>
                        \<comment> \<open>The preimage under inv_into Vsheet R_to_S1 of V \<inter> Vsheet \<inter> I_interval
                           is open in (Ux, subspace topology from S1).\<close>
                        have hVVI_sub_Vs: "V \<inter> Vsheet \<inter> I_interval \<subseteq> Vsheet" by (by100 blast)
                        have hVVI_in_sub: "V \<inter> Vsheet \<inter> I_interval \<in>
                            subspace_topology UNIV top1_open_sets Vsheet"
                          unfolding subspace_topology_def using hVVI_open by (by100 blast)
                        \<comment> \<open>The preimage of V \<inter> Vsheet \<inter> I_interval under inv_into Vsheet R_to_S1
                           is open in Ux (by continuity of the inverse).\<close>
                        define Sx where "Sx = {s \<in> Ux. inv_into Vsheet top1_R_to_S1 s \<in>
                            V \<inter> Vsheet \<inter> I_interval}"
                        have hSx_open: "Sx \<in> subspace_topology top1_S1 top1_S1_topology Ux"
                          unfolding Sx_def
                          using continuous_map_preimage_open[OF hVs_inv_cont hVVI_in_sub] .
                        have hhinv_x_Sx: "?hinv_n x \<in> Sx"
                        proof -
                          have "inv_into Vsheet top1_R_to_S1 (?hinv_n x) = angle_n x"
                          proof -
                            have hbij_Vs: "bij_betw top1_R_to_S1 Vsheet Ux"
                              using hVs_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                            have "top1_R_to_S1 (angle_n x) = ?hinv_n x" using hspec_x by (by100 blast)
                            moreover have "angle_n x \<in> Vsheet" using hax_Vs .
                            ultimately show ?thesis
                              using inv_into_f_eq[OF bij_betw_imp_inj_on[OF hbij_Vs] hax_Vs]
                              by (by100 simp)
                          qed
                          thus ?thesis unfolding Sx_def
                            using hhinv_x_Ux hax_in_VVI by (by100 simp)
                        qed
                        \<comment> \<open>Sx is open in S1 (contained in Ux which is open in S1).\<close>
                        obtain Ux_outer where hUx_outer: "Ux_outer \<in> top1_S1_topology"
                            and hSx_eq: "Sx = Ux \<inter> Ux_outer"
                          using hSx_open unfolding subspace_topology_def by (by100 blast)
                        \<comment> \<open>Ux is open in S1.\<close>
                        have hUx_open_S1: "openin_on top1_S1 top1_S1_topology Ux"
                          using top1_evenly_covered_on_openin_on[OF hUx_ec] .
                        hence hUx_in_S1T: "Ux \<in> top1_S1_topology"
                          unfolding openin_on_def by (by100 blast)
                        \<comment> \<open>Sx \<in> S1 topology.\<close>
                        have hTS1: "is_topology_on top1_S1 top1_S1_topology"
                          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def
                          by (by100 blast)
                        have hSx_in_S1T: "Sx \<in> top1_S1_topology"
                          using topology_inter2[OF hTS1 hUx_in_S1T hUx_outer] hSx_eq by (by100 simp)
                        \<comment> \<open>hinv_n is continuous from C(n-1) to S1.\<close>
                        have hcont_hinv_Cn: "top1_continuous_map_on ?Cn
                            (subspace_topology X TX ?Cn) top1_S1 top1_S1_topology ?hinv_n"
                          using hhinv_n unfolding top1_homeomorphism_on_def by (by100 blast)
                        \<comment> \<open>Restrict to W(n-1).\<close>
                        have hWn_sub_Cn: "W (n-1) \<subseteq> ?Cn" unfolding W_def by (by100 blast)
                        have hcont_hinv_Wn: "top1_continuous_map_on (W (n-1)) ?TWn
                            top1_S1 top1_S1_topology ?hinv_n"
                        proof -
                          have "?TWn = subspace_topology ?Cn (subspace_topology X TX ?Cn) (W (n-1))"
                            by (rule subspace_topology_trans[OF hWn_sub_Cn, symmetric])
                          thus ?thesis using top1_continuous_map_on_restrict_domain_simple[OF
                              hcont_hinv_Cn hWn_sub_Cn] by (by100 simp)
                        qed
                        \<comment> \<open>Preimage of Sx under hinv_n in W(n-1) is open.\<close>
                        have hSx_preim: "{x' \<in> W (n-1). ?hinv_n x' \<in> Sx} \<in> ?TWn"
                          using continuous_map_preimage_open[OF hcont_hinv_Wn hSx_in_S1T] .
                        \<comment> \<open>This preimage is a subset of ?pre.\<close>
                        have hSx_preim_sub: "{x' \<in> W (n-1). ?hinv_n x' \<in> Sx} \<subseteq> ?pre"
                        proof (intro subsetI)
                          fix y assume hy: "y \<in> {x' \<in> W (n-1). ?hinv_n x' \<in> Sx}"
                          hence hyW: "y \<in> W (n-1)" and hhinv_y_Sx: "?hinv_n y \<in> Sx"
                            by (by100 blast)+
                          \<comment> \<open>inv_into Vsheet R_to_S1 (hinv_n y) is in V \<inter> Vsheet \<inter> I_interval.\<close>
                          have hinv_y_VVI: "inv_into Vsheet top1_R_to_S1 (?hinv_n y) \<in>
                              V \<inter> Vsheet \<inter> I_interval"
                            using hhinv_y_Sx unfolding Sx_def by (by100 blast)
                          define \<theta>y where "\<theta>y = inv_into Vsheet top1_R_to_S1 (?hinv_n y)"
                          have h\<theta>y_V: "\<theta>y \<in> V" and h\<theta>y_Vs: "\<theta>y \<in> Vsheet"
                              and h\<theta>y_I: "\<theta>q_n < \<theta>y \<and> \<theta>y < \<theta>q_n + 1"
                            using hinv_y_VVI unfolding \<theta>y_def I_interval_def by (by100 blast)+
                          \<comment> \<open>R_to_S1 \<theta>y = hinv_n y.\<close>
                          have hbij_Vs: "bij_betw top1_R_to_S1 Vsheet Ux"
                            using hVs_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                          have hhinv_y_Ux: "?hinv_n y \<in> Ux"
                            using hhinv_y_Sx unfolding Sx_def by (by100 blast)
                          have hR_\<theta>y: "top1_R_to_S1 \<theta>y = ?hinv_n y"
                            unfolding \<theta>y_def
                            using f_inv_into_f[of "?hinv_n y" top1_R_to_S1 Vsheet]
                              hhinv_y_Ux hbij_Vs unfolding bij_betw_def by (by100 blast)
                          \<comment> \<open>Since \<theta>y \<in> I_interval and R_to_S1 \<theta>y = hinv_n y, by uniqueness
                             angle_n y = \<theta>y.\<close>
                          have "\<theta>q_n < \<theta>y \<and> \<theta>y < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta>y = ?hinv_n y"
                            using h\<theta>y_I hR_\<theta>y by (by100 blast)
                          hence "angle_n y = \<theta>y"
                          proof -
                            have hspec_y: "\<theta>q_n < angle_n y \<and> angle_n y < \<theta>q_n + 1 \<and>
                                top1_R_to_S1 (angle_n y) = ?hinv_n y"
                              using hangle_n_spec[OF hyW] by (by100 blast)
                            \<comment> \<open>Both \<theta>y and angle_n y are in (\<theta>q, \<theta>q+1) and map to hinv_n y.
                               By injectivity of R_to_S1 on length < 1 intervals, they are equal.\<close>
                            have "top1_R_to_S1 \<theta>y = top1_R_to_S1 (angle_n y)"
                              using hR_\<theta>y hspec_y by (by100 simp)
                            hence "sin (2 * pi * \<theta>y) = sin (2 * pi * angle_n y)
                                \<and> cos (2 * pi * \<theta>y) = cos (2 * pi * angle_n y)"
                              unfolding top1_R_to_S1_def by (by100 auto)
                            then obtain k :: int where
                                hk: "2*pi*\<theta>y = 2*pi*(angle_n y) + 2*pi*of_int k"
                              using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                            hence "2*pi*(\<theta>y - angle_n y) = 2*pi*of_int k"
                              by (simp add: algebra_simps)
                            hence "\<theta>y - angle_n y = of_int k" using pi_gt_zero
                              by (by100 simp)
                            moreover have "\<bar>\<theta>y - angle_n y\<bar> < 1"
                              using h\<theta>y_I hspec_y by (by100 linarith)
                            hence "k = 0" using \<open>\<theta>y - angle_n y = of_int k\<close> by (by100 linarith)
                            ultimately show "angle_n y = \<theta>y" by (by100 linarith)
                          qed
                          hence "angle_n y \<in> V" using h\<theta>y_V by (by100 simp)
                          thus "y \<in> ?pre" using hyW by (by100 blast)
                        qed
                        \<comment> \<open>x is in the preimage.\<close>
                        have hx_in_preim: "x \<in> {x' \<in> W (n-1). ?hinv_n x' \<in> Sx}"
                          using hxW hhinv_x_Sx by (by100 blast)
                        show "\<exists>U\<in>?TWn. x \<in> U \<and> U \<subseteq> ?pre"
                          apply (rule bexI[of _ "{x' \<in> W (n-1). ?hinv_n x' \<in> Sx}"])
                          using hx_in_preim hSx_preim_sub hSx_preim by (by100 blast)+
                      qed
                    qed
                  qed
                qed
                have hinterp_cont: "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    (UNIV :: real set) top1_open_sets
                    (\<lambda>(x,t). (1 - t) * angle_n x + t * \<theta>p_n)"
                proof -
                  \<comment> \<open>Bridge: order_topology_on_UNIV = top1_open_sets for reals.\<close>
                  have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
                  proof (rule set_eqI)
                    fix U :: "real set"
                    show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
                      using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def
                      by (by100 simp)
                  qed
                  let ?TR = "order_topology_on_UNIV :: real set set"
                  have hTR: "is_topology_on (UNIV::real set) ?TR"
                    by (rule order_topology_on_UNIV_is_topology_on)
                  have hTWnI: "is_topology_on (W (n-1) \<times> I_set) (product_topology_on ?TWn ?TI)"
                    by (rule product_topology_on_is_topology_on[OF hTWn hTI])
                  \<comment> \<open>I_top = subspace_topology UNIV top1_open_sets I_set.\<close>
                  have hItop_eq: "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
                    unfolding top1_unit_interval_topology_def top1_unit_interval_def
                    by (by100 simp)
                  \<comment> \<open>angle_n \<circ> pi1 continuous W(n-1)\<times>I \<rightarrow> UNIV (order_topology_on_UNIV).\<close>
                  have hangle_pi1: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR (angle_n \<circ> pi1)"
                  proof -
                    have hpi1_cont: "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) (W (n-1)) ?TWn pi1"
                      by (rule top1_continuous_pi1[OF hTWn hTI])
                    have "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) (UNIV::real set) top1_open_sets
                        (angle_n \<circ> pi1)"
                      by (rule top1_continuous_map_on_comp[OF hpi1_cont hangle_n_cont])
                    thus ?thesis unfolding hTR_eq .
                  qed
                  \<comment> \<open>pi2 continuous W(n-1)\<times>I \<rightarrow> I_set, then enlarge to UNIV.\<close>
                  have hpi2_R: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR pi2"
                  proof -
                    have hpi2_I: "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) I_set I_top pi2"
                      by (rule top1_continuous_pi2[OF hTWn hTI])
                    have h1: "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) I_set
                        (subspace_topology UNIV top1_open_sets I_set) pi2"
                      using hpi2_I unfolding hItop_eq .
                    have h2: "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) (UNIV::real set)
                        (subspace_topology UNIV top1_open_sets UNIV) pi2"
                      using top1_continuous_map_on_codomain_enlarge[OF h1]
                      by (by100 simp)
                    have h3: "top1_continuous_map_on (W (n-1) \<times> I_set)
                        (product_topology_on ?TWn ?TI) (UNIV::real set) top1_open_sets pi2"
                      using h2 unfolding subspace_topology_UNIV_self .
                    thus ?thesis unfolding hTR_eq .
                  qed
                  \<comment> \<open>Constant 1 continuous.\<close>
                  have hconst1: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR (\<lambda>_. 1::real)"
                    using top1_continuous_map_on_const[OF hTWnI hTR UNIV_I]
                    by (by100 simp)
                  \<comment> \<open>Constant \<theta>p_n continuous.\<close>
                  have hconst_\<theta>pn: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR (\<lambda>_. \<theta>p_n)"
                    using top1_continuous_map_on_const[OF hTWnI hTR UNIV_I]
                    by (by100 simp)
                  \<comment> \<open>(1 - pi2) continuous.\<close>
                  have h1_minus_t: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR
                      (\<lambda>p. 1 - pi2 p)"
                    by (rule top1_continuous_diff_real[OF hTWnI hconst1 hpi2_R])
                  \<comment> \<open>(1 - pi2) * (angle_n \<circ> pi1) continuous.\<close>
                  have hterm1: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR
                      (\<lambda>p. (1 - pi2 p) * (angle_n \<circ> pi1) p)"
                    by (rule top1_continuous_mul_real[OF hTWnI h1_minus_t hangle_pi1])
                  \<comment> \<open>pi2 * \<theta>p_n continuous.\<close>
                  have hterm2: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR
                      (\<lambda>p. pi2 p * \<theta>p_n)"
                    by (rule top1_continuous_mul_real[OF hTWnI hpi2_R hconst_\<theta>pn])
                  \<comment> \<open>Sum: (1-t)*angle_n(x) + t*\<theta>p_n continuous (in order_topology_on_UNIV).\<close>
                  have hsum_OT: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) ?TR
                      (\<lambda>p. (1 - pi2 p) * (angle_n \<circ> pi1) p + pi2 p * \<theta>p_n)"
                    by (rule top1_continuous_add_real[OF hTWnI hterm1 hterm2])
                  \<comment> \<open>Switch to top1_open_sets via bridge.\<close>
                  have hsum_OS: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) (UNIV::real set) top1_open_sets
                      (\<lambda>p. (1 - pi2 p) * (angle_n \<circ> pi1) p + pi2 p * \<theta>p_n)"
                    using hsum_OT unfolding hTR_eq .
                  \<comment> \<open>Rewrite the function to match the goal.\<close>
                  have hfun_eq: "\<forall>p \<in> W (n-1) \<times> I_set.
                      (1 - pi2 p) * (angle_n \<circ> pi1) p + pi2 p * \<theta>p_n =
                      (case p of (x,t) \<Rightarrow> (1 - t) * angle_n x + t * \<theta>p_n)"
                  proof (intro ballI)
                    fix p assume "p \<in> W (n-1) \<times> I_set"
                    obtain x t where hp: "p = (x, t)" by (cases p)
                    show "(1 - pi2 p) * (angle_n \<circ> pi1) p + pi2 p * \<theta>p_n =
                        (case p of (x,t) \<Rightarrow> (1 - t) * angle_n x + t * \<theta>p_n)"
                      unfolding hp pi1_def pi2_def by (by100 simp)
                  qed
                  show ?thesis
                    using iffD1[OF top1_continuous_map_on_cong[OF hfun_eq]] hsum_OS
                    by (by100 blast)
                qed
                \<comment> \<open>Step C: Compose with R_to_S1: W(n-1) \<times> I \<rightarrow> S1.\<close>
                have hR_S1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                    top1_S1 top1_S1_topology top1_R_to_S1"
                  by (rule top1_covering_map_on_continuous[OF Theorem_53_1])
                have hRS1_comp: "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    top1_S1 top1_S1_topology
                    (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))"
                proof -
                  have hcomp: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) top1_S1 top1_S1_topology
                      (top1_R_to_S1 \<circ> (\<lambda>(x,t). (1 - t) * angle_n x + t * \<theta>p_n))"
                    by (rule top1_continuous_map_on_comp[OF hinterp_cont hR_S1])
                  have heq: "\<forall>xt\<in>W (n-1) \<times> I_set.
                      (top1_R_to_S1 \<circ> (\<lambda>(x,t). (1 - t) * angle_n x + t * \<theta>p_n)) xt =
                      (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) xt"
                    by (by100 auto)
                  show ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq]] hcomp by (by100 blast)
                qed
                \<comment> \<open>Step D: Compose with h_n: W(n-1) \<times> I \<rightarrow> C(n-1).\<close>
                have hcont_hn: "top1_continuous_map_on top1_S1 top1_S1_topology
                    ?Cn (subspace_topology X TX ?Cn) h_n"
                  using hh_n unfolding top1_homeomorphism_on_def by (by100 blast)
                have hfull_comp: "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    ?Cn (subspace_topology X TX ?Cn)
                    (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
                proof -
                  have hcomp: "top1_continuous_map_on (W (n-1) \<times> I_set)
                      (product_topology_on ?TWn ?TI) ?Cn (subspace_topology X TX ?Cn)
                      (h_n \<circ> (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
                    by (rule top1_continuous_map_on_comp[OF hRS1_comp hcont_hn])
                  have heq: "\<forall>xt\<in>W (n-1) \<times> I_set.
                      (h_n \<circ> (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt =
                      (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt"
                    by (by100 auto)
                  show ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq]] hcomp by (by100 blast)
                qed
                \<comment> \<open>Step E: On W(n-1), H_U agrees with this composition.
                   Note: p \<in> W(n-1) \<inter> X', but both branches agree at p since
                   angle_n(p) = \<theta>p_n, giving h_n(R_to_S1(\<theta>p_n)) = h_n(p'_n) = p.\<close>
                have hH_U_eq_corrected: "\<forall>xt\<in>W (n-1) \<times> I_set. H_U xt =
                    (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt"
                proof (intro ballI)
                  fix xt assume hxt: "xt \<in> W (n-1) \<times> I_set"
                  obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> W (n-1)" and ht: "t \<in> I_set"
                    using hxt by (by100 blast)
                  show "H_U xt = (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt"
                  proof (cases "x \<in> ?X'")
                    case False
                    thus ?thesis unfolding hxt_eq H_U_def by (by100 simp)
                  next
                    case True
                    \<comment> \<open>x \<in> X' \<inter> W(n-1), so x = p.\<close>
                    have hx_Cn: "x \<in> ?Cn" using hx unfolding W_def by (by100 blast)
                    from True obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hx\<beta>: "x \<in> C \<beta>" by (by100 blast)
                    have h\<beta>n: "\<beta> \<in> {..<n}" using h\<beta> hn2 by (by100 simp)
                    have "\<beta> \<noteq> n - 1" using h\<beta> by (by100 simp)
                    hence "C \<beta> \<inter> ?Cn = {p}" using hC_inter h\<beta>n hn1_in by (by100 blast)
                    hence hxp: "x = p" using hx\<beta> hx_Cn by (by100 blast)
                    \<comment> \<open>LHS: H_U(p,t) = p.\<close>
                    have "H_U xt = x" unfolding hxt_eq H_U_def using True by (by100 simp)
                    hence lhs: "H_U xt = p" using hxp by (by100 simp)
                    \<comment> \<open>RHS: angle_n(p) = \<theta>p_n, so (1-t)*\<theta>p_n + t*\<theta>p_n = \<theta>p_n,
                         R_to_S1(\<theta>p_n) = p'_n, h_n(p'_n) = p.\<close>
                    have hangle_p: "angle_n p = \<theta>p_n"
                    proof -
                      have hspec: "\<theta>q_n < \<theta>p_n \<and> \<theta>p_n < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta>p_n = ?hinv_n p"
                      proof (intro conjI)
                        show "\<theta>q_n < \<theta>p_n" using h\<theta>p_range by (by100 blast)
                        show "\<theta>p_n < \<theta>q_n + 1" using h\<theta>p_range by (by100 blast)
                        show "top1_R_to_S1 \<theta>p_n = ?hinv_n p"
                          using h\<theta>p_n unfolding p'_n_def by (by100 simp)
                      qed
                      have hex1: "\<exists>!\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n p"
                      proof (rule ex_ex1I)
                        show "\<exists>\<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n p"
                          using hspec by (by100 blast)
                      next
                        fix a b
                        assume ha: "\<theta>q_n < a \<and> a < \<theta>q_n + 1 \<and> top1_R_to_S1 a = ?hinv_n p"
                        assume hb: "\<theta>q_n < b \<and> b < \<theta>q_n + 1 \<and> top1_R_to_S1 b = ?hinv_n p"
                        hence "top1_R_to_S1 a = top1_R_to_S1 b" using ha by (by100 simp)
                        hence "cos (2*pi*a) = cos (2*pi*b) \<and> sin (2*pi*a) = sin (2*pi*b)"
                          unfolding top1_R_to_S1_def by (by100 simp)
                        hence "sin (2*pi*a) = sin (2*pi*b) \<and> cos (2*pi*a) = cos (2*pi*b)"
                          by (by100 blast)
                        then obtain j :: int where hj: "2*pi*a = 2*pi*b + 2*pi*of_int j"
                          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                        have "2*pi*a - 2*pi*b = 2*pi*of_int j" using hj by (by100 linarith)
                        hence hd: "2*pi*(a - b) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                        have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                        hence "2*pi \<noteq> 0" by (by100 linarith)
                        hence "a - b = of_int j" using hd by (by100 simp)
                        moreover have "a - b > -1 \<and> a - b < 1" using ha hb by (by100 linarith)
                        ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                        hence "j = 0" by (by100 linarith)
                        thus "a = b" using \<open>a - b = of_int j\<close> by (by100 simp)
                      qed
                      have hthe: "(THE \<theta>. \<theta>q_n < \<theta> \<and> \<theta> < \<theta>q_n + 1 \<and> top1_R_to_S1 \<theta> = ?hinv_n p) = \<theta>p_n"
                        by (rule the1_equality[OF hex1 hspec])
                      show ?thesis unfolding angle_n_def using hthe by (by100 simp)
                    qed
                    have rhs: "(\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt = p"
                    proof -
                      have "(1 - t) * angle_n p + t * \<theta>p_n = (1 - t) * \<theta>p_n + t * \<theta>p_n"
                        using hangle_p by (by100 simp)
                      also have "\<dots> = \<theta>p_n" by (simp add: algebra_simps)
                      finally have hinterp_p: "(1 - t) * angle_n p + t * \<theta>p_n = \<theta>p_n" .
                      show ?thesis unfolding hxt_eq using hxp hinterp_p h\<theta>p_n hh_n_p'_eq by (by100 simp)
                    qed
                    show ?thesis using lhs rhs by (by100 simp)
                  qed
                qed
                \<comment> \<open>Step F: Transfer continuity: C(n-1) \<rightarrow> W(n-1) \<rightarrow> U_def.\<close>
                have hWn_sub_Cn: "W (n-1) \<subseteq> ?Cn" unfolding W_def by (by100 blast)
                \<comment> \<open>The image lies in W(n-1).\<close>
                have himg_Wn: "(\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) ` (W (n-1) \<times> I_set) \<subseteq> W (n-1)"
                proof (intro image_subsetI)
                  fix xt assume hxt: "xt \<in> W (n-1) \<times> I_set"
                  obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> W (n-1)" and ht: "t \<in> I_set"
                    using hxt by (by100 blast)
                  have hangle: "\<theta>q_n < angle_n x \<and> angle_n x < \<theta>q_n + 1"
                    using hangle_n_spec[OF hx] by (by100 blast)
                  have ht_range: "0 \<le> t \<and> t \<le> 1"
                    using ht unfolding top1_unit_interval_def by (by100 simp)
                  \<comment> \<open>Interpolated angle in (\<theta>q, \<theta>q+1).\<close>
                  have hinterp_range: "\<theta>q_n < (1 - t) * angle_n x + t * \<theta>p_n \<and>
                      (1 - t) * angle_n x + t * \<theta>p_n < \<theta>q_n + 1"
                  proof (intro conjI)
                    show "\<theta>q_n < (1 - t) * angle_n x + t * \<theta>p_n"
                    proof (cases "t = 0")
                      case True thus ?thesis using hangle by (by100 simp)
                    next
                      case False hence "t > 0" using ht_range by (by100 linarith)
                      have "t * (\<theta>p_n - \<theta>q_n) > 0" using h\<theta>p_range \<open>t > 0\<close> by (by100 simp)
                      moreover have "(1 - t) * (angle_n x - \<theta>q_n) \<ge> 0" using hangle ht_range by (by100 simp)
                      ultimately have "(1-t)*angle_n x + t*\<theta>p_n > (1-t)*\<theta>q_n + t*\<theta>q_n" by (simp add: algebra_simps)
                      moreover have "(1-t)*\<theta>q_n + t*\<theta>q_n = \<theta>q_n" by (simp add: algebra_simps)
                      ultimately show ?thesis by (by100 linarith)
                    qed
                  next
                    show "(1 - t) * angle_n x + t * \<theta>p_n < \<theta>q_n + 1"
                    proof (cases "t = 0")
                      case True thus ?thesis using hangle by (by100 simp)
                    next
                      case False hence "t > 0" using ht_range by (by100 linarith)
                      have "t*(\<theta>p_n - (\<theta>q_n+1)) < 0" using h\<theta>p_range \<open>t > 0\<close> by (simp add: mult_pos_neg)
                      moreover have "(1-t)*(angle_n x - (\<theta>q_n+1)) \<le> 0" using hangle ht_range
                        by (intro mult_nonneg_nonpos) linarith+
                      ultimately have "(1-t)*angle_n x + t*\<theta>p_n < (1-t)*(\<theta>q_n+1) + t*(\<theta>q_n+1)" by (simp add: algebra_simps)
                      moreover have "(1-t)*(\<theta>q_n+1) + t*(\<theta>q_n+1) = \<theta>q_n + 1" by (simp add: algebra_simps)
                      ultimately show ?thesis by (by100 linarith)
                    qed
                  qed
                  \<comment> \<open>R_to_S1 of angle avoids q'_n, so h_n of it avoids q(n-1), hence is in W(n-1).\<close>
                  have hinterp_S1: "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) \<in> top1_S1"
                    unfolding top1_R_to_S1_def top1_S1_def by (simp add: sin_squared_eq)
                  have hne_q': "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) \<noteq> q'_n"
                  proof
                    assume heq: "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = q'_n"
                    hence "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = top1_R_to_S1 \<theta>q_n"
                      using h\<theta>q_n by (by100 simp)
                    hence "cos(2*pi*((1-t)*angle_n x+t*\<theta>p_n))=cos(2*pi*\<theta>q_n) \<and>
                           sin(2*pi*((1-t)*angle_n x+t*\<theta>p_n))=sin(2*pi*\<theta>q_n)"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin(2*pi*((1-t)*angle_n x+t*\<theta>p_n))=sin(2*pi*\<theta>q_n) \<and>
                           cos(2*pi*((1-t)*angle_n x+t*\<theta>p_n))=cos(2*pi*\<theta>q_n)"
                      by (by100 blast)
                    then obtain j::int where hj: "2*pi*((1-t)*angle_n x+t*\<theta>p_n) = 2*pi*\<theta>q_n + 2*pi*of_int j"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    have "2*pi*((1-t)*angle_n x+t*\<theta>p_n) - 2*pi*\<theta>q_n = 2*pi*of_int j" using hj by (by100 linarith)
                    hence hd: "2*pi*(((1-t)*angle_n x+t*\<theta>p_n) - \<theta>q_n) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                    have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                    hence "2*pi \<noteq> 0" by (by100 linarith)
                    hence "((1-t)*angle_n x+t*\<theta>p_n) - \<theta>q_n = of_int j" using hd by (by100 simp)
                    moreover have "((1-t)*angle_n x+t*\<theta>p_n) - \<theta>q_n > 0 \<and> ((1-t)*angle_n x+t*\<theta>p_n) - \<theta>q_n < 1"
                      using hinterp_range by (by100 linarith)
                    ultimately have "of_int j > (0::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "j > 0 \<and> j < 1" by (by100 linarith)
                    thus False by (by100 linarith)
                  qed
                  have hresult_Cn: "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) \<in> ?Cn"
                    using hbij_n hinterp_S1 unfolding bij_betw_def by (by100 blast)
                  have hresult_neq: "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) \<noteq> q (n-1)"
                  proof
                    assume "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) = q (n-1)"
                    hence "h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)) = h_n q'_n"
                      unfolding q'_n_def using bij_betw_inv_into_right[OF hbij_n hq_in_n] by (by100 simp)
                    moreover note hinterp_S1 moreover note hq'_S1
                    ultimately have "top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n) = q'_n"
                      using hbij_n unfolding bij_betw_def inj_on_def by (by100 blast)
                    thus False using hne_q' by (by100 blast)
                  qed
                  show "(\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n))) xt \<in> W (n-1)"
                    unfolding hxt_eq W_def using hresult_Cn hresult_neq by (by100 simp)
                qed
                \<comment> \<open>Shrink codomain from C(n-1) to W(n-1), then enlarge to U_def.\<close>
                have hfull_comp_Wn: "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    (W (n-1)) (subspace_topology ?Cn (subspace_topology X TX ?Cn) (W (n-1)))
                    (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
                  by (rule top1_continuous_map_on_codomain_shrink[OF hfull_comp himg_Wn hWn_sub_Cn])
                have hWn_subspace_eq: "subspace_topology ?Cn (subspace_topology X TX ?Cn) (W (n-1))
                    = subspace_topology X TX (W (n-1))"
                  by (rule subspace_topology_trans[OF hWn_sub_Cn])
                have hfull_comp_Wn': "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    (W (n-1)) ?TWn
                    (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
                  using hfull_comp_Wn hWn_subspace_eq by (by100 simp)
                have hfull_comp_U: "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI)
                    U_def ?TU
                    (\<lambda>(x,t). h_n (top1_R_to_S1 ((1 - t) * angle_n x + t * \<theta>p_n)))"
                  by (rule top1_continuous_map_on_codomain_enlarge[OF hfull_comp_Wn' hWn_sub_U hU_sub])
                have "top1_continuous_map_on (W (n-1) \<times> I_set)
                    (product_topology_on ?TWn ?TI) U_def ?TU H_U"
                  using iffD2[OF top1_continuous_map_on_cong[OF hH_U_eq_corrected] hfull_comp_U] .
                thus ?thesis using hTWnI_eq by (by100 simp)
              qed
              \<comment> \<open>Step 11: Apply pasting lemma.\<close>
              show ?thesis
                by (rule pasting_lemma_two_closed[OF hTUI hTU hX'I_closed hWnI_closed hcover hH_U_range hH_U_X' hH_U_Wn])
            qed
            show ?thesis unfolding top1_deformation_retract_of_on_def
              using hX'_sub_U hH_U_cont hH_U_0 hH_U_1 hH_U_A by (by100 blast)
          qed
          have hTopU: "is_topology_on U_def (subspace_topology X TX U_def)"
            by (rule subspace_topology_is_topology_on[OF hTX]) (rule hU_sub)
          from Theorem_58_3[OF hdef_U hTopU hp_X']
          have "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier ?X' (subspace_topology U_def (subspace_topology X TX U_def) ?X') p)
              (top1_fundamental_group_mul ?X' (subspace_topology U_def (subspace_topology X TX U_def) ?X') p)
              (top1_fundamental_group_carrier U_def (subspace_topology X TX U_def) p)
              (top1_fundamental_group_mul U_def (subspace_topology X TX U_def) p)" .
          moreover have "subspace_topology U_def (subspace_topology X TX U_def) ?X' = ?TX'"
          proof -
            have "?X' \<subseteq> U_def" unfolding U_def_def by (by100 blast)
            thus ?thesis by (rule subspace_topology_trans)
          qed
          ultimately have h_iso_XU: "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier ?X' ?TX' p)
              (top1_fundamental_group_mul ?X' ?TX' p)
              (top1_fundamental_group_carrier U_def (subspace_topology X TX U_def) p)
              (top1_fundamental_group_mul U_def (subspace_topology X TX U_def) p)"
            by (simp only:)
          show ?thesis
            by (rule top1_groups_isomorphic_on_sym[OF h_iso_XU
                top1_fundamental_group_is_group[OF
                  subspace_topology_is_topology_on[OF hTX hX'_sub] hp_X']
                top1_fundamental_group_is_group[OF hTopU hp_U]])
        qed
        show "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier V_def (subspace_topology X TX V_def) p)
            (top1_fundamental_group_mul V_def (subspace_topology X TX V_def) p)
            (top1_fundamental_group_carrier ?Cn ?TCn p)
            (top1_fundamental_group_mul ?Cn ?TCn p)"
        proof -
          have hdef_V: "top1_deformation_retract_of_on V_def (subspace_topology X TX V_def) ?Cn"
          proof -
            \<comment> \<open>Step 1: C(n-1) \<subseteq> V_def.\<close>
            have hCn_sub_Vd: "?Cn \<subseteq> V_def" unfolding V_def_def by (by100 blast)
            \<comment> \<open>Step 2: Build homotopy H_V on V_def \<times> I.
               For x \<in> C(n-1): H_V(x,t) = x.
               For x \<in> W(\<alpha>) with \<alpha> < n-1: contract x to p along the arc in W(\<alpha>).
               These agree on W(\<alpha>) \<inter> C(n-1) \<subseteq> C(\<alpha>) \<inter> C(n-1) = {p}.\<close>
            \<comment> \<open>For each \<alpha> < n-1, get the angle parameterization of W(\<alpha>).\<close>
            \<comment> \<open>For each \<alpha> < n, we have: h: S1 \<rightarrow> C(\<alpha>), q(\<alpha>) \<in> C(\<alpha>), W(\<alpha>) = C(\<alpha>)\{q(\<alpha>)},
               p \<in> W(\<alpha>), and angle parameterization \<theta>: W(\<alpha>) \<rightarrow> (\<theta>_q, \<theta>_q+1) with p at \<theta>_p.\<close>
            \<comment> \<open>Define the retraction r_\<alpha>: W(\<alpha>) \<rightarrow> {p} as contraction via angles.\<close>
            \<comment> \<open>For each \<alpha> < n, choose homeomorphism h_\<alpha> and define angle function.\<close>
            have hparam: "\<forall>\<alpha>\<in>{..<n}. \<exists>h_\<alpha> \<theta>q_\<alpha> \<theta>p_\<alpha>.
                top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>
              \<and> top1_R_to_S1 \<theta>q_\<alpha> = inv_into top1_S1 h_\<alpha> (q \<alpha>)
              \<and> top1_R_to_S1 \<theta>p_\<alpha> = inv_into top1_S1 h_\<alpha> p
              \<and> \<theta>q_\<alpha> < \<theta>p_\<alpha> \<and> \<theta>p_\<alpha> < \<theta>q_\<alpha> + 1"
            proof (intro ballI)
              fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
              obtain h_\<alpha> where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>"
                using hC_props h\<alpha> by (by100 blast)
              have hbij: "bij_betw h_\<alpha> top1_S1 (C \<alpha>)"
                using hh unfolding top1_homeomorphism_on_def by (by100 blast)
              let ?hinv = "inv_into top1_S1 h_\<alpha>"
              have hbij_inv: "bij_betw ?hinv (C \<alpha>) top1_S1"
                using homeomorphism_inverse[OF hh] unfolding top1_homeomorphism_on_def by (by100 blast)
              have hq_in: "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
              have hp_in: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
              define q' where "q' = ?hinv (q \<alpha>)"
              have hq'_S1: "q' \<in> top1_S1"
                using hbij_inv hq_in unfolding q'_def bij_betw_def by (by100 blast)
              define p' where "p' = ?hinv p"
              have hp'_S1: "p' \<in> top1_S1"
                using hbij_inv hp_in unfolding p'_def bij_betw_def by (by100 blast)
              have hp'_ne_q': "p' \<noteq> q'"
              proof
                assume "p' = q'"
                hence "?hinv p = ?hinv (q \<alpha>)" unfolding p'_def q'_def .
                hence "h_\<alpha> (?hinv p) = h_\<alpha> (?hinv (q \<alpha>))" by (by100 simp)
                hence "p = q \<alpha>"
                  using bij_betw_inv_into_right[OF hbij hp_in]
                        bij_betw_inv_into_right[OF hbij hq_in] by (by100 simp)
                thus False using hq h\<alpha> by (by100 blast)
              qed
              \<comment> \<open>Get angles.\<close>
              obtain \<theta>q' where h\<theta>q': "top1_R_to_S1 \<theta>q' = q'"
              proof -
                have "fst q' ^ 2 + snd q' ^ 2 = 1" using hq'_S1 unfolding top1_S1_def by (by100 simp)
                then obtain \<theta> where "fst q' = cos \<theta>" "snd q' = sin \<theta>"
                  using sincos_total_2pi by (by100 metis)
                hence "top1_R_to_S1 (\<theta> / (2 * pi)) = q'"
                  unfolding top1_R_to_S1_def by (simp add: prod_eq_iff)
                thus ?thesis using that by (by100 blast)
              qed
              obtain \<theta>p' where h\<theta>p': "top1_R_to_S1 \<theta>p' = p'"
                  and h\<theta>p'_range: "\<theta>q' < \<theta>p' \<and> \<theta>p' < \<theta>q' + 1"
              proof -
                have "fst p' ^ 2 + snd p' ^ 2 = 1" using hp'_S1 unfolding top1_S1_def by (by100 simp)
                then obtain \<theta>r where hcos: "fst p' = cos \<theta>r" and hsin: "snd p' = sin \<theta>r"
                  using sincos_total_2pi by (by100 metis)
                define \<theta>0 where "\<theta>0 = \<theta>r / (2 * pi)"
                have h\<theta>0: "top1_R_to_S1 \<theta>0 = p'"
                  unfolding top1_R_to_S1_def \<theta>0_def using hcos hsin by (simp add: prod_eq_iff)
                define k where "k = \<lfloor>\<theta>0 - \<theta>q'\<rfloor>"
                define \<theta>a where "\<theta>a = \<theta>0 - of_int k"
                have h\<theta>a_R: "top1_R_to_S1 \<theta>a = p'"
                proof -
                  have "top1_R_to_S1 \<theta>a = top1_R_to_S1 (\<theta>0 + of_int (-k))"
                    unfolding \<theta>a_def by (by100 simp)
                  also have "\<dots> = top1_R_to_S1 \<theta>0" by (rule top1_R_to_S1_int_shift_early)
                  also have "\<dots> = p'" by (rule h\<theta>0)
                  finally show ?thesis .
                qed
                have "\<theta>q' \<le> \<theta>a \<and> \<theta>a < \<theta>q' + 1"
                  unfolding \<theta>a_def k_def by linarith
                moreover have "\<theta>a \<noteq> \<theta>q'"
                proof
                  assume "\<theta>a = \<theta>q'"
                  hence "top1_R_to_S1 \<theta>a = top1_R_to_S1 \<theta>q'" by (by100 simp)
                  hence "p' = q'" using h\<theta>a_R h\<theta>q' by (by100 simp)
                  thus False using hp'_ne_q' by (by100 blast)
                qed
                ultimately have "\<theta>q' < \<theta>a \<and> \<theta>a < \<theta>q' + 1" by (by100 linarith)
                thus ?thesis using that h\<theta>a_R by (by100 blast)
              qed
              show "\<exists>h_\<alpha> \<theta>q_\<alpha> \<theta>p_\<alpha>.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h_\<alpha>
                \<and> top1_R_to_S1 \<theta>q_\<alpha> = inv_into top1_S1 h_\<alpha> (q \<alpha>)
                \<and> top1_R_to_S1 \<theta>p_\<alpha> = inv_into top1_S1 h_\<alpha> p
                \<and> \<theta>q_\<alpha> < \<theta>p_\<alpha> \<and> \<theta>p_\<alpha> < \<theta>q_\<alpha> + 1"
                using hh h\<theta>q' h\<theta>p' h\<theta>p'_range
                unfolding q'_def p'_def by (by100 blast)
            qed
            \<comment> \<open>Choose parameterizations for all \<alpha> < n.\<close>
            obtain h_fam :: "nat \<Rightarrow> (real \<times> real) \<Rightarrow> 'a"
                and \<theta>q_fam \<theta>p_fam :: "nat \<Rightarrow> real" where
                hfam: "\<forall>\<alpha>\<in>{..<n}. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h_fam \<alpha>)
                  \<and> top1_R_to_S1 (\<theta>q_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) (q \<alpha>)
                  \<and> top1_R_to_S1 (\<theta>p_fam \<alpha>) = inv_into top1_S1 (h_fam \<alpha>) p
                  \<and> \<theta>q_fam \<alpha> < \<theta>p_fam \<alpha> \<and> \<theta>p_fam \<alpha> < \<theta>q_fam \<alpha> + 1"
            proof -
              from hparam have "\<forall>\<alpha>\<in>{..<n}. \<exists>h' \<theta>q' \<theta>p'.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h'
                \<and> top1_R_to_S1 \<theta>q' = inv_into top1_S1 h' (q \<alpha>)
                \<and> top1_R_to_S1 \<theta>p' = inv_into top1_S1 h' p
                \<and> \<theta>q' < \<theta>p' \<and> \<theta>p' < \<theta>q' + 1" .
              then obtain hf where hhf: "\<forall>\<alpha>\<in>{..<n}. \<exists>\<theta>q' \<theta>p'.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                \<and> top1_R_to_S1 \<theta>q' = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                \<and> top1_R_to_S1 \<theta>p' = inv_into top1_S1 (hf \<alpha>) p
                \<and> \<theta>q' < \<theta>p' \<and> \<theta>p' < \<theta>q' + 1"
                by (by100 metis)
              then obtain tqf where htqf: "\<forall>\<alpha>\<in>{..<n}. \<exists>\<theta>p'.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                \<and> top1_R_to_S1 (tqf \<alpha>) = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                \<and> top1_R_to_S1 \<theta>p' = inv_into top1_S1 (hf \<alpha>) p
                \<and> tqf \<alpha> < \<theta>p' \<and> \<theta>p' < tqf \<alpha> + 1"
                by (by100 metis)
              then obtain tpf where htpf: "\<forall>\<alpha>\<in>{..<n}.
                  top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (hf \<alpha>)
                \<and> top1_R_to_S1 (tqf \<alpha>) = inv_into top1_S1 (hf \<alpha>) (q \<alpha>)
                \<and> top1_R_to_S1 (tpf \<alpha>) = inv_into top1_S1 (hf \<alpha>) p
                \<and> tqf \<alpha> < tpf \<alpha> \<and> tpf \<alpha> < tqf \<alpha> + 1"
                by (by100 metis)
              thus ?thesis using that[of hf tqf tpf] by (by100 blast)
            qed
            \<comment> \<open>Define angle function for each \<alpha>.\<close>
            define angle_fam :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
              "angle_fam \<alpha> x = (THE \<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1
                \<and> top1_R_to_S1 \<theta> = inv_into top1_S1 (h_fam \<alpha>) x)" for \<alpha> x
            \<comment> \<open>Standalone angle_fam spec: for \<alpha> < n and x \<in> W(\<alpha>), angle_fam gives the angle.\<close>
            have hangle_fam_spec: "\<And>\<alpha> x. \<alpha> \<in> {..<n} \<Longrightarrow> x \<in> W \<alpha> \<Longrightarrow>
                \<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1 \<and>
                top1_R_to_S1 (angle_fam \<alpha> x) = inv_into top1_S1 (h_fam \<alpha>) x"
            proof -
              fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> {..<n}" and hxW: "x \<in> W \<alpha>"
              have hx_C: "x \<in> C \<alpha>" using hxW unfolding W_def by (by100 blast)
              let ?hinv' = "inv_into top1_S1 (h_fam \<alpha>)"
              have hh\<alpha>: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (h_fam \<alpha>)"
                using hfam h\<alpha> by (by100 blast)
              have hbij': "bij_betw (h_fam \<alpha>) top1_S1 (C \<alpha>)"
                using hh\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
              have hbij_inv': "bij_betw ?hinv' (C \<alpha>) top1_S1"
                using homeomorphism_inverse[OF hh\<alpha>]
                unfolding top1_homeomorphism_on_def by (by100 blast)
              have hhinv'_x: "?hinv' x \<in> top1_S1" using hbij_inv' hx_C unfolding bij_betw_def by (by100 blast)
              have hx_neq_q: "x \<noteq> q \<alpha>" using hxW unfolding W_def by (by100 blast)
              have hq_in': "q \<alpha> \<in> C \<alpha>" using hq h\<alpha> by (by100 blast)
              have hhinv'_x_ne_q: "?hinv' x \<noteq> ?hinv' (q \<alpha>)"
              proof
                assume heqq: "?hinv' x = ?hinv' (q \<alpha>)"
                hence "h_fam \<alpha> (?hinv' x) = h_fam \<alpha> (?hinv' (q \<alpha>))" by (by100 simp)
                hence "x = q \<alpha>" using bij_betw_inv_into_right[OF hbij' hx_C]
                    bij_betw_inv_into_right[OF hbij' hq_in'] by (by100 simp)
                thus False using hx_neq_q by (by100 blast)
              qed
              have h\<theta>q_eq: "top1_R_to_S1 (\<theta>q_fam \<alpha>) = ?hinv' (q \<alpha>)"
                using hfam h\<alpha> by (by100 blast)
              have heq_x: "fst (?hinv' x) ^ 2 + snd (?hinv' x) ^ 2 = 1"
                using hhinv'_x unfolding top1_S1_def by (by100 simp)
              obtain \<theta>r where hcos_x: "fst (?hinv' x) = cos \<theta>r" and hsin_x: "snd (?hinv' x) = sin \<theta>r"
                using sincos_total_2pi heq_x by (by100 metis)
              define \<theta>_raw_x where "\<theta>_raw_x = \<theta>r / (2 * pi)"
              have h_raw_x: "top1_R_to_S1 \<theta>_raw_x = ?hinv' x"
                unfolding top1_R_to_S1_def \<theta>_raw_x_def using hcos_x hsin_x by (simp add: prod_eq_iff)
              define k_x where "k_x = \<lfloor>\<theta>_raw_x - \<theta>q_fam \<alpha>\<rfloor>"
              define \<theta>0_x where "\<theta>0_x = \<theta>_raw_x - of_int k_x"
              have h\<theta>0_x_R: "top1_R_to_S1 \<theta>0_x = ?hinv' x"
              proof -
                have "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 (\<theta>_raw_x + of_int (-k_x))"
                  unfolding \<theta>0_x_def by (by100 simp)
                also have "\<dots> = top1_R_to_S1 \<theta>_raw_x" by (rule top1_R_to_S1_int_shift_early)
                also have "\<dots> = ?hinv' x" by (rule h_raw_x)
                finally show ?thesis .
              qed
              have h\<theta>0_x_range: "\<theta>q_fam \<alpha> \<le> \<theta>0_x \<and> \<theta>0_x < \<theta>q_fam \<alpha> + 1"
                unfolding \<theta>0_x_def k_x_def by linarith
              have "\<theta>0_x \<noteq> \<theta>q_fam \<alpha>"
              proof
                assume "\<theta>0_x = \<theta>q_fam \<alpha>"
                hence "top1_R_to_S1 \<theta>0_x = top1_R_to_S1 (\<theta>q_fam \<alpha>)" by (by100 simp)
                hence "?hinv' x = ?hinv' (q \<alpha>)" using h\<theta>0_x_R h\<theta>q_eq by (by100 simp)
                thus False using hhinv'_x_ne_q by (by100 blast)
              qed
              hence h\<theta>0_x_strict: "\<theta>q_fam \<alpha> < \<theta>0_x" using h\<theta>0_x_range by (by100 linarith)
              have h\<theta>0_x: "\<theta>q_fam \<alpha> < \<theta>0_x \<and> \<theta>0_x < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta>0_x = ?hinv' x"
                using h\<theta>0_x_strict h\<theta>0_x_range h\<theta>0_x_R by (by100 blast)
              have huniq_x: "\<And>\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x \<Longrightarrow> \<theta> = \<theta>0_x"
              proof -
                fix \<theta> assume h\<theta>: "\<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>0_x" using h\<theta>0_x_R by (by100 simp)
                hence "cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x) \<and> sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x)"
                  unfolding top1_R_to_S1_def by (by100 simp)
                hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>0_x) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>0_x)"
                  by (by100 blast)
                then obtain j :: int where hj: "2*pi*\<theta> = 2*pi*\<theta>0_x + 2*pi*of_int j"
                  using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                have "2*pi*\<theta> - 2*pi*\<theta>0_x = 2*pi*of_int j" using hj by (by100 linarith)
                hence hd: "2*pi*(\<theta> - \<theta>0_x) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                hence "2*pi \<noteq> 0" by (by100 linarith)
                hence "\<theta> - \<theta>0_x = of_int j" using hd by (by100 simp)
                moreover have "\<theta> - \<theta>0_x > -1 \<and> \<theta> - \<theta>0_x < 1" using h\<theta> h\<theta>0_x by (by100 linarith)
                ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                hence "j = 0" by (by100 linarith)
                thus "\<theta> = \<theta>0_x" using \<open>\<theta> - \<theta>0_x = of_int j\<close> by (by100 simp)
              qed
              have hex1_x: "\<exists>!\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
              proof (rule ex_ex1I)
                show "\<exists>\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                  using h\<theta>0_x by (by100 blast)
              next
                fix a b assume ha: "\<theta>q_fam \<alpha> < a \<and> a < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 a = ?hinv' x"
                    and hb: "\<theta>q_fam \<alpha> < b \<and> b < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 b = ?hinv' x"
                show "a = b" using huniq_x[OF ha] huniq_x[OF hb] by (by100 simp)
              qed
              have hthe_x: "(THE \<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x) = \<theta>0_x"
                by (rule the1_equality[OF hex1_x h\<theta>0_x])
              show "\<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1 \<and>
                  top1_R_to_S1 (angle_fam \<alpha> x) = inv_into top1_S1 (h_fam \<alpha>) x"
                unfolding angle_fam_def using hthe_x h\<theta>0_x by (by100 simp)
            qed
            \<comment> \<open>Define H_V: for x \<in> C(n-1), H_V(x,t) = x.
               For x \<in> W(\<alpha>) with \<alpha> < n-1, contract x to p via angle interpolation.\<close>
            define H_V :: "'a \<times> real \<Rightarrow> 'a" where
              "H_V = (\<lambda>(x, t). if x \<in> ?Cn then x
                     else if \<exists>\<alpha>\<in>{..<(n-1)}. x \<in> W \<alpha> then
                       let \<alpha>0 = (SOME \<alpha>. \<alpha> \<in> {..<(n-1)} \<and> x \<in> W \<alpha>) in
                       h_fam \<alpha>0 (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>0 x + t * \<theta>p_fam \<alpha>0))
                     else x)"
            \<comment> \<open>Note: for p \<in> C(n-1) \<inter> W(\<alpha>), the first branch applies: H_V(p,t) = p.
               This is consistent with the contraction branch since angle_fam \<alpha> p = \<theta>p_fam \<alpha>.\<close>
            \<comment> \<open>Key simplification: for x \<notin> C(n-1) and \<alpha> < n-1 with x \<in> W \<alpha>,
               H_V(x,t) = h_fam \<alpha>'(R_to_S1((1-t)*angle + t*\<theta>p_fam \<alpha>'))
               where \<alpha>' = SOME \<alpha> with x \<in> W \<alpha>.\<close>
            have hH_V_Cn: "\<And>x t. x \<in> ?Cn \<Longrightarrow> H_V (x, t) = x"
              unfolding H_V_def by (by100 simp)
            \<comment> \<open>Reduction: for x \<notin> C(n-1), \<alpha> < n-1 with x \<in> W(\<alpha>):
               H_V(x,t) = h_fam (SOME \<alpha>...) (R_to_S1((1-t)*angle_fam (SOME \<alpha>...) x + t*\<theta>p_fam (SOME \<alpha>...))).\<close>
            have hH_V_W: "\<And>x t \<alpha>0. \<lbrakk>x \<notin> ?Cn; \<alpha>0 \<in> {..<(n-1)}; x \<in> W \<alpha>0\<rbrakk> \<Longrightarrow>
                \<exists>\<alpha>'. \<alpha>' \<in> {..<(n-1)} \<and> x \<in> W \<alpha>' \<and>
                H_V (x, t) = h_fam \<alpha>' (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'))"
            proof -
              fix x :: 'a and t :: real and \<alpha>0 :: nat
              assume hxnCn: "x \<notin> ?Cn" and h\<alpha>0: "\<alpha>0 \<in> {..<(n-1)}" and hx\<alpha>0: "x \<in> W \<alpha>0"
              have hbex: "\<exists>\<alpha>\<in>{..<(n-1)}. x \<in> W \<alpha>" using h\<alpha>0 hx\<alpha>0 by (by100 blast)
              define \<alpha>' where "\<alpha>' = (SOME \<alpha>. \<alpha> \<in> {..<(n-1)} \<and> x \<in> W \<alpha>)"
              have h\<alpha>': "\<alpha>' \<in> {..<(n-1)} \<and> x \<in> W \<alpha>'"
                unfolding \<alpha>'_def using someI_ex[of "\<lambda>\<alpha>. \<alpha> \<in> {..<(n-1)} \<and> x \<in> W \<alpha>"]
                  h\<alpha>0 hx\<alpha>0 by (by100 blast)
              have "H_V (x, t) = (let \<alpha>0 = (SOME \<alpha>. \<alpha> \<in> {..<(n-1)} \<and> x \<in> W \<alpha>) in
                h_fam \<alpha>0 (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>0 x + t * \<theta>p_fam \<alpha>0)))"
                unfolding H_V_def using hxnCn hbex by (by100 simp)
              hence "H_V (x, t) = h_fam \<alpha>' (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'))"
                unfolding \<alpha>'_def Let_def by (by100 simp)
              thus "\<exists>\<alpha>'. \<alpha>' \<in> {..<(n-1)} \<and> x \<in> W \<alpha>' \<and>
                  H_V (x, t) = h_fam \<alpha>' (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'))"
                using h\<alpha>' by (by100 blast)
            qed
            have hH_V_0: "\<forall>x\<in>V_def. H_V (x, 0) = x"
            proof (intro ballI)
              fix x assume hx: "x \<in> V_def"
              show "H_V (x, 0) = x"
              proof (cases "x \<in> ?Cn")
                case True thus ?thesis using hH_V_Cn by (by100 blast)
              next
                case False
                hence "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>)" using hx unfolding V_def_def by (by100 blast)
                then obtain \<alpha>0 where h\<alpha>0: "\<alpha>0 \<in> {..<(n-1)}" and hx\<alpha>0: "x \<in> W \<alpha>0" by (by100 blast)
                obtain \<alpha>' where h\<alpha>': "\<alpha>' \<in> {..<(n-1)}" and hx\<alpha>': "x \<in> W \<alpha>'"
                    and hH_eq: "H_V (x, 0) = h_fam \<alpha>' (top1_R_to_S1 ((1 - 0) * angle_fam \<alpha>' x + 0 * \<theta>p_fam \<alpha>'))"
                  using hH_V_W[OF False h\<alpha>0 hx\<alpha>0] by (by100 blast)
                have h\<alpha>'n: "\<alpha>' \<in> {..<n}" using h\<alpha>' hn2 by (by100 simp)
                have hx_C: "x \<in> C \<alpha>'" using hx\<alpha>' unfolding W_def by (by100 blast)
                have hbij': "bij_betw (h_fam \<alpha>') top1_S1 (C \<alpha>')"
                  using hfam h\<alpha>'n unfolding top1_homeomorphism_on_def by (by100 blast)
                \<comment> \<open>angle_fam \<alpha>' x gives the correct angle.\<close>
                have h_angle: "top1_R_to_S1 (angle_fam \<alpha>' x) = inv_into top1_S1 (h_fam \<alpha>') x"
                proof -
                  let ?hinv' = "inv_into top1_S1 (h_fam \<alpha>')"
                  have hh\<alpha>': "top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>') (subspace_topology X TX (C \<alpha>')) (h_fam \<alpha>')"
                    using hfam h\<alpha>'n by (by100 blast)
                  have hbij_inv': "bij_betw ?hinv' (C \<alpha>') top1_S1"
                    using homeomorphism_inverse[OF hh\<alpha>']
                    unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hhinv'_x: "?hinv' x \<in> top1_S1" using hbij_inv' hx_C unfolding bij_betw_def by (by100 blast)
                  have hx_neq_q: "x \<noteq> q \<alpha>'" using hx\<alpha>' unfolding W_def by (by100 blast)
                  have hq_in': "q \<alpha>' \<in> C \<alpha>'" using hq h\<alpha>'n by (by100 blast)
                  have hhinv'_x_ne_q: "?hinv' x \<noteq> inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                  proof
                    assume heq: "?hinv' x = ?hinv' (q \<alpha>')"
                    hence "h_fam \<alpha>' (?hinv' x) = h_fam \<alpha>' (?hinv' (q \<alpha>'))" by (by100 simp)
                    hence "x = q \<alpha>'" using bij_betw_inv_into_right[OF hbij' hx_C]
                        bij_betw_inv_into_right[OF hbij' hq_in'] by (by100 simp)
                    thus False using hx_neq_q by (by100 blast)
                  qed
                  have h\<theta>q_eq: "top1_R_to_S1 (\<theta>q_fam \<alpha>') = ?hinv' (q \<alpha>')"
                    using hfam h\<alpha>'n by (by100 blast)
                  \<comment> \<open>Get \<theta>0 with R_to_S1(\<theta>0) = hinv(x) in (\<theta>q, \<theta>q+1).\<close>
                  have heq: "fst (?hinv' x) ^ 2 + snd (?hinv' x) ^ 2 = 1"
                    using hhinv'_x unfolding top1_S1_def by (by100 simp)
                  obtain \<theta>r where hcos: "fst (?hinv' x) = cos \<theta>r" and hsin: "snd (?hinv' x) = sin \<theta>r"
                    using sincos_total_2pi heq by (by100 metis)
                  define \<theta>_raw where "\<theta>_raw = \<theta>r / (2 * pi)"
                  have h_raw: "top1_R_to_S1 \<theta>_raw = ?hinv' x"
                    unfolding top1_R_to_S1_def \<theta>_raw_def using hcos hsin by (simp add: prod_eq_iff)
                  define kk where "kk = \<lfloor>\<theta>_raw - \<theta>q_fam \<alpha>'\<rfloor>"
                  define \<theta>0 where "\<theta>0 = \<theta>_raw - of_int kk"
                  have h\<theta>0_R: "top1_R_to_S1 \<theta>0 = ?hinv' x"
                  proof -
                    have "top1_R_to_S1 \<theta>0 = top1_R_to_S1 (\<theta>_raw + of_int (-kk))"
                      unfolding \<theta>0_def by (by100 simp)
                    also have "\<dots> = top1_R_to_S1 \<theta>_raw" by (rule top1_R_to_S1_int_shift_early)
                    also have "\<dots> = ?hinv' x" by (rule h_raw)
                    finally show ?thesis .
                  qed
                  have h\<theta>0_range: "\<theta>q_fam \<alpha>' \<le> \<theta>0 \<and> \<theta>0 < \<theta>q_fam \<alpha>' + 1"
                    unfolding \<theta>0_def kk_def by linarith
                  have "\<theta>0 \<noteq> \<theta>q_fam \<alpha>'"
                  proof
                    assume "\<theta>0 = \<theta>q_fam \<alpha>'"
                    hence "top1_R_to_S1 \<theta>0 = top1_R_to_S1 (\<theta>q_fam \<alpha>')" by (by100 simp)
                    hence "?hinv' x = ?hinv' (q \<alpha>')" using h\<theta>0_R h\<theta>q_eq by (by100 simp)
                    thus False using hhinv'_x_ne_q by (by100 blast)
                  qed
                  hence h\<theta>0_strict: "\<theta>q_fam \<alpha>' < \<theta>0" using h\<theta>0_range by (by100 linarith)
                  have h\<theta>0: "\<theta>q_fam \<alpha>' < \<theta>0 \<and> \<theta>0 < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta>0 = ?hinv' x"
                    using h\<theta>0_strict h\<theta>0_range h\<theta>0_R by (by100 blast)
                  \<comment> \<open>Uniqueness.\<close>
                  have huniq: "\<And>\<theta>. \<theta>q_fam \<alpha>' < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x \<Longrightarrow> \<theta> = \<theta>0"
                  proof -
                    fix \<theta> assume h\<theta>: "\<theta>q_fam \<alpha>' < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                    hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>0" using h\<theta>0_R by (by100 simp)
                    hence "cos (2*pi*\<theta>) = cos (2*pi*\<theta>0) \<and> sin (2*pi*\<theta>) = sin (2*pi*\<theta>0)"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>0) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>0)"
                      by (by100 blast)
                    then obtain j :: int where hj: "2*pi*\<theta> = 2*pi*\<theta>0 + 2*pi*of_int j"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    have "2*pi*\<theta> - 2*pi*\<theta>0 = 2*pi*of_int j" using hj by (by100 linarith)
                    hence hd: "2*pi*(\<theta> - \<theta>0) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                    have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                    hence "2*pi \<noteq> 0" by (by100 linarith)
                    hence "\<theta> - \<theta>0 = of_int j" using hd by (by100 simp)
                    moreover have "\<theta> - \<theta>0 > -1 \<and> \<theta> - \<theta>0 < 1" using h\<theta> h\<theta>0 by (by100 linarith)
                    ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "j = 0" by (by100 linarith)
                    thus "\<theta> = \<theta>0" using \<open>\<theta> - \<theta>0 = of_int j\<close> by (by100 simp)
                  qed
                  have hex1: "\<exists>!\<theta>. \<theta>q_fam \<alpha>' < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                  proof (rule ex_ex1I)
                    show "\<exists>\<theta>. \<theta>q_fam \<alpha>' < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x"
                      using h\<theta>0 by (by100 blast)
                  next
                    fix a b assume ha: "\<theta>q_fam \<alpha>' < a \<and> a < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 a = ?hinv' x"
                        and hb: "\<theta>q_fam \<alpha>' < b \<and> b < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 b = ?hinv' x"
                    show "a = b" using huniq[OF ha] huniq[OF hb] by (by100 simp)
                  qed
                  have hthe: "(THE \<theta>. \<theta>q_fam \<alpha>' < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha>' + 1 \<and> top1_R_to_S1 \<theta> = ?hinv' x) = \<theta>0"
                    by (rule the1_equality[OF hex1 h\<theta>0])
                  show ?thesis unfolding angle_fam_def using hthe h\<theta>0_R by (by100 simp)
                qed
                have "H_V (x, 0) = h_fam \<alpha>' (top1_R_to_S1 (angle_fam \<alpha>' x))"
                  using hH_eq by (by100 simp)
                also have "\<dots> = h_fam \<alpha>' (inv_into top1_S1 (h_fam \<alpha>') x)"
                  using h_angle by (by100 simp)
                also have "\<dots> = x" by (rule bij_betw_inv_into_right[OF hbij' hx_C])
                finally show ?thesis .
              qed
            qed
            have hH_V_1: "\<forall>x\<in>V_def. H_V (x, 1) \<in> ?Cn"
            proof (intro ballI)
              fix x assume hx: "x \<in> V_def"
              show "H_V (x, 1) \<in> ?Cn"
              proof (cases "x \<in> ?Cn")
                case True
                have "H_V (x, 1) = x" using hH_V_Cn[OF True] .
                thus ?thesis using True by (by100 simp)
              next
                case False
                hence "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>)" using hx unfolding V_def_def by (by100 blast)
                then obtain \<alpha>0 where h\<alpha>0: "\<alpha>0 \<in> {..<(n-1)}" and hx\<alpha>0: "x \<in> W \<alpha>0" by (by100 blast)
                obtain \<alpha>' where h\<alpha>': "\<alpha>' \<in> {..<(n-1)}" and hx\<alpha>': "x \<in> W \<alpha>'"
                    and hH_eq: "H_V (x, 1) = h_fam \<alpha>' (top1_R_to_S1 ((1 - 1) * angle_fam \<alpha>' x + 1 * \<theta>p_fam \<alpha>'))"
                  using hH_V_W[OF False h\<alpha>0 hx\<alpha>0] by (by100 blast)
                have h\<alpha>'n: "\<alpha>' \<in> {..<n}" using h\<alpha>' hn2 by (by100 simp)
                have "H_V (x, 1) = h_fam \<alpha>' (top1_R_to_S1 (\<theta>p_fam \<alpha>'))"
                  using hH_eq by (by100 simp)
                also have "top1_R_to_S1 (\<theta>p_fam \<alpha>') = inv_into top1_S1 (h_fam \<alpha>') p"
                  using hfam h\<alpha>'n by (by100 blast)
                also have "h_fam \<alpha>' (inv_into top1_S1 (h_fam \<alpha>') p) = p"
                proof -
                  have "bij_betw (h_fam \<alpha>') top1_S1 (C \<alpha>')"
                    using hfam h\<alpha>'n unfolding top1_homeomorphism_on_def by (by100 blast)
                  moreover have "p \<in> C \<alpha>'" using hC_props h\<alpha>'n by (by100 blast)
                  ultimately show ?thesis by (rule bij_betw_inv_into_right)
                qed
                finally show ?thesis using hp_Cn by (by100 simp)
              qed
            qed
            have hH_V_A: "\<forall>a\<in>?Cn. \<forall>t\<in>I_set. H_V (a, t) = a"
            proof (intro ballI)
              fix a t assume ha: "a \<in> ?Cn" and ht: "t \<in> I_set"
              show "H_V (a, t) = a" unfolding H_V_def using ha by (by100 simp)
            qed
            \<comment> \<open>Continuity of H_V: piecewise continuous on C(n-1)\<times>I (identity) and
               each W(\<alpha>)\<times>I (angle interpolation composed with h_\<alpha>).
               Continuous w.r.t. weak topology by coherent topology condition.\<close>
            have hH_V_cont: "top1_continuous_map_on (V_def \<times> I_set)
                (product_topology_on (subspace_topology X TX V_def) I_top)
                V_def (subspace_topology X TX V_def) H_V"
            proof -
              let ?TV = "subspace_topology X TX V_def"
              let ?TI = "I_top"
              let ?TVI = "product_topology_on ?TV ?TI"
              have hTI: "is_topology_on I_set ?TI"
                by (rule top1_unit_interval_topology_is_topology_on)
              have hTV: "is_topology_on V_def ?TV"
                by (rule subspace_topology_is_topology_on[OF hTX hV_sub])
              have hTVI: "is_topology_on (V_def \<times> I_set) ?TVI"
                by (rule product_topology_on_is_topology_on[OF hTV hTI])
              let ?Ws = "\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>"
              \<comment> \<open>Step 1: C(n-1) is closed in V_def.\<close>
              have hCn_closed_V: "closedin_on V_def ?TV ?Cn"
              proof -
                have hCn_closed_X: "closedin_on X TX ?Cn"
                proof -
                  have hCn_sub_X: "?Cn \<subseteq> X" using hCn_sub .
                  have hall: "\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?Cn)"
                  proof (intro ballI)
                    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<n}"
                    show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> ?Cn)"
                    proof (cases "\<alpha> = n - 1")
                      case True
                      hence "C \<alpha> \<inter> ?Cn = C \<alpha>" by (by100 simp)
                      moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha>)"
                      proof (rule closedin_intro)
                        show "C \<alpha> \<subseteq> C \<alpha>" by (by100 blast)
                        show "C \<alpha> - C \<alpha> \<in> subspace_topology X TX (C \<alpha>)"
                        proof -
                          have "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                          have "{} \<in> subspace_topology X TX (C \<alpha>)"
                            using subspace_topology_is_topology_on[OF hTX \<open>C \<alpha> \<subseteq> X\<close>]
                            unfolding is_topology_on_def by (by100 blast)
                          thus ?thesis by (by100 simp)
                        qed
                      qed
                      ultimately show ?thesis by (by100 simp)
                    next
                      case False
                      hence "C \<alpha> \<inter> ?Cn = {p}" using hC_inter h\<alpha> hn1_in by (by100 blast)
                      moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) {p}"
                      proof -
                        have hC\<alpha>_sub: "C \<alpha> \<subseteq> X" using hC_props h\<alpha> by (by100 blast)
                        have hp_C\<alpha>: "p \<in> C \<alpha>" using hC_props h\<alpha> by (by100 blast)
                        have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
                          by (rule hausdorff_subspace[OF hHausdorff hC\<alpha>_sub])
                        thus ?thesis using hp_C\<alpha>
                          by (rule singleton_closed_in_hausdorff)
                      qed
                      ultimately show ?thesis by (by100 simp)
                    qed
                  qed
                  show ?thesis using iffD2[OF hC_weak[rule_format, OF hCn_sub_X] hall] .
                qed
                have "?Cn = ?Cn \<inter> V_def"
                  using hCn_sub_Vd by (by100 blast)
                thus ?thesis
                  using iffD2[OF Theorem_17_2[OF hTX hV_sub]] hCn_closed_X by (by100 blast)
              qed
              \<comment> \<open>Step 2: \<Union>{W(\<alpha>) | \<alpha> < n-1} is closed in V_def (finite union of closed sets).\<close>
              have hWs_closed_V: "closedin_on V_def ?TV ?Ws"
              proof -
                \<comment> \<open>Each W(\<alpha>) is closed in V_def: W(\<alpha>) = C(\<alpha>) \<inter> V_def and C(\<alpha>) is closed in X.\<close>
                have hW_closed: "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on V_def ?TV (W \<alpha>)"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
                  \<comment> \<open>C(\<alpha>) is closed in X.\<close>
                  have hC\<alpha>_closed_X: "closedin_on X TX (C \<alpha>)"
                  proof -
                    have hC\<alpha>_sub_X: "C \<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
                    have hall: "\<forall>\<beta>\<in>{..<n}. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                    proof (intro ballI)
                      fix \<beta> assume h\<beta>: "\<beta> \<in> {..<n}"
                      show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                      proof (cases "\<beta> = \<alpha>")
                        case True
                        hence "C \<beta> \<inter> C \<alpha> = C \<alpha>" by (by100 simp)
                        moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha>)"
                        proof (rule closedin_intro)
                          show "C \<alpha> \<subseteq> C \<alpha>" by (by100 blast)
                          show "C \<alpha> - C \<alpha> \<in> subspace_topology X TX (C \<alpha>)"
                          proof -
                            have "{} \<in> subspace_topology X TX (C \<alpha>)"
                              using subspace_topology_is_topology_on[OF hTX hC\<alpha>_sub_X]
                              unfolding is_topology_on_def by (by100 blast)
                            thus ?thesis by (by100 simp)
                          qed
                        qed
                        ultimately show ?thesis using True by (by100 simp)
                      next
                        case False
                        hence "C \<beta> \<inter> C \<alpha> = {p}" using hC_inter h\<beta> h\<alpha>n by (by100 blast)
                        moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) {p}"
                        proof -
                          have "C \<beta> \<subseteq> X" using hC_props h\<beta> by (by100 blast)
                          have "p \<in> C \<beta>" using hC_props h\<beta> by (by100 blast)
                          have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                            by (rule hausdorff_subspace[OF hHausdorff \<open>C \<beta> \<subseteq> X\<close>])
                          thus ?thesis using \<open>p \<in> C \<beta>\<close>
                            by (rule singleton_closed_in_hausdorff)
                        qed
                        ultimately show ?thesis by (by100 simp)
                      qed
                    qed
                    show ?thesis using iffD2[OF hC_weak[rule_format, OF hC\<alpha>_sub_X] hall] .
                  qed
                  \<comment> \<open>W(\<alpha>) = C(\<alpha>) \<inter> V_def.\<close>
                  have "W \<alpha> = C \<alpha> \<inter> V_def"
                  proof -
                    have "W \<alpha> \<subseteq> V_def" unfolding V_def_def using h\<alpha> by (by100 blast)
                    moreover have "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
                    moreover have "\<forall>x. x \<in> C \<alpha> \<and> x \<in> V_def \<longrightarrow> x \<in> W \<alpha>"
                    proof (intro allI impI)
                      fix x assume hx: "x \<in> C \<alpha> \<and> x \<in> V_def"
                      show "x \<in> W \<alpha>"
                      proof (rule ccontr)
                        assume "x \<notin> W \<alpha>"
                        hence "x = q \<alpha>" using hx unfolding W_def by (by100 blast)
                        moreover have "q \<alpha> \<notin> V_def"
                        proof -
                          have "q \<alpha> \<noteq> p" using hq h\<alpha>n by (by100 blast)
                          have "q \<alpha> \<in> C \<alpha>" using hq h\<alpha>n by (by100 blast)
                          have "q \<alpha> \<notin> W \<alpha>" unfolding W_def by (by100 blast)
                          moreover have "\<forall>\<beta>\<in>{..<(n-1)}. \<beta> \<noteq> \<alpha> \<longrightarrow> q \<alpha> \<notin> W \<beta>"
                          proof (intro ballI impI)
                            fix \<beta> assume h\<beta>': "\<beta> \<in> {..<(n-1)}" and hne: "\<beta> \<noteq> \<alpha>"
                            have h\<beta>n': "\<beta> \<in> {..<n}" using h\<beta>' hn2 by (by100 simp)
                            have "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha>n h\<beta>n' hne by (by100 blast)
                            hence "q \<alpha> \<notin> C \<beta>" using \<open>q \<alpha> \<in> C \<alpha>\<close> \<open>q \<alpha> \<noteq> p\<close> by (by100 blast)
                            thus "q \<alpha> \<notin> W \<beta>" unfolding W_def by (by100 blast)
                          qed
                          moreover have "q \<alpha> \<notin> ?Cn"
                          proof -
                            have "\<alpha> \<noteq> n - 1" using h\<alpha> by (by100 simp)
                            hence "C \<alpha> \<inter> ?Cn = {p}" using hC_inter h\<alpha>n hn1_in by (by100 blast)
                            thus ?thesis using \<open>q \<alpha> \<in> C \<alpha>\<close> \<open>q \<alpha> \<noteq> p\<close> by (by100 blast)
                          qed
                          moreover have "q \<alpha> \<notin> ?Ws"
                          proof
                            assume "q \<alpha> \<in> ?Ws"
                            then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hq\<beta>: "q \<alpha> \<in> W \<beta>"
                              by (by100 blast)
                            show False
                            proof (cases "\<beta> = \<alpha>")
                              case True thus False using hq\<beta> \<open>q \<alpha> \<notin> W \<alpha>\<close> by (by100 blast)
                            next
                              case False
                              thus False using hq\<beta> \<open>\<forall>\<beta>\<in>{..<n - 1}. \<beta> \<noteq> \<alpha> \<longrightarrow> q \<alpha> \<notin> W \<beta>\<close> h\<beta> by (by100 blast)
                            qed
                          qed
                          ultimately show ?thesis unfolding V_def_def by (by100 blast)
                        qed
                        ultimately show False using hx by (by100 blast)
                      qed
                    qed
                    ultimately show ?thesis by (by100 blast)
                  qed
                  have "closedin_on V_def ?TV (W \<alpha>) \<longleftrightarrow>
                      (\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> V_def)"
                    by (rule Theorem_17_2[OF hTX hV_sub])
                  moreover have "\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> V_def"
                    using hC\<alpha>_closed_X \<open>W \<alpha> = C \<alpha> \<inter> V_def\<close> by (by100 blast)
                  ultimately show "closedin_on V_def ?TV (W \<alpha>)" by (by100 blast)
                qed
                \<comment> \<open>Finite union of closed sets is closed.\<close>
                have hfin: "finite {..<(n-1)}" by (by100 simp)
                have hWs_eq: "?Ws = \<Union>((\<lambda>\<alpha>. W \<alpha>) ` {..<(n-1)})" by (by100 blast)
                show ?thesis using conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hTV]]]]
                  hfin hW_closed by (by100 blast)
              qed
              \<comment> \<open>Step 3: Cover V_def.\<close>
              have hcover: "(?Cn \<times> I_set) \<union> (?Ws \<times> I_set) = V_def \<times> I_set"
              proof -
                have "V_def = ?Cn \<union> ?Ws" unfolding V_def_def by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              \<comment> \<open>Step 4: C(n-1) \<times> I_set is closed in V_def \<times> I_set.\<close>
              have hCnI_closed: "closedin_on (V_def \<times> I_set) ?TVI (?Cn \<times> I_set)"
              proof (rule closedin_intro)
                show "?Cn \<times> I_set \<subseteq> V_def \<times> I_set" using hCn_sub_Vd by (by100 blast)
                have "V_def \<times> I_set - ?Cn \<times> I_set = (V_def - ?Cn) \<times> I_set" by (by100 blast)
                moreover have "(V_def - ?Cn) \<in> ?TV"
                  using hCn_closed_V unfolding closedin_on_def by (by100 blast)
                moreover have "I_set \<in> ?TI"
                  using hTI unfolding is_topology_on_def by (by100 blast)
                ultimately show "V_def \<times> I_set - ?Cn \<times> I_set \<in> ?TVI"
                  using product_rect_open by (by100 simp)
              qed
              \<comment> \<open>Step 5: \<Union>W(\<alpha>) \<times> I_set is closed in V_def \<times> I_set.\<close>
              have hWsI_closed: "closedin_on (V_def \<times> I_set) ?TVI (?Ws \<times> I_set)"
              proof (rule closedin_intro)
                show "?Ws \<times> I_set \<subseteq> V_def \<times> I_set"
                  unfolding V_def_def by (by100 blast)
                have "V_def \<times> I_set - ?Ws \<times> I_set = (V_def - ?Ws) \<times> I_set" by (by100 blast)
                moreover have "(V_def - ?Ws) \<in> ?TV"
                  using hWs_closed_V unfolding closedin_on_def by (by100 blast)
                moreover have "I_set \<in> ?TI"
                  using hTI unfolding is_topology_on_def by (by100 blast)
                ultimately show "V_def \<times> I_set - ?Ws \<times> I_set \<in> ?TVI"
                  using product_rect_open by (by100 simp)
              qed
              \<comment> \<open>Step 6: H_V maps V_def \<times> I_set into V_def.\<close>
              have hH_V_range: "\<forall>p\<in>V_def \<times> I_set. H_V p \<in> V_def"
              proof (intro ballI)
                fix xt assume hxt: "xt \<in> V_def \<times> I_set"
                obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> V_def" and ht: "t \<in> I_set"
                  using hxt by (by100 blast)
                show "H_V xt \<in> V_def"
                proof (cases "x \<in> ?Cn")
                  case True
                  have "H_V xt = x" unfolding hxt_eq using hH_V_Cn[OF True] by (by100 simp)
                  thus ?thesis using True hCn_sub_Vd by (by100 blast)
                next
                  case False
                  hence "x \<in> (\<Union>\<alpha>\<in>{..<(n-1)}. W \<alpha>)" using hx unfolding V_def_def by (by100 blast)
                  then obtain \<alpha>0 where h\<alpha>0: "\<alpha>0 \<in> {..<(n-1)}" and hx\<alpha>0: "x \<in> W \<alpha>0" by (by100 blast)
                  obtain \<alpha>' where h\<alpha>': "\<alpha>' \<in> {..<(n-1)}" and hx\<alpha>': "x \<in> W \<alpha>'"
                      and hH_eq: "H_V (x, t) = h_fam \<alpha>' (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'))"
                    using hH_V_W[OF False h\<alpha>0 hx\<alpha>0] by (by100 blast)
                  have h\<alpha>'n: "\<alpha>' \<in> {..<n}" using h\<alpha>' hn2 by (by100 simp)
                  \<comment> \<open>angle_fam \<alpha>' x is in (\<theta>q, \<theta>q+1).\<close>
                  have h_angle_spec: "\<theta>q_fam \<alpha>' < angle_fam \<alpha>' x \<and> angle_fam \<alpha>' x < \<theta>q_fam \<alpha>' + 1"
                    using hangle_fam_spec[OF h\<alpha>'n hx\<alpha>'] by (by100 blast)
                  \<comment> \<open>\<theta>p_fam \<alpha>' is in (\<theta>q, \<theta>q+1).\<close>
                  have h\<theta>p_range: "\<theta>q_fam \<alpha>' < \<theta>p_fam \<alpha>' \<and> \<theta>p_fam \<alpha>' < \<theta>q_fam \<alpha>' + 1"
                    using hfam h\<alpha>'n by (by100 blast)
                  \<comment> \<open>Convex combination stays in (\<theta>q, \<theta>q+1).\<close>
                  have ht_range: "0 \<le> t \<and> t \<le> 1"
                  proof -
                    have "t \<in> {0..1::real}" using ht unfolding top1_unit_interval_def by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                  have hconv: "\<theta>q_fam \<alpha>' < (1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'
                      \<and> (1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>' < \<theta>q_fam \<alpha>' + 1"
                  proof (intro conjI)
                    have h1t_nn: "(1-t) \<ge> 0" using ht_range by (by100 linarith)
                    have ht_nn: "t \<ge> 0" using ht_range by (by100 linarith)
                    have h1: "(1-t) * angle_fam \<alpha>' x \<ge> (1-t) * \<theta>q_fam \<alpha>'"
                      using mult_left_mono[of "\<theta>q_fam \<alpha>'" "angle_fam \<alpha>' x" "1-t"]
                        h_angle_spec h1t_nn by (by100 linarith)
                    have h2: "t * \<theta>p_fam \<alpha>' \<ge> t * \<theta>q_fam \<alpha>'"
                      using mult_left_mono[of "\<theta>q_fam \<alpha>'" "\<theta>p_fam \<alpha>'" t]
                        h\<theta>p_range ht_nn by (by100 linarith)
                    show "\<theta>q_fam \<alpha>' < (1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'"
                    proof (cases "t = 1")
                      case True thus ?thesis using h\<theta>p_range by (by100 simp)
                    next
                      case False
                      hence h1t_pos: "(1-t) > 0" using ht_range by (by100 linarith)
                      have "(1-t) * \<theta>q_fam \<alpha>' < (1-t) * angle_fam \<alpha>' x"
                        using mult_strict_left_mono[of "\<theta>q_fam \<alpha>'" "angle_fam \<alpha>' x" "1-t"]
                          h_angle_spec h1t_pos by (by100 linarith)
                      hence "(1-t) * \<theta>q_fam \<alpha>' + t * \<theta>q_fam \<alpha>'
                          < (1-t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'"
                        using h2 by (by100 linarith)
                      moreover have "(1-t) * \<theta>q_fam \<alpha>' + t * \<theta>q_fam \<alpha>' = \<theta>q_fam \<alpha>'"
                        by (simp add: algebra_simps)
                      ultimately show ?thesis by (by100 linarith)
                    qed
                    show "(1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>' < \<theta>q_fam \<alpha>' + 1"
                    proof -
                      have h3: "(1 - t) * angle_fam \<alpha>' x \<le> (1 - t) * (\<theta>q_fam \<alpha>' + 1)"
                        using mult_left_mono[of "angle_fam \<alpha>' x" "\<theta>q_fam \<alpha>' + 1" "1-t"]
                          h_angle_spec h1t_nn by (by100 linarith)
                      have h4: "t * \<theta>p_fam \<alpha>' \<le> t * (\<theta>q_fam \<alpha>' + 1)"
                        using mult_left_mono[of "\<theta>p_fam \<alpha>'" "\<theta>q_fam \<alpha>' + 1" t]
                          h\<theta>p_range ht_nn by (by100 linarith)
                      have "(1-t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'
                          \<le> (1-t) * (\<theta>q_fam \<alpha>' + 1) + t * (\<theta>q_fam \<alpha>' + 1)"
                        using h3 h4 by (by100 linarith)
                      moreover have "(1-t) * (\<theta>q_fam \<alpha>' + 1) + t * (\<theta>q_fam \<alpha>' + 1) = \<theta>q_fam \<alpha>' + 1"
                        by (simp add: algebra_simps)
                      ultimately have "(1-t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>' \<le> \<theta>q_fam \<alpha>' + 1"
                        by (by100 linarith)
                      moreover have "(1-t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>' \<noteq> \<theta>q_fam \<alpha>' + 1"
                      proof (cases "t = 0")
                        case True thus ?thesis using h_angle_spec by (by100 simp)
                      next
                        case False
                        hence "t > 0" using ht_range by (by100 linarith)
                        hence "t * \<theta>p_fam \<alpha>' < t * (\<theta>q_fam \<alpha>' + 1)"
                          using mult_strict_left_mono[of "\<theta>p_fam \<alpha>'" "\<theta>q_fam \<alpha>' + 1" t]
                            h\<theta>p_range by (by100 linarith)
                        hence "(1-t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'
                            < (1-t) * (\<theta>q_fam \<alpha>' + 1) + t * (\<theta>q_fam \<alpha>' + 1)"
                          using h3 by (by100 linarith)
                        moreover have "(1-t) * (\<theta>q_fam \<alpha>' + 1) + t * (\<theta>q_fam \<alpha>' + 1) = \<theta>q_fam \<alpha>' + 1"
                          by (simp add: algebra_simps)
                        ultimately show ?thesis by (by100 linarith)
                      qed
                      ultimately show ?thesis by (by100 linarith)
                    qed
                  qed
                  \<comment> \<open>The interpolated angle is not \<theta>q_fam, so R_to_S1 of it is not q'.\<close>
                  let ?\<theta>_interp = "(1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'"
                  have h\<theta>_neq_q: "top1_R_to_S1 ?\<theta>_interp \<noteq> inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                  proof
                    assume heqq: "top1_R_to_S1 ?\<theta>_interp = inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                    have h\<theta>q_eq: "top1_R_to_S1 (\<theta>q_fam \<alpha>') = inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                      using hfam h\<alpha>'n by (by100 blast)
                    hence "top1_R_to_S1 ?\<theta>_interp = top1_R_to_S1 (\<theta>q_fam \<alpha>')" using heqq by (by100 simp)
                    hence "cos (2*pi*?\<theta>_interp) = cos (2*pi*\<theta>q_fam \<alpha>') \<and> sin (2*pi*?\<theta>_interp) = sin (2*pi*\<theta>q_fam \<alpha>')"
                      unfolding top1_R_to_S1_def by (by100 simp)
                    hence "sin (2*pi*?\<theta>_interp) = sin (2*pi*\<theta>q_fam \<alpha>') \<and> cos (2*pi*?\<theta>_interp) = cos (2*pi*\<theta>q_fam \<alpha>')"
                      by (by100 blast)
                    then obtain j :: int where hj: "2*pi*?\<theta>_interp = 2*pi*\<theta>q_fam \<alpha>' + 2*pi*of_int j"
                      using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                    have "2*pi*(?\<theta>_interp - \<theta>q_fam \<alpha>') = 2*pi*of_int j"
                      using hj by (simp only: right_diff_distrib)
                    moreover have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                    hence "2*pi \<noteq> 0" by (by100 linarith)
                    ultimately have "?\<theta>_interp - \<theta>q_fam \<alpha>' = of_int j" by (by100 simp)
                    moreover have "?\<theta>_interp - \<theta>q_fam \<alpha>' > 0 \<and> ?\<theta>_interp - \<theta>q_fam \<alpha>' < 1"
                      using hconv by (by100 linarith)
                    ultimately have hj_bounds: "of_int j > (0::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                    hence "j = 0" by (by100 linarith)
                    hence "of_int j = (0::real)" by (by100 simp)
                    thus False using hj_bounds by (by100 linarith)
                  qed
                  \<comment> \<open>R_to_S1 of interp is in S1.\<close>
                  have hinterp_S1: "top1_R_to_S1 ?\<theta>_interp \<in> top1_S1"
                    unfolding top1_S1_def top1_R_to_S1_def by (by100 simp)
                  \<comment> \<open>h_fam maps S1 to C(\<alpha>'), so h_fam(R_to_S1(interp)) \<in> C(\<alpha>').\<close>
                  have hbij': "bij_betw (h_fam \<alpha>') top1_S1 (C \<alpha>')"
                    using hfam h\<alpha>'n unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hresult_C: "h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp) \<in> C \<alpha>'"
                    using hbij' hinterp_S1 unfolding bij_betw_def by (by100 blast)
                  \<comment> \<open>It's not q(\<alpha>').\<close>
                  have hresult_neq_q: "h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp) \<noteq> q \<alpha>'"
                  proof
                    assume "h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp) = q \<alpha>'"
                    have hq_in': "q \<alpha>' \<in> C \<alpha>'" using hq h\<alpha>'n by (by100 blast)
                    have "inv_into top1_S1 (h_fam \<alpha>') (h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp))
                        = inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                      using \<open>h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp) = q \<alpha>'\<close> by (by100 simp)
                    moreover have "inv_into top1_S1 (h_fam \<alpha>') (h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp))
                        = top1_R_to_S1 ?\<theta>_interp"
                      using bij_betw_inv_into_left[OF hbij' hinterp_S1] .
                    ultimately have "top1_R_to_S1 ?\<theta>_interp = inv_into top1_S1 (h_fam \<alpha>') (q \<alpha>')"
                      by (by100 simp)
                    thus False using h\<theta>_neq_q by (by100 blast)
                  qed
                  \<comment> \<open>So h_fam(interp) \<in> W(\<alpha>') = C(\<alpha>') - {q(\<alpha>')}.\<close>
                  have "h_fam \<alpha>' (top1_R_to_S1 ?\<theta>_interp) \<in> W \<alpha>'"
                    using hresult_C hresult_neq_q unfolding W_def by (by100 blast)
                  hence "H_V xt \<in> W \<alpha>'" unfolding hxt_eq using hH_eq by (by100 simp)
                  moreover have "W \<alpha>' \<subseteq> V_def" unfolding V_def_def using h\<alpha>' by (by100 blast)
                  ultimately show ?thesis by (by100 blast)
                qed
              qed
              \<comment> \<open>Step 7: H_V continuous on C(n-1) \<times> I_set (identity/projection).\<close>
              have hH_V_Cn: "top1_continuous_map_on (?Cn \<times> I_set)
                  (subspace_topology (V_def \<times> I_set) ?TVI (?Cn \<times> I_set))
                  V_def ?TV H_V"
              proof -
                \<comment> \<open>H_V = pi1 on C(n-1) \<times> I_set.\<close>
                have heq: "\<forall>xt\<in>?Cn \<times> I_set. H_V xt = pi1 xt"
                proof (intro ballI)
                  fix xt assume hxt: "xt \<in> ?Cn \<times> I_set"
                  obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> ?Cn" and ht: "t \<in> I_set"
                    using hxt by (by100 blast)
                  show "H_V xt = pi1 xt"
                    unfolding hxt_eq H_V_def pi1_def using hx by (by100 simp)
                qed
                \<comment> \<open>Subspace topology = product of subspaces.\<close>
                let ?TCn = "subspace_topology X TX ?Cn"
                have hTCneq: "subspace_topology (V_def \<times> I_set) ?TVI (?Cn \<times> I_set)
                    = product_topology_on ?TCn ?TI"
                proof -
                  have hT163: "product_topology_on (subspace_topology V_def ?TV ?Cn) (subspace_topology I_set ?TI I_set)
                      = subspace_topology (V_def \<times> I_set) ?TVI (?Cn \<times> I_set)"
                    by (rule Theorem_16_3[OF hTV hTI])
                  have "subspace_topology (V_def \<times> I_set) ?TVI (?Cn \<times> I_set)
                      = product_topology_on (subspace_topology V_def ?TV ?Cn) (subspace_topology I_set ?TI I_set)"
                    using hT163[symmetric] .
                  moreover have "subspace_topology V_def ?TV ?Cn = ?TCn"
                    by (rule subspace_topology_trans[OF hCn_sub_Vd])
                  moreover have "subspace_topology I_set ?TI I_set = ?TI"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>?TI. U \<subseteq> I_set"
                    proof (intro ballI)
                      fix U assume "U \<in> ?TI"
                      thus "U \<subseteq> I_set"
                        unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                    qed
                  qed
                  ultimately show ?thesis by (simp only:)
                qed
                have hTCn: "is_topology_on ?Cn ?TCn"
                  by (rule subspace_topology_is_topology_on[OF hTX hCn_sub])
                have hpi1_cont: "top1_continuous_map_on (?Cn \<times> I_set)
                    (product_topology_on ?TCn ?TI) ?Cn ?TCn pi1"
                  by (rule top1_continuous_pi1[OF hTCn hTI])
                have hpi1_V: "top1_continuous_map_on (?Cn \<times> I_set)
                    (product_topology_on ?TCn ?TI) V_def ?TV pi1"
                  by (rule top1_continuous_map_on_codomain_enlarge[OF hpi1_cont hCn_sub_Vd hV_sub])
                have "top1_continuous_map_on (?Cn \<times> I_set)
                    (product_topology_on ?TCn ?TI) V_def ?TV H_V"
                  using iffD2[OF top1_continuous_map_on_cong[OF heq] hpi1_V] .
                thus ?thesis using hTCneq by (simp only:)
              qed
              \<comment> \<open>Step 8: H_V continuous on \<Union>W(\<alpha>) \<times> I_set.\<close>
              have hH_V_Ws: "top1_continuous_map_on (?Ws \<times> I_set)
                  (subspace_topology (V_def \<times> I_set) ?TVI (?Ws \<times> I_set))
                  V_def ?TV H_V"
              proof -
                \<comment> \<open>The subspace topology on Ws \<times> I from V_def \<times> I equals the subspace from X \<times> I.\<close>
                have hWs_sub_Vd: "?Ws \<subseteq> V_def" unfolding V_def_def by (by100 blast)
                have hWs_sub_X: "?Ws \<subseteq> X"
                proof (intro UN_subset_iff[THEN iffD2] ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
                  have "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
                  moreover have "C \<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
                  ultimately show "W \<alpha> \<subseteq> X" by (by100 blast)
                qed
                let ?TWs = "subspace_topology X TX ?Ws"
                have hTWs: "is_topology_on ?Ws ?TWs"
                  by (rule subspace_topology_is_topology_on[OF hTX hWs_sub_X])
                \<comment> \<open>Subspace topology on ?Ws \<times> I_set from V_def \<times> I_set.\<close>
                have hTWsI_eq: "subspace_topology (V_def \<times> I_set) ?TVI (?Ws \<times> I_set)
                    = product_topology_on ?TWs ?TI"
                proof -
                  have hT163: "product_topology_on (subspace_topology V_def ?TV ?Ws) (subspace_topology I_set ?TI I_set)
                      = subspace_topology (V_def \<times> I_set) ?TVI (?Ws \<times> I_set)"
                    by (rule Theorem_16_3[OF hTV hTI])
                  have "subspace_topology (V_def \<times> I_set) ?TVI (?Ws \<times> I_set)
                      = product_topology_on (subspace_topology V_def ?TV ?Ws) (subspace_topology I_set ?TI I_set)"
                    using hT163[symmetric] .
                  moreover have "subspace_topology V_def ?TV ?Ws = ?TWs"
                    by (rule subspace_topology_trans[OF hWs_sub_Vd])
                  moreover have "subspace_topology I_set ?TI I_set = ?TI"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>?TI. U \<subseteq> I_set"
                    proof (intro ballI)
                      fix U assume "U \<in> ?TI"
                      thus "U \<subseteq> I_set"
                        unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                    qed
                  qed
                  ultimately show ?thesis by (simp only:)
                qed
                have hTWsI: "is_topology_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)"
                  by (rule product_topology_on_is_topology_on[OF hTWs hTI])
                \<comment> \<open>Step 8a: For each \<alpha> < n-1, H_V is continuous on W(\<alpha>) \<times> I_set
                   with values in V_def, where the domain topology is
                   subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set).\<close>
                have hH_V_each: "\<forall>\<alpha>\<in>{..<(n-1)}. top1_continuous_map_on (W \<alpha> \<times> I_set)
                    (product_topology_on (subspace_topology X TX (W \<alpha>)) ?TI)
                    V_def ?TV H_V"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
                  let ?TW\<alpha> = "subspace_topology X TX (W \<alpha>)"
                  let ?C\<alpha> = "C \<alpha>"
                  let ?TC\<alpha> = "subspace_topology X TX ?C\<alpha>"
                  have hW\<alpha>_sub_C: "W \<alpha> \<subseteq> ?C\<alpha>" unfolding W_def by (by100 blast)
                  have hC\<alpha>_sub_X: "?C\<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
                  have hW\<alpha>_sub_X: "W \<alpha> \<subseteq> X" using hW\<alpha>_sub_C hC\<alpha>_sub_X by (by100 blast)
                  have hW\<alpha>_sub_Vd: "W \<alpha> \<subseteq> V_def" unfolding V_def_def using h\<alpha> by (by100 blast)
                  have hTW\<alpha>: "is_topology_on (W \<alpha>) ?TW\<alpha>"
                    by (rule subspace_topology_is_topology_on[OF hTX hW\<alpha>_sub_X])
                  have hTW\<alpha>I: "is_topology_on (W \<alpha> \<times> I_set) (product_topology_on ?TW\<alpha> ?TI)"
                    by (rule product_topology_on_is_topology_on[OF hTW\<alpha> hTI])
                  \<comment> \<open>Homeomorphism for C(\<alpha>).\<close>
                  have hh\<alpha>: "top1_homeomorphism_on top1_S1 top1_S1_topology
                      ?C\<alpha> ?TC\<alpha> (h_fam \<alpha>)"
                    using hfam h\<alpha>n by (by100 blast)
                  have hbij\<alpha>: "bij_betw (h_fam \<alpha>) top1_S1 ?C\<alpha>"
                    using hh\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                  let ?hinv\<alpha> = "inv_into top1_S1 (h_fam \<alpha>)"
                  have hbij_inv\<alpha>: "bij_betw ?hinv\<alpha> ?C\<alpha> top1_S1"
                    using homeomorphism_inverse[OF hh\<alpha>]
                    unfolding top1_homeomorphism_on_def by (by100 blast)
                  have h\<theta>q_eq: "top1_R_to_S1 (\<theta>q_fam \<alpha>) = ?hinv\<alpha> (q \<alpha>)"
                    using hfam h\<alpha>n by (by100 blast)
                  have h\<theta>p_eq: "top1_R_to_S1 (\<theta>p_fam \<alpha>) = ?hinv\<alpha> p"
                    using hfam h\<alpha>n by (by100 blast)
                  have h\<theta>p_range: "\<theta>q_fam \<alpha> < \<theta>p_fam \<alpha> \<and> \<theta>p_fam \<alpha> < \<theta>q_fam \<alpha> + 1"
                    using hfam h\<alpha>n by (by100 blast)
                  have hq_in\<alpha>: "q \<alpha> \<in> ?C\<alpha>" using hq h\<alpha>n by (by100 blast)
                  have hp_in\<alpha>: "p \<in> ?C\<alpha>" using hC_props h\<alpha>n by (by100 blast)
                  have hq'_S1\<alpha>: "?hinv\<alpha> (q \<alpha>) \<in> top1_S1"
                    using hbij_inv\<alpha> hq_in\<alpha> unfolding bij_betw_def by (by100 blast)
                  have hp'_S1\<alpha>: "?hinv\<alpha> p \<in> top1_S1"
                    using hbij_inv\<alpha> hp_in\<alpha> unfolding bij_betw_def by (by100 blast)
                  \<comment> \<open>Step A: angle_fam \<alpha> is continuous W(\<alpha>) \<rightarrow> R.\<close>
                  have hangle_cont: "top1_continuous_map_on (W \<alpha>) ?TW\<alpha>
                      (UNIV :: real set) top1_open_sets (angle_fam \<alpha>)"
                  proof (rule continuous_map_onI)
                    show "\<forall>x\<in>W \<alpha>. angle_fam \<alpha> x \<in> (UNIV :: real set)" by (by100 blast)
                  next
                    show "\<forall>V\<in>top1_open_sets. {x \<in> W \<alpha>. angle_fam \<alpha> x \<in> V} \<in> ?TW\<alpha>"
                    proof (intro ballI)
                      fix V assume hV: "V \<in> (top1_open_sets :: real set set)"
                      let ?pre = "{x \<in> W \<alpha>. angle_fam \<alpha> x \<in> V}"
                      have hpre_sub: "?pre \<subseteq> W \<alpha>" by (by100 blast)
                      show "?pre \<in> ?TW\<alpha>"
                      proof (rule top1_open_of_local_subsets[OF hTW\<alpha> hpre_sub])
                        show "\<forall>x\<in>?pre. \<exists>U\<in>?TW\<alpha>. x \<in> U \<and> U \<subseteq> ?pre"
                        proof (intro ballI)
                          fix x assume hx_pre: "x \<in> ?pre"
                          hence hxW: "x \<in> W \<alpha>" and hax_V: "angle_fam \<alpha> x \<in> V" by (by100 blast)+
                          have hxC: "x \<in> ?C\<alpha>" using hxW unfolding W_def by (by100 blast)
                          have hx_ne_q: "x \<noteq> q \<alpha>" using hxW unfolding W_def by (by100 blast)
                          have hhinv_x_S1: "?hinv\<alpha> x \<in> top1_S1"
                            using hbij_inv\<alpha> hxC unfolding bij_betw_def by (by100 blast)
                          have hhinv_x_ne_q': "?hinv\<alpha> x \<noteq> ?hinv\<alpha> (q \<alpha>)"
                          proof
                            assume "?hinv\<alpha> x = ?hinv\<alpha> (q \<alpha>)"
                            hence "h_fam \<alpha> (?hinv\<alpha> x) = h_fam \<alpha> (?hinv\<alpha> (q \<alpha>))" by (by100 simp)
                            hence "x = q \<alpha>"
                              using bij_betw_inv_into_right[OF hbij\<alpha> hxC]
                                bij_betw_inv_into_right[OF hbij\<alpha> hq_in\<alpha>]
                              by (by100 simp)
                            thus False using hx_ne_q by (by100 blast)
                          qed
                          have hspec_x: "\<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1 \<and>
                              top1_R_to_S1 (angle_fam \<alpha> x) = ?hinv\<alpha> x"
                            using hangle_fam_spec[OF h\<alpha>n hxW] by (by100 blast)
                          obtain Ux where hhinv_x_Ux: "?hinv\<alpha> x \<in> Ux"
                              and hUx_ec: "top1_evenly_covered_on UNIV top1_open_sets
                                  top1_S1 top1_S1_topology top1_R_to_S1 Ux"
                            using top1_covering_map_on_evenly_covered[OF Theorem_53_1 hhinv_x_S1]
                            by (by100 blast)
                          have hUx_ec_unf: "openin_on top1_S1 top1_S1_topology Ux \<and>
                              (\<exists>\<V>x.
                              (\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs) \<and>
                              (\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}) \<and>
                              {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x \<and>
                              (\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                  (subspace_topology UNIV top1_open_sets Vs)
                                  Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1))"
                            using hUx_ec unfolding top1_evenly_covered_on_def by (by100 fast)
                          obtain \<V>x where hVx_conj:
                              "(\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs) \<and>
                              (\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}) \<and>
                              {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x \<and>
                              (\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                  (subspace_topology UNIV top1_open_sets Vs)
                                  Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1)"
                            using conjunct2[OF hUx_ec_unf] by blast
                          have hVx_open: "\<forall>Vs\<in>\<V>x. openin_on (UNIV::real set) top1_open_sets Vs"
                            and hVx_disj: "\<forall>Vs\<in>\<V>x. \<forall>Vs'\<in>\<V>x. Vs \<noteq> Vs' \<longrightarrow> Vs \<inter> Vs' = {}"
                            and hVx_union: "{t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux} = \<Union>\<V>x"
                            and hVx_homeo: "\<forall>Vs\<in>\<V>x. top1_homeomorphism_on Vs
                                  (subspace_topology UNIV top1_open_sets Vs)
                                  Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1"
                            using hVx_conj by (by100 blast)+
                          have hax_preim: "angle_fam \<alpha> x \<in> {t\<in>(UNIV::real set). top1_R_to_S1 t \<in> Ux}"
                            using hspec_x hhinv_x_Ux by (by100 simp)
                          hence "angle_fam \<alpha> x \<in> \<Union>\<V>x" using hVx_union by (by100 simp)
                          then obtain Vsheet where hVs_in: "Vsheet \<in> \<V>x"
                              and hax_Vs: "angle_fam \<alpha> x \<in> Vsheet"
                            by (by100 blast)
                          have hVs_homeo: "top1_homeomorphism_on Vsheet
                              (subspace_topology UNIV top1_open_sets Vsheet)
                              Ux (subspace_topology top1_S1 top1_S1_topology Ux) top1_R_to_S1"
                            using hVx_homeo hVs_in by (by100 blast)
                          have hVs_open: "Vsheet \<in> top1_open_sets"
                            using hVx_open hVs_in unfolding openin_on_def by (by100 blast)
                          have hVs_inv_cont: "top1_continuous_map_on Ux
                              (subspace_topology top1_S1 top1_S1_topology Ux)
                              Vsheet (subspace_topology UNIV top1_open_sets Vsheet)
                              (inv_into Vsheet top1_R_to_S1)"
                            using hVs_homeo unfolding top1_homeomorphism_on_def
                            by (by100 blast)
                          define I_interval where "I_interval = {\<theta>::real. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1}"
                          have hI_open: "I_interval \<in> top1_open_sets"
                          proof -
                            have "I_interval = {\<theta>q_fam \<alpha> <..< \<theta>q_fam \<alpha> + 1}"
                              unfolding I_interval_def by (by100 auto)
                            thus ?thesis unfolding top1_open_sets_def
                              using open_greaterThanLessThan[of "\<theta>q_fam \<alpha>" "\<theta>q_fam \<alpha> + 1"] by (by100 simp)
                          qed
                          have hVVI_open: "V \<inter> Vsheet \<inter> I_interval \<in> top1_open_sets"
                          proof -
                            have h1: "V \<inter> Vsheet \<in> top1_open_sets"
                              using topology_inter2[OF top1_open_sets_is_topology_on_UNIV hV hVs_open] .
                            show ?thesis
                              using topology_inter2[OF top1_open_sets_is_topology_on_UNIV h1 hI_open] .
                          qed
                          have hax_in_VVI: "angle_fam \<alpha> x \<in> V \<inter> Vsheet \<inter> I_interval"
                            using hax_V hax_Vs hspec_x unfolding I_interval_def by (by100 blast)
                          have hVVI_in_sub: "V \<inter> Vsheet \<inter> I_interval \<in>
                              subspace_topology UNIV top1_open_sets Vsheet"
                            unfolding subspace_topology_def using hVVI_open by (by100 blast)
                          define Sx where "Sx = {s \<in> Ux. inv_into Vsheet top1_R_to_S1 s \<in>
                              V \<inter> Vsheet \<inter> I_interval}"
                          have hSx_open: "Sx \<in> subspace_topology top1_S1 top1_S1_topology Ux"
                            unfolding Sx_def
                            using continuous_map_preimage_open[OF hVs_inv_cont hVVI_in_sub] .
                          have hhinv_x_Sx: "?hinv\<alpha> x \<in> Sx"
                          proof -
                            have "inv_into Vsheet top1_R_to_S1 (?hinv\<alpha> x) = angle_fam \<alpha> x"
                            proof -
                              have hbij_Vs: "bij_betw top1_R_to_S1 Vsheet Ux"
                                using hVs_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                              have "top1_R_to_S1 (angle_fam \<alpha> x) = ?hinv\<alpha> x" using hspec_x by (by100 blast)
                              moreover have "angle_fam \<alpha> x \<in> Vsheet" using hax_Vs .
                              ultimately show ?thesis
                                using inv_into_f_eq[OF bij_betw_imp_inj_on[OF hbij_Vs] hax_Vs]
                                by (by100 simp)
                            qed
                            thus ?thesis unfolding Sx_def
                              using hhinv_x_Ux hax_in_VVI by (by100 simp)
                          qed
                          obtain Ux_outer where hUx_outer: "Ux_outer \<in> top1_S1_topology"
                              and hSx_eq: "Sx = Ux \<inter> Ux_outer"
                            using hSx_open unfolding subspace_topology_def by (by100 blast)
                          have hUx_open_S1: "openin_on top1_S1 top1_S1_topology Ux"
                            using top1_evenly_covered_on_openin_on[OF hUx_ec] .
                          hence hUx_in_S1T: "Ux \<in> top1_S1_topology"
                            unfolding openin_on_def by (by100 blast)
                          have hTS1: "is_topology_on top1_S1 top1_S1_topology"
                            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def
                            by (by100 blast)
                          have hSx_in_S1T: "Sx \<in> top1_S1_topology"
                            using topology_inter2[OF hTS1 hUx_in_S1T hUx_outer] hSx_eq by (by100 simp)
                          \<comment> \<open>hinv_\<alpha> is continuous from C(\<alpha>) to S1.\<close>
                          have hcont_hinv\<alpha>: "top1_continuous_map_on ?C\<alpha> ?TC\<alpha>
                              top1_S1 top1_S1_topology ?hinv\<alpha>"
                            using hh\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                          have hW\<alpha>_sub_C\<alpha>: "W \<alpha> \<subseteq> ?C\<alpha>" unfolding W_def by (by100 blast)
                          have hcont_hinv_W\<alpha>: "top1_continuous_map_on (W \<alpha>) ?TW\<alpha>
                              top1_S1 top1_S1_topology ?hinv\<alpha>"
                          proof -
                            have "?TW\<alpha> = subspace_topology ?C\<alpha> ?TC\<alpha> (W \<alpha>)"
                              by (rule subspace_topology_trans[OF hW\<alpha>_sub_C\<alpha>, symmetric])
                            thus ?thesis using top1_continuous_map_on_restrict_domain_simple[OF
                                hcont_hinv\<alpha> hW\<alpha>_sub_C\<alpha>] by (by100 simp)
                          qed
                          have hSx_preim: "{x' \<in> W \<alpha>. ?hinv\<alpha> x' \<in> Sx} \<in> ?TW\<alpha>"
                            using continuous_map_preimage_open[OF hcont_hinv_W\<alpha> hSx_in_S1T] .
                          have hSx_preim_sub: "{x' \<in> W \<alpha>. ?hinv\<alpha> x' \<in> Sx} \<subseteq> ?pre"
                          proof (intro subsetI)
                            fix y assume hy: "y \<in> {x' \<in> W \<alpha>. ?hinv\<alpha> x' \<in> Sx}"
                            hence hyW: "y \<in> W \<alpha>" and hhinv_y_Sx: "?hinv\<alpha> y \<in> Sx"
                              by (by100 blast)+
                            have hinv_y_VVI: "inv_into Vsheet top1_R_to_S1 (?hinv\<alpha> y) \<in>
                                V \<inter> Vsheet \<inter> I_interval"
                              using hhinv_y_Sx unfolding Sx_def by (by100 blast)
                            define \<theta>y where "\<theta>y = inv_into Vsheet top1_R_to_S1 (?hinv\<alpha> y)"
                            have h\<theta>y_V: "\<theta>y \<in> V" and h\<theta>y_Vs: "\<theta>y \<in> Vsheet"
                                and h\<theta>y_I: "\<theta>q_fam \<alpha> < \<theta>y \<and> \<theta>y < \<theta>q_fam \<alpha> + 1"
                              using hinv_y_VVI unfolding \<theta>y_def I_interval_def by (by100 blast)+
                            have hbij_Vs: "bij_betw top1_R_to_S1 Vsheet Ux"
                              using hVs_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                            have hhinv_y_Ux: "?hinv\<alpha> y \<in> Ux"
                              using hhinv_y_Sx unfolding Sx_def by (by100 blast)
                            have hR_\<theta>y: "top1_R_to_S1 \<theta>y = ?hinv\<alpha> y"
                              unfolding \<theta>y_def
                              using f_inv_into_f[of "?hinv\<alpha> y" top1_R_to_S1 Vsheet]
                                hhinv_y_Ux hbij_Vs unfolding bij_betw_def by (by100 blast)
                            have "\<theta>q_fam \<alpha> < \<theta>y \<and> \<theta>y < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta>y = ?hinv\<alpha> y"
                              using h\<theta>y_I hR_\<theta>y by (by100 blast)
                            hence "angle_fam \<alpha> y = \<theta>y"
                            proof -
                              have hspec_y: "\<theta>q_fam \<alpha> < angle_fam \<alpha> y \<and> angle_fam \<alpha> y < \<theta>q_fam \<alpha> + 1 \<and>
                                  top1_R_to_S1 (angle_fam \<alpha> y) = ?hinv\<alpha> y"
                                using hangle_fam_spec[OF h\<alpha>n hyW] by (by100 blast)
                              have "top1_R_to_S1 \<theta>y = top1_R_to_S1 (angle_fam \<alpha> y)"
                                using hR_\<theta>y hspec_y by (by100 simp)
                              hence "sin (2 * pi * \<theta>y) = sin (2 * pi * angle_fam \<alpha> y)
                                  \<and> cos (2 * pi * \<theta>y) = cos (2 * pi * angle_fam \<alpha> y)"
                                unfolding top1_R_to_S1_def by (by100 auto)
                              then obtain k :: int where
                                  hk: "2*pi*\<theta>y = 2*pi*(angle_fam \<alpha> y) + 2*pi*of_int k"
                                using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                              hence "2*pi*(\<theta>y - angle_fam \<alpha> y) = 2*pi*of_int k"
                                by (simp add: algebra_simps)
                              hence "\<theta>y - angle_fam \<alpha> y = of_int k" using pi_gt_zero
                                by (by100 simp)
                              moreover have "\<bar>\<theta>y - angle_fam \<alpha> y\<bar> < 1"
                                using h\<theta>y_I hspec_y by (by100 linarith)
                              hence "k = 0" using \<open>\<theta>y - angle_fam \<alpha> y = of_int k\<close> by (by100 linarith)
                              ultimately show "angle_fam \<alpha> y = \<theta>y" by (by100 linarith)
                            qed
                            hence "angle_fam \<alpha> y \<in> V" using h\<theta>y_V by (by100 simp)
                            thus "y \<in> ?pre" using hyW by (by100 blast)
                          qed
                          have hx_in_preim: "x \<in> {x' \<in> W \<alpha>. ?hinv\<alpha> x' \<in> Sx}"
                            using hxW hhinv_x_Sx by (by100 blast)
                          show "\<exists>U\<in>?TW\<alpha>. x \<in> U \<and> U \<subseteq> ?pre"
                            apply (rule bexI[of _ "{x' \<in> W \<alpha>. ?hinv\<alpha> x' \<in> Sx}"])
                            using hx_in_preim hSx_preim_sub hSx_preim by (by100 blast)+
                        qed
                      qed
                    qed
                  qed
                  \<comment> \<open>Step B: The interpolation map is continuous on W(\<alpha>) \<times> I.\<close>
                  have hinterp_cont: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      (UNIV :: real set) top1_open_sets
                      (\<lambda>(x,t). (1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)"
                  proof -
                    have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
                    proof (rule set_eqI)
                      fix U :: "real set"
                      show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
                        using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def
                        by (by100 simp)
                    qed
                    let ?TR = "order_topology_on_UNIV :: real set set"
                    have hTR: "is_topology_on (UNIV::real set) ?TR"
                      by (rule order_topology_on_UNIV_is_topology_on)
                    have hItop_eq: "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
                      unfolding top1_unit_interval_topology_def top1_unit_interval_def
                      by (by100 simp)
                    have hangle_pi1: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR (angle_fam \<alpha> \<circ> pi1)"
                    proof -
                      have hpi1_cont: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) (W \<alpha>) ?TW\<alpha> pi1"
                        by (rule top1_continuous_pi1[OF hTW\<alpha> hTI])
                      have "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) top1_open_sets
                          (angle_fam \<alpha> \<circ> pi1)"
                        by (rule top1_continuous_map_on_comp[OF hpi1_cont hangle_cont])
                      thus ?thesis unfolding hTR_eq .
                    qed
                    have hpi2_R: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR pi2"
                    proof -
                      have hpi2_I: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) I_set I_top pi2"
                        by (rule top1_continuous_pi2[OF hTW\<alpha> hTI])
                      have h1: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) I_set
                          (subspace_topology UNIV top1_open_sets I_set) pi2"
                        using hpi2_I unfolding hItop_eq .
                      have h2: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set)
                          (subspace_topology UNIV top1_open_sets UNIV) pi2"
                        using top1_continuous_map_on_codomain_enlarge[OF h1]
                        by (by100 simp)
                      have h3: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) top1_open_sets pi2"
                        using h2 unfolding subspace_topology_UNIV_self .
                      thus ?thesis unfolding hTR_eq .
                    qed
                    have hconst1: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR (\<lambda>_. 1::real)"
                      using top1_continuous_map_on_const[OF hTW\<alpha>I hTR UNIV_I]
                      by (by100 simp)
                    have hconst_\<theta>p: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR (\<lambda>_. \<theta>p_fam \<alpha>)"
                      using top1_continuous_map_on_const[OF hTW\<alpha>I hTR UNIV_I]
                      by (by100 simp)
                    have h1_minus_t: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR
                        (\<lambda>p. 1 - pi2 p)"
                      by (rule top1_continuous_diff_real[OF hTW\<alpha>I hconst1 hpi2_R])
                    have hterm1: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR
                        (\<lambda>p. (1 - pi2 p) * (angle_fam \<alpha> \<circ> pi1) p)"
                      by (rule top1_continuous_mul_real[OF hTW\<alpha>I h1_minus_t hangle_pi1])
                    have hterm2: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR
                        (\<lambda>p. pi2 p * \<theta>p_fam \<alpha>)"
                      by (rule top1_continuous_mul_real[OF hTW\<alpha>I hpi2_R hconst_\<theta>p])
                    have hsum_OT: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) ?TR
                        (\<lambda>p. (1 - pi2 p) * (angle_fam \<alpha> \<circ> pi1) p + pi2 p * \<theta>p_fam \<alpha>)"
                      by (rule top1_continuous_add_real[OF hTW\<alpha>I hterm1 hterm2])
                    have hsum_OS: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) (UNIV::real set) top1_open_sets
                        (\<lambda>p. (1 - pi2 p) * (angle_fam \<alpha> \<circ> pi1) p + pi2 p * \<theta>p_fam \<alpha>)"
                      using hsum_OT unfolding hTR_eq .
                    have hfun_eq: "\<forall>p \<in> W \<alpha> \<times> I_set.
                        (1 - pi2 p) * (angle_fam \<alpha> \<circ> pi1) p + pi2 p * \<theta>p_fam \<alpha> =
                        (case p of (x,t) \<Rightarrow> (1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)"
                    proof (intro ballI)
                      fix p assume "p \<in> W \<alpha> \<times> I_set"
                      obtain x t where hp: "p = (x, t)" by (cases p)
                      show "(1 - pi2 p) * (angle_fam \<alpha> \<circ> pi1) p + pi2 p * \<theta>p_fam \<alpha> =
                          (case p of (x,t) \<Rightarrow> (1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)"
                        unfolding hp pi1_def pi2_def by (by100 simp)
                    qed
                    show ?thesis
                      using iffD1[OF top1_continuous_map_on_cong[OF hfun_eq]] hsum_OS
                      by (by100 blast)
                  qed
                  \<comment> \<open>Step C: Compose with R_to_S1.\<close>
                  have hR_S1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
                      top1_S1 top1_S1_topology top1_R_to_S1"
                    by (rule top1_covering_map_on_continuous[OF Theorem_53_1])
                  have hRS1_comp: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      top1_S1 top1_S1_topology
                      (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))"
                  proof -
                    have hcomp: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) top1_S1 top1_S1_topology
                        (top1_R_to_S1 \<circ> (\<lambda>(x,t). (1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))"
                      by (rule top1_continuous_map_on_comp[OF hinterp_cont hR_S1])
                    have heq: "\<forall>xt\<in>W \<alpha> \<times> I_set.
                        (top1_R_to_S1 \<circ> (\<lambda>(x,t). (1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)) xt =
                        (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)) xt"
                      by (by100 auto)
                    show ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq]] hcomp by (by100 blast)
                  qed
                  \<comment> \<open>Step D: Compose with h_fam \<alpha>.\<close>
                  have hcont_h\<alpha>: "top1_continuous_map_on top1_S1 top1_S1_topology
                      ?C\<alpha> ?TC\<alpha> (h_fam \<alpha>)"
                    using hh\<alpha> unfolding top1_homeomorphism_on_def by (by100 blast)
                  have hfull_comp: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      ?C\<alpha> ?TC\<alpha>
                      (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)))"
                  proof -
                    have hcomp: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                        (product_topology_on ?TW\<alpha> ?TI) ?C\<alpha> ?TC\<alpha>
                        (h_fam \<alpha> \<circ> (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)))"
                      by (rule top1_continuous_map_on_comp[OF hRS1_comp hcont_h\<alpha>])
                    have heq: "\<forall>xt\<in>W \<alpha> \<times> I_set.
                        (h_fam \<alpha> \<circ> (\<lambda>(x,t). top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt =
                        (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt"
                      by (by100 auto)
                    show ?thesis using iffD1[OF top1_continuous_map_on_cong[OF heq]] hcomp by (by100 blast)
                  qed
                  \<comment> \<open>Step E: Show H_V agrees with the composition on W(\<alpha>) \<times> I.\<close>
                  have hH_V_eq_\<alpha>: "\<forall>xt\<in>W \<alpha> \<times> I_set. H_V xt =
                      (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt"
                  proof (intro ballI)
                    fix xt assume hxt: "xt \<in> W \<alpha> \<times> I_set"
                    obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> W \<alpha>" and ht: "t \<in> I_set"
                      using hxt by (by100 blast)
                    show "H_V xt = (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt"
                    proof (cases "x \<in> ?Cn")
                      case True
                      \<comment> \<open>x \<in> C(n-1) \<inter> W(\<alpha>), so x = p.\<close>
                      have hxC\<alpha>: "x \<in> ?C\<alpha>" using hx unfolding W_def by (by100 blast)
                      have "\<alpha> \<noteq> n - 1" using h\<alpha> by (by100 simp)
                      hence "?C\<alpha> \<inter> ?Cn = {p}" using hC_inter h\<alpha>n hn1_in by (by100 blast)
                      hence hxp: "x = p" using hxC\<alpha> True by (by100 blast)
                      have "H_V xt = x" unfolding hxt_eq H_V_def using True by (by100 simp)
                      hence lhs: "H_V xt = p" using hxp by (by100 simp)
                      have hangle_p: "angle_fam \<alpha> p = \<theta>p_fam \<alpha>"
                      proof -
                        have hspec: "\<theta>q_fam \<alpha> < \<theta>p_fam \<alpha> \<and> \<theta>p_fam \<alpha> < \<theta>q_fam \<alpha> + 1 \<and>
                            top1_R_to_S1 (\<theta>p_fam \<alpha>) = ?hinv\<alpha> p"
                          using h\<theta>p_range h\<theta>p_eq by (by100 blast)
                        have hex1: "\<exists>!\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv\<alpha> p"
                        proof (rule ex_ex1I)
                          show "\<exists>\<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv\<alpha> p"
                            using hspec by (by100 blast)
                        next
                          fix a b
                          assume ha: "\<theta>q_fam \<alpha> < a \<and> a < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 a = ?hinv\<alpha> p"
                          assume hb: "\<theta>q_fam \<alpha> < b \<and> b < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 b = ?hinv\<alpha> p"
                          hence "top1_R_to_S1 a = top1_R_to_S1 b" using ha by (by100 simp)
                          hence "cos (2*pi*a) = cos (2*pi*b) \<and> sin (2*pi*a) = sin (2*pi*b)"
                            unfolding top1_R_to_S1_def by (by100 simp)
                          hence "sin (2*pi*a) = sin (2*pi*b) \<and> cos (2*pi*a) = cos (2*pi*b)"
                            by (by100 blast)
                          then obtain j :: int where hj: "2*pi*a = 2*pi*b + 2*pi*of_int j"
                            using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                          have "2*pi*a - 2*pi*b = 2*pi*of_int j" using hj by (by100 linarith)
                          hence hd: "2*pi*(a - b) = 2*pi*of_int j" by (simp only: right_diff_distrib)
                          have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                          hence "2*pi \<noteq> 0" by (by100 linarith)
                          hence "a - b = of_int j" using hd by (by100 simp)
                          moreover have "a - b > -1 \<and> a - b < 1" using ha hb by (by100 linarith)
                          ultimately have "of_int j > (-1::real) \<and> of_int j < (1::real)" by (by100 linarith)
                          hence "j = 0" by (by100 linarith)
                          thus "a = b" using \<open>a - b = of_int j\<close> by (by100 simp)
                        qed
                        have hthe: "(THE \<theta>. \<theta>q_fam \<alpha> < \<theta> \<and> \<theta> < \<theta>q_fam \<alpha> + 1 \<and> top1_R_to_S1 \<theta> = ?hinv\<alpha> p) = \<theta>p_fam \<alpha>"
                          by (rule the1_equality[OF hex1 hspec])
                        show ?thesis unfolding angle_fam_def using hthe by (by100 simp)
                      qed
                      have rhs: "(\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt = p"
                      proof -
                        have "(1 - t) * angle_fam \<alpha> p + t * \<theta>p_fam \<alpha> = (1 - t) * \<theta>p_fam \<alpha> + t * \<theta>p_fam \<alpha>"
                          using hangle_p by (by100 simp)
                        also have "\<dots> = \<theta>p_fam \<alpha>" by (simp add: algebra_simps)
                        finally have hinterp_p: "(1 - t) * angle_fam \<alpha> p + t * \<theta>p_fam \<alpha> = \<theta>p_fam \<alpha>" .
                        have "h_fam \<alpha> (top1_R_to_S1 (\<theta>p_fam \<alpha>)) = h_fam \<alpha> (?hinv\<alpha> p)"
                          using h\<theta>p_eq by (by100 simp)
                        also have "\<dots> = p" using bij_betw_inv_into_right[OF hbij\<alpha> hp_in\<alpha>] .
                        finally have hh_p: "h_fam \<alpha> (top1_R_to_S1 (\<theta>p_fam \<alpha>)) = p" .
                        show ?thesis unfolding hxt_eq using hxp hinterp_p hh_p by (by100 simp)
                      qed
                      show ?thesis using lhs rhs by (by100 simp)
                    next
                      case False
                      \<comment> \<open>x \<notin> C(n-1), x \<in> W(\<alpha>), so SOME gives back \<alpha>.\<close>
                      obtain \<alpha>' where h\<alpha>': "\<alpha>' \<in> {..<(n-1)}" and hx\<alpha>': "x \<in> W \<alpha>'"
                          and hH_eq: "H_V (x, t) = h_fam \<alpha>' (top1_R_to_S1 ((1 - t) * angle_fam \<alpha>' x + t * \<theta>p_fam \<alpha>'))"
                        using hH_V_W[OF False h\<alpha> hx] by (by100 blast)
                      \<comment> \<open>Since x \<notin> C(n-1) and x \<in> W(\<alpha>) \<inter> W(\<alpha>'), we must have \<alpha>' = \<alpha>.
                         Proof: W(\<alpha>) \<inter> W(\<alpha>') \<subseteq> C(\<alpha>) \<inter> C(\<alpha>').
                         If \<alpha>' \<noteq> \<alpha>, C(\<alpha>) \<inter> C(\<alpha>') = {p}, so x = p \<in> C(n-1), contradiction.\<close>
                      have h\<alpha>'_eq: "\<alpha>' = \<alpha>"
                      proof (rule ccontr)
                        assume hne: "\<alpha>' \<noteq> \<alpha>"
                        have h\<alpha>'n: "\<alpha>' \<in> {..<n}" using h\<alpha>' hn2 by (by100 simp)
                        have "C \<alpha> \<inter> C \<alpha>' = {p}" using hC_inter h\<alpha>n h\<alpha>'n hne by (by100 blast)
                        moreover have "x \<in> C \<alpha>" using hx unfolding W_def by (by100 blast)
                        moreover have "x \<in> C \<alpha>'" using hx\<alpha>' unfolding W_def by (by100 blast)
                        ultimately have "x = p" by (by100 blast)
                        hence "x \<in> ?Cn" using hp_Cn by (by100 blast)
                        thus False using False by (by100 blast)
                      qed
                      show ?thesis unfolding hxt_eq using hH_eq h\<alpha>'_eq by (by100 simp)
                    qed
                  qed
                  \<comment> \<open>Step F: Transfer continuity through to V_def.\<close>
                  \<comment> \<open>Image lies in W(\<alpha>).\<close>
                  have himg_W\<alpha>: "(\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) ` (W \<alpha> \<times> I_set) \<subseteq> W \<alpha>"
                  proof (intro image_subsetI)
                    fix xt assume hxt: "xt \<in> W \<alpha> \<times> I_set"
                    obtain x t where hxt_eq: "xt = (x, t)" and hx: "x \<in> W \<alpha>" and ht: "t \<in> I_set"
                      using hxt by (by100 blast)
                    have h_angle_spec: "\<theta>q_fam \<alpha> < angle_fam \<alpha> x \<and> angle_fam \<alpha> x < \<theta>q_fam \<alpha> + 1"
                      using hangle_fam_spec[OF h\<alpha>n hx] by (by100 blast)
                    have ht_range: "0 \<le> t \<and> t \<le> 1"
                      using ht unfolding top1_unit_interval_def by (by100 simp)
                    let ?\<theta>_interp = "(1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>"
                    have hconv: "\<theta>q_fam \<alpha> < ?\<theta>_interp \<and> ?\<theta>_interp < \<theta>q_fam \<alpha> + 1"
                    proof (intro conjI)
                      show "\<theta>q_fam \<alpha> < ?\<theta>_interp"
                      proof (cases "t = 1")
                        case True thus ?thesis using h\<theta>p_range by (by100 simp)
                      next
                        case False
                        hence h1t_pos: "(1-t) > 0" using ht_range by (by100 linarith)
                        have "(1-t) * \<theta>q_fam \<alpha> < (1-t) * angle_fam \<alpha> x"
                          using mult_strict_left_mono[of "\<theta>q_fam \<alpha>" "angle_fam \<alpha> x" "1-t"]
                            h_angle_spec h1t_pos by (by100 linarith)
                        moreover have "t * \<theta>q_fam \<alpha> \<le> t * \<theta>p_fam \<alpha>"
                          using mult_left_mono[of "\<theta>q_fam \<alpha>" "\<theta>p_fam \<alpha>" t] h\<theta>p_range ht_range by (by100 linarith)
                        ultimately have "(1-t)*\<theta>q_fam \<alpha> + t*\<theta>q_fam \<alpha> < (1-t)*angle_fam \<alpha> x + t*\<theta>p_fam \<alpha>"
                          by (by100 linarith)
                        moreover have "(1-t)*\<theta>q_fam \<alpha> + t*\<theta>q_fam \<alpha> = \<theta>q_fam \<alpha>" by (simp add: algebra_simps)
                        ultimately show ?thesis by (by100 linarith)
                      qed
                    next
                      show "?\<theta>_interp < \<theta>q_fam \<alpha> + 1"
                      proof (cases "t = 0")
                        case True thus ?thesis using h_angle_spec by (by100 simp)
                      next
                        case False hence "t > 0" using ht_range by (by100 linarith)
                        have "t*(\<theta>p_fam \<alpha> - (\<theta>q_fam \<alpha>+1)) < 0" using h\<theta>p_range \<open>t > 0\<close> by (simp add: mult_pos_neg)
                        moreover have "(1-t)*(angle_fam \<alpha> x - (\<theta>q_fam \<alpha>+1)) \<le> 0" using h_angle_spec ht_range
                          by (intro mult_nonneg_nonpos) linarith+
                        ultimately have "(1-t)*angle_fam \<alpha> x + t*\<theta>p_fam \<alpha> < (1-t)*(\<theta>q_fam \<alpha>+1) + t*(\<theta>q_fam \<alpha>+1)"
                          by (simp add: algebra_simps)
                        moreover have "(1-t)*(\<theta>q_fam \<alpha>+1) + t*(\<theta>q_fam \<alpha>+1) = \<theta>q_fam \<alpha> + 1" by (simp add: algebra_simps)
                        ultimately show ?thesis by (by100 linarith)
                      qed
                    qed
                    have hinterp_S1: "top1_R_to_S1 ?\<theta>_interp \<in> top1_S1"
                      unfolding top1_R_to_S1_def top1_S1_def by (by100 simp)
                    have hne_q': "top1_R_to_S1 ?\<theta>_interp \<noteq> ?hinv\<alpha> (q \<alpha>)"
                    proof
                      assume heq: "top1_R_to_S1 ?\<theta>_interp = ?hinv\<alpha> (q \<alpha>)"
                      hence "top1_R_to_S1 ?\<theta>_interp = top1_R_to_S1 (\<theta>q_fam \<alpha>)" using h\<theta>q_eq by (by100 simp)
                      hence "cos(2*pi*?\<theta>_interp) = cos(2*pi*\<theta>q_fam \<alpha>) \<and>
                             sin(2*pi*?\<theta>_interp) = sin(2*pi*\<theta>q_fam \<alpha>)"
                        unfolding top1_R_to_S1_def by (by100 simp)
                      hence "sin(2*pi*?\<theta>_interp) = sin(2*pi*\<theta>q_fam \<alpha>) \<and>
                             cos(2*pi*?\<theta>_interp) = cos(2*pi*\<theta>q_fam \<alpha>)"
                        by (by100 blast)
                      then obtain j::int where hj: "2*pi*?\<theta>_interp = 2*pi*\<theta>q_fam \<alpha> + 2*pi*of_int j"
                        using iffD1[OF sin_cos_eq_iff] by (by100 blast)
                      have "2*pi*(?\<theta>_interp - \<theta>q_fam \<alpha>) = 2*pi*of_int j"
                        using hj by (simp only: right_diff_distrib)
                      moreover have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
                      hence "2*pi \<noteq> 0" by (by100 linarith)
                      ultimately have "?\<theta>_interp - \<theta>q_fam \<alpha> = of_int j" by (by100 simp)
                      moreover have "?\<theta>_interp - \<theta>q_fam \<alpha> > 0 \<and> ?\<theta>_interp - \<theta>q_fam \<alpha> < 1"
                        using hconv by (by100 linarith)
                      ultimately have "of_int j > (0::real) \<and> of_int j < (1::real)" by (by100 linarith)
                      hence "j > 0 \<and> j < 1" by (by100 linarith)
                      thus False by (by100 linarith)
                    qed
                    have hresult_C: "h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp) \<in> ?C\<alpha>"
                      using hbij\<alpha> hinterp_S1 unfolding bij_betw_def by (by100 blast)
                    have hresult_neq_q: "h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp) \<noteq> q \<alpha>"
                    proof
                      assume "h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp) = q \<alpha>"
                      have "inv_into top1_S1 (h_fam \<alpha>) (h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp))
                          = inv_into top1_S1 (h_fam \<alpha>) (q \<alpha>)"
                        using \<open>h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp) = q \<alpha>\<close> by (by100 simp)
                      moreover have "inv_into top1_S1 (h_fam \<alpha>) (h_fam \<alpha> (top1_R_to_S1 ?\<theta>_interp))
                          = top1_R_to_S1 ?\<theta>_interp"
                        using bij_betw_inv_into_left[OF hbij\<alpha> hinterp_S1] .
                      ultimately have "top1_R_to_S1 ?\<theta>_interp = ?hinv\<alpha> (q \<alpha>)"
                        by (by100 simp)
                      thus False using hne_q' by (by100 blast)
                    qed
                    show "(\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>))) xt \<in> W \<alpha>"
                      unfolding hxt_eq W_def using hresult_C hresult_neq_q by (by100 simp)
                  qed
                  \<comment> \<open>Shrink codomain from C(\<alpha>) to W(\<alpha>), then enlarge to V_def.\<close>
                  have hfull_comp_W\<alpha>: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      (W \<alpha>) (subspace_topology ?C\<alpha> ?TC\<alpha> (W \<alpha>))
                      (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)))"
                    by (rule top1_continuous_map_on_codomain_shrink[OF hfull_comp himg_W\<alpha> hW\<alpha>_sub_C])
                  have hW\<alpha>_subspace_eq: "subspace_topology ?C\<alpha> ?TC\<alpha> (W \<alpha>) = ?TW\<alpha>"
                    by (rule subspace_topology_trans[OF hW\<alpha>_sub_C])
                  have hfull_comp_W\<alpha>': "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      (W \<alpha>) ?TW\<alpha>
                      (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)))"
                    using hfull_comp_W\<alpha> hW\<alpha>_subspace_eq by (by100 simp)
                  have hfull_comp_V: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI)
                      V_def ?TV
                      (\<lambda>(x,t). h_fam \<alpha> (top1_R_to_S1 ((1 - t) * angle_fam \<alpha> x + t * \<theta>p_fam \<alpha>)))"
                    by (rule top1_continuous_map_on_codomain_enlarge[OF hfull_comp_W\<alpha>' hW\<alpha>_sub_Vd hV_sub])
                  have "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on ?TW\<alpha> ?TI) V_def ?TV H_V"
                    using iffD2[OF top1_continuous_map_on_cong[OF hH_V_eq_\<alpha>] hfull_comp_V] .
                  thus "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (product_topology_on (subspace_topology X TX (W \<alpha>)) ?TI)
                      V_def ?TV H_V" .
                qed
                \<comment> \<open>Step 8b: Combine using Theorem_18_1(2) (closed preimage characterization).
                   Each W(\<alpha>) closed in ?Ws. Each W(\<alpha>)\<times>I closed in ?Ws\<times>I.
                   Preimage of closed B = \<Union>\<alpha>. {xt \<in> W(\<alpha>)\<times>I. H_V xt \<in> B}.
                   Each piece closed in W(\<alpha>)\<times>I by continuity, hence closed in ?Ws\<times>I.
                   Finite union of closed = closed.\<close>
                \<comment> \<open>Each W(\<alpha>) is closed in ?Ws.\<close>
                have hW_closed_Ws: "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on ?Ws ?TWs (W \<alpha>)"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have hW_cl_V: "closedin_on V_def ?TV (W \<alpha>)"
                  proof -
                    have h\<alpha>n: "\<alpha> \<in> {..<n}" using h\<alpha> hn2 by (by100 simp)
                    have hC\<alpha>_closed_X: "closedin_on X TX (C \<alpha>)"
                    proof -
                      have hC\<alpha>_sub_X: "C \<alpha> \<subseteq> X" using hC_props h\<alpha>n by (by100 blast)
                      have hall: "\<forall>\<beta>\<in>{..<n}. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                      proof (intro ballI)
                        fix \<beta> assume h\<beta>: "\<beta> \<in> {..<n}"
                        show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> C \<alpha>)"
                        proof (cases "\<beta> = \<alpha>")
                          case True
                          hence "C \<beta> \<inter> C \<alpha> = C \<alpha>" by (by100 simp)
                          moreover have "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha>)"
                          proof (rule closedin_intro)
                            show "C \<alpha> \<subseteq> C \<alpha>" by (by100 blast)
                            show "C \<alpha> - C \<alpha> \<in> subspace_topology X TX (C \<alpha>)"
                            proof -
                              have "{} \<in> subspace_topology X TX (C \<alpha>)"
                                using subspace_topology_is_topology_on[OF hTX hC\<alpha>_sub_X]
                                unfolding is_topology_on_def by (by100 blast)
                              thus ?thesis by (by100 simp)
                            qed
                          qed
                          ultimately show ?thesis using True by (by100 simp)
                        next
                          case False
                          hence "C \<beta> \<inter> C \<alpha> = {p}" using hC_inter h\<beta> h\<alpha>n by (by100 blast)
                          moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) {p}"
                          proof -
                            have "C \<beta> \<subseteq> X" using hC_props h\<beta> by (by100 blast)
                            have "p \<in> C \<beta>" using hC_props h\<beta> by (by100 blast)
                            have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                              by (rule hausdorff_subspace[OF hHausdorff \<open>C \<beta> \<subseteq> X\<close>])
                            thus ?thesis using \<open>p \<in> C \<beta>\<close>
                              by (rule singleton_closed_in_hausdorff)
                          qed
                          ultimately show ?thesis by (by100 simp)
                        qed
                      qed
                      show ?thesis using iffD2[OF hC_weak[rule_format, OF hC\<alpha>_sub_X] hall] .
                    qed
                    have "W \<alpha> = C \<alpha> \<inter> V_def"
                    proof -
                      have "W \<alpha> \<subseteq> V_def" unfolding V_def_def using h\<alpha> by (by100 blast)
                      moreover have "W \<alpha> \<subseteq> C \<alpha>" unfolding W_def by (by100 blast)
                      moreover have "\<forall>x. x \<in> C \<alpha> \<and> x \<in> V_def \<longrightarrow> x \<in> W \<alpha>"
                      proof (intro allI impI)
                        fix x assume hx: "x \<in> C \<alpha> \<and> x \<in> V_def"
                        show "x \<in> W \<alpha>"
                        proof (rule ccontr)
                          assume "x \<notin> W \<alpha>"
                          hence "x = q \<alpha>" using hx unfolding W_def by (by100 blast)
                          moreover have "q \<alpha> \<notin> V_def"
                          proof -
                            have "q \<alpha> \<noteq> p" using hq h\<alpha>n by (by100 blast)
                            have "q \<alpha> \<in> C \<alpha>" using hq h\<alpha>n by (by100 blast)
                            have "q \<alpha> \<notin> W \<alpha>" unfolding W_def by (by100 blast)
                            moreover have "\<forall>\<beta>\<in>{..<(n-1)}. \<beta> \<noteq> \<alpha> \<longrightarrow> q \<alpha> \<notin> W \<beta>"
                            proof (intro ballI impI)
                              fix \<beta> assume h\<beta>': "\<beta> \<in> {..<(n-1)}" and hne: "\<beta> \<noteq> \<alpha>"
                              have h\<beta>n': "\<beta> \<in> {..<n}" using h\<beta>' hn2 by (by100 simp)
                              have "C \<alpha> \<inter> C \<beta> = {p}" using hC_inter h\<alpha>n h\<beta>n' hne by (by100 blast)
                              hence "q \<alpha> \<notin> C \<beta>" using \<open>q \<alpha> \<in> C \<alpha>\<close> \<open>q \<alpha> \<noteq> p\<close> by (by100 blast)
                              thus "q \<alpha> \<notin> W \<beta>" unfolding W_def by (by100 blast)
                            qed
                            moreover have "q \<alpha> \<notin> ?Cn"
                            proof -
                              have "\<alpha> \<noteq> n - 1" using h\<alpha> by (by100 simp)
                              hence "C \<alpha> \<inter> ?Cn = {p}" using hC_inter h\<alpha>n hn1_in by (by100 blast)
                              thus ?thesis using \<open>q \<alpha> \<in> C \<alpha>\<close> \<open>q \<alpha> \<noteq> p\<close> by (by100 blast)
                            qed
                            moreover have "q \<alpha> \<notin> (\<Union>\<beta>\<in>{..<(n-1)}. W \<beta>)"
                            proof
                              assume "q \<alpha> \<in> (\<Union>\<beta>\<in>{..<(n-1)}. W \<beta>)"
                              then obtain \<beta> where h\<beta>: "\<beta> \<in> {..<(n-1)}" and hq\<beta>: "q \<alpha> \<in> W \<beta>"
                                by (by100 blast)
                              show False
                              proof (cases "\<beta> = \<alpha>")
                                case True thus False using hq\<beta> \<open>q \<alpha> \<notin> W \<alpha>\<close> by (by100 blast)
                              next
                                case False
                                thus False using hq\<beta> calculation(2) h\<beta> by (by100 blast)
                              qed
                            qed
                            ultimately show ?thesis unfolding V_def_def by (by100 blast)
                          qed
                          ultimately show False using hx by (by100 blast)
                        qed
                      qed
                      ultimately show ?thesis by (by100 blast)
                    qed
                    hence "\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> V_def"
                      using hC\<alpha>_closed_X by (by100 blast)
                    thus ?thesis using iffD2[OF Theorem_17_2[OF hTX hV_sub]] by (by100 blast)
                  qed
                  have "closedin_on ?Ws ?TWs (W \<alpha>) \<longleftrightarrow>
                      (\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> ?Ws)"
                    by (rule Theorem_17_2[OF hTX hWs_sub_X])
                  moreover have "\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> ?Ws"
                  proof -
                    have "closedin_on V_def ?TV (W \<alpha>) \<longleftrightarrow>
                        (\<exists>Cl. closedin_on X TX Cl \<and> W \<alpha> = Cl \<inter> V_def)"
                      by (rule Theorem_17_2[OF hTX hV_sub])
                    then obtain Cl where hCl: "closedin_on X TX Cl" and hWeq: "W \<alpha> = Cl \<inter> V_def"
                      using hW_cl_V by (by100 blast)
                    have "W \<alpha> = Cl \<inter> ?Ws"
                    proof -
                      have "W \<alpha> \<subseteq> ?Ws" using h\<alpha> by (by100 blast)
                      moreover have "?Ws \<subseteq> V_def" using hWs_sub_Vd .
                      ultimately show ?thesis using hWeq by (by100 blast)
                    qed
                    thus ?thesis using hCl by (by100 blast)
                  qed
                  ultimately show "closedin_on ?Ws ?TWs (W \<alpha>)" by (by100 blast)
                qed
                \<comment> \<open>Each W(\<alpha>) \<times> I_set is closed in ?Ws \<times> I_set.\<close>
                have hWI_closed_WsI: "\<forall>\<alpha>\<in>{..<(n-1)}. closedin_on (?Ws \<times> I_set)
                    (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have hW_cl: "closedin_on ?Ws ?TWs (W \<alpha>)"
                    using hW_closed_Ws h\<alpha> by (by100 blast)
                  show "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                  proof (rule closedin_intro)
                    show "W \<alpha> \<times> I_set \<subseteq> ?Ws \<times> I_set" using h\<alpha> by (by100 blast)
                  next
                    have hdiff_eq: "?Ws \<times> I_set - W \<alpha> \<times> I_set = (?Ws - W \<alpha>) \<times> I_set" by (by100 blast)
                    have hWs_minus_open: "(?Ws - W \<alpha>) \<in> ?TWs"
                      using hW_cl unfolding closedin_on_def by (by100 blast)
                    have hI_open: "I_set \<in> ?TI"
                      using hTI unfolding is_topology_on_def by (by100 blast)
                    have "(?Ws - W \<alpha>) \<times> I_set \<in> product_topology_on ?TWs ?TI"
                      by (rule product_rect_open[OF hWs_minus_open hI_open])
                    thus "?Ws \<times> I_set - W \<alpha> \<times> I_set \<in> product_topology_on ?TWs ?TI"
                      using hdiff_eq by (by100 simp)
                  qed
                qed
                \<comment> \<open>Subspace topology on W(\<alpha>) \<times> I from ?Ws \<times> I = product on W(\<alpha>) \<times> I.\<close>
                have hW\<alpha>_subspace_eq: "\<forall>\<alpha>\<in>{..<(n-1)}.
                    product_topology_on (subspace_topology X TX (W \<alpha>)) ?TI
                    = subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have hW\<alpha>_sub_Ws: "W \<alpha> \<subseteq> ?Ws" using h\<alpha> by (by100 blast)
                  have h1: "subspace_topology ?Ws ?TWs (W \<alpha>) = subspace_topology X TX (W \<alpha>)"
                    by (rule subspace_topology_trans[OF hW\<alpha>_sub_Ws])
                  have h2: "subspace_topology I_set ?TI I_set = ?TI"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>?TI. U \<subseteq> I_set"
                    proof (intro ballI)
                      fix U assume "U \<in> ?TI"
                      thus "U \<subseteq> I_set"
                        unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                    qed
                  qed
                  have hT163: "product_topology_on (subspace_topology ?Ws ?TWs (W \<alpha>)) (subspace_topology I_set ?TI I_set)
                      = subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                    by (rule Theorem_16_3[OF hTWs hTI])
                  show "product_topology_on (subspace_topology X TX (W \<alpha>)) ?TI
                      = subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                    using hT163 h1 h2 by (simp only:)
                qed
                \<comment> \<open>Each H_V restricted to W(\<alpha>) \<times> I is continuous with subspace topology from ?Ws \<times> I.\<close>
                have hH_V_each_sub: "\<forall>\<alpha>\<in>{..<(n-1)}. top1_continuous_map_on (W \<alpha> \<times> I_set)
                    (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                    V_def ?TV H_V"
                proof (intro ballI)
                  fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                  have heq: "subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)
                      = product_topology_on (subspace_topology X TX (W \<alpha>)) ?TI"
                    using hW\<alpha>_subspace_eq h\<alpha> by (by100 blast)
                  show "top1_continuous_map_on (W \<alpha> \<times> I_set)
                      (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                      V_def ?TV H_V"
                    using hH_V_each h\<alpha> heq by (by100 simp)
                qed
                show ?thesis unfolding hTWsI_eq
                proof (rule iffD2[OF Theorem_18_1(2)[OF hTWsI hTV]])
                  show "(\<forall>x\<in>?Ws \<times> I_set. H_V x \<in> V_def) \<and>
                      (\<forall>B. closedin_on V_def ?TV B \<longrightarrow>
                        closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)
                          {x \<in> ?Ws \<times> I_set. H_V x \<in> B})"
                  proof (intro conjI allI impI)
                    show "\<forall>x\<in>?Ws \<times> I_set. H_V x \<in> V_def"
                      using hH_V_range hWs_sub_Vd by (by100 blast)
                  next
                    fix B assume hB: "closedin_on V_def ?TV B"
                    \<comment> \<open>Each piece preimage is closed in W(\<alpha>)\<times>I (subspace from ?Ws\<times>I).\<close>
                    have hpre_closed_each: "\<forall>\<alpha>\<in>{..<(n-1)}.
                        closedin_on (W \<alpha> \<times> I_set)
                          (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                          {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}"
                    proof (intro ballI)
                      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                      have hcont_sub: "top1_continuous_map_on (W \<alpha> \<times> I_set)
                          (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                          V_def ?TV H_V"
                        using hH_V_each_sub h\<alpha> by (by100 blast)
                      have hW\<alpha>_sub_Ws: "W \<alpha> \<subseteq> ?Ws" using h\<alpha> by (by100 blast)
                      have hTW\<alpha>I_sub: "is_topology_on (W \<alpha> \<times> I_set)
                          (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))"
                      proof (rule subspace_topology_is_topology_on[OF hTWsI])
                        show "W \<alpha> \<times> I_set \<subseteq> ?Ws \<times> I_set" using hW\<alpha>_sub_Ws by (by100 blast)
                      qed
                      show "closedin_on (W \<alpha> \<times> I_set)
                          (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                          {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}"
                        using iffD1[OF Theorem_18_1(2)[OF hTW\<alpha>I_sub hTV] hcont_sub] hB
                        by (by100 blast)
                    qed
                    \<comment> \<open>Each piece is closed in ?Ws\<times>I (closed in closed subspace \<Longrightarrow> closed in ambient).\<close>
                    have hpre_closed_WsI: "\<forall>\<alpha>\<in>{..<(n-1)}.
                        closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)
                          {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}"
                    proof (intro ballI)
                      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> {..<(n-1)}"
                      have hcl_piece: "closedin_on (W \<alpha> \<times> I_set)
                          (subspace_topology (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set))
                          {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}"
                        using hpre_closed_each h\<alpha> by (by100 blast)
                      have hWI_cl: "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (W \<alpha> \<times> I_set)"
                        using hWI_closed_WsI h\<alpha> by (by100 blast)
                      have hW\<alpha>I_sub: "W \<alpha> \<times> I_set \<subseteq> ?Ws \<times> I_set" using h\<alpha> by (by100 blast)
                      obtain Cl where hCl: "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) Cl"
                          and hSeq: "{xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B} = Cl \<inter> (W \<alpha> \<times> I_set)"
                        using iffD1[OF Theorem_17_2[OF hTWsI hW\<alpha>I_sub]] hcl_piece by (by100 blast)
                      have "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (Cl \<inter> (W \<alpha> \<times> I_set))"
                      proof -
                        have hinter_rule: "\<forall>F. F \<noteq> {} \<longrightarrow> (\<forall>A\<in>F. closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) A) \<longrightarrow>
                            closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (\<Inter>F)"
                          using conjunct1[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hTWsI]]]] .
                        have "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) (\<Inter>{Cl, W \<alpha> \<times> I_set})"
                        proof (rule mp[OF mp[OF spec[OF hinter_rule]]])
                          show "{Cl, W \<alpha> \<times> I_set} \<noteq> {}" by (by100 blast)
                          show "\<forall>A\<in>{Cl, W \<alpha> \<times> I_set}. closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) A"
                            using hCl hWI_cl by (by100 blast)
                        qed
                        moreover have "\<Inter>{Cl, W \<alpha> \<times> I_set} = Cl \<inter> (W \<alpha> \<times> I_set)" by (by100 blast)
                        ultimately show ?thesis by (by100 simp)
                      qed
                      thus "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)
                          {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}"
                        using hSeq by (by100 simp)
                    qed
                    \<comment> \<open>Finite union of closed = closed.\<close>
                    have hfin_img: "finite ((\<lambda>\<alpha>. {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}) ` {..<(n-1)})"
                      using finite_imageI[OF finite_lessThan] .
                    have hall_closed: "\<forall>S\<in>(\<lambda>\<alpha>. {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}) ` {..<(n-1)}.
                        closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI) S"
                      using hpre_closed_WsI by (by100 blast)
                    have hunion_closed: "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)
                        (\<Union>((\<lambda>\<alpha>. {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}) ` {..<(n-1)}))"
                      using conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hTWsI]]]]
                        hfin_img hall_closed by (by100 blast)
                    have hunion_eq: "(\<Union>((\<lambda>\<alpha>. {xt \<in> W \<alpha> \<times> I_set. H_V xt \<in> B}) ` {..<(n-1)}))
                        = {xt \<in> ?Ws \<times> I_set. H_V xt \<in> B}"
                      by (by100 blast)
                    show "closedin_on (?Ws \<times> I_set) (product_topology_on ?TWs ?TI)
                        {x \<in> ?Ws \<times> I_set. H_V x \<in> B}"
                      using hunion_closed hunion_eq by (by100 simp)
                  qed
                qed
              qed
              \<comment> \<open>Step 9: Apply pasting lemma.\<close>
              show ?thesis
                by (rule pasting_lemma_two_closed[OF hTVI hTV hCnI_closed hWsI_closed hcover hH_V_range hH_V_Cn hH_V_Ws])
            qed
            show ?thesis unfolding top1_deformation_retract_of_on_def
              using hCn_sub_Vd hH_V_cont hH_V_0 hH_V_1 hH_V_A by (by100 blast)
          qed
          have hTopV: "is_topology_on V_def (subspace_topology X TX V_def)"
            by (rule subspace_topology_is_topology_on[OF hTX]) (rule hV_sub)
          from Theorem_58_3[OF hdef_V hTopV hp_Cn]
          have "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier ?Cn (subspace_topology V_def (subspace_topology X TX V_def) ?Cn) p)
              (top1_fundamental_group_mul ?Cn (subspace_topology V_def (subspace_topology X TX V_def) ?Cn) p)
              (top1_fundamental_group_carrier V_def (subspace_topology X TX V_def) p)
              (top1_fundamental_group_mul V_def (subspace_topology X TX V_def) p)" .
          moreover have "subspace_topology V_def (subspace_topology X TX V_def) ?Cn = ?TCn"
          proof -
            have "?Cn \<subseteq> V_def" unfolding V_def_def by (by100 blast)
            thus ?thesis by (rule subspace_topology_trans)
          qed
          ultimately have h_iso_CV: "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier ?Cn ?TCn p)
              (top1_fundamental_group_mul ?Cn ?TCn p)
              (top1_fundamental_group_carrier V_def (subspace_topology X TX V_def) p)
              (top1_fundamental_group_mul V_def (subspace_topology X TX V_def) p)"
            by (by100 simp)
          show ?thesis
            by (rule top1_groups_isomorphic_on_sym[OF h_iso_CV
                top1_fundamental_group_is_group[OF
                  subspace_topology_is_topology_on[OF hTX hCn_sub] hp_Cn]
                top1_fundamental_group_is_group[OF hTopV hp_V]])
        qed
      qed
    qed
    \<comment> \<open>Step 7: \<pi>_1(U) is free on n-1 generators (via isomorphism with \<pi>_1(X')).\<close>
    let ?piU = "top1_fundamental_group_carrier U (subspace_topology X TX U) p"
    let ?mulU = "top1_fundamental_group_mul U (subspace_topology X TX U) p"
    let ?piV = "top1_fundamental_group_carrier V (subspace_topology X TX V) p"
    let ?mulV = "top1_fundamental_group_mul V (subspace_topology X TX V) p"
    \<comment> \<open>Step 8: Build the free product of \<pi>_1(U) and \<pi>_1(V).\<close>
    have hU_sub: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
    have hV_sub: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
    have hTopU: "is_topology_on U (subspace_topology X TX U)"
      by (rule subspace_topology_is_topology_on[OF hTX hU_sub])
    have hTopV: "is_topology_on V (subspace_topology X TX V)"
      by (rule subspace_topology_is_topology_on[OF hTX hV_sub])
    have hp_U: "p \<in> U" using hp_UV by (by100 blast)
    have hp_V: "p \<in> V" using hp_UV by (by100 blast)
    have hpiU_grp: "top1_is_group_on ?piU ?mulU
        (top1_fundamental_group_id U (subspace_topology X TX U) p)
        (top1_fundamental_group_invg U (subspace_topology X TX U) p)"
      by (rule top1_fundamental_group_is_group[OF hTopU hp_U])
    have hpiV_grp: "top1_is_group_on ?piV ?mulV
        (top1_fundamental_group_id V (subspace_topology X TX V) p)
        (top1_fundamental_group_invg V (subspace_topology X TX V) p)"
      by (rule top1_fundamental_group_is_group[OF hTopV hp_V])
    \<comment> \<open>Build the free product FP of \<pi>_1(U) and \<pi>_1(V) using Theorem 68.2.\<close>
    have hgroups_UV: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
        (if \<alpha> = 0 then ?piU else ?piV)
        (if \<alpha> = 0 then ?mulU else ?mulV)
        (if \<alpha> = 0 then top1_fundamental_group_id U (subspace_topology X TX U) p
                   else top1_fundamental_group_id V (subspace_topology X TX V) p)
        (if \<alpha> = 0 then top1_fundamental_group_invg U (subspace_topology X TX U) p
                   else top1_fundamental_group_invg V (subspace_topology X TX V) p)"
    proof (intro ballI)
      fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
      hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
      thus "top1_is_group_on (if \<alpha> = 0 then ?piU else ?piV)
          (if \<alpha> = 0 then ?mulU else ?mulV)
          (if \<alpha> = 0 then top1_fundamental_group_id U (subspace_topology X TX U) p
                     else top1_fundamental_group_id V (subspace_topology X TX V) p)
          (if \<alpha> = 0 then top1_fundamental_group_invg U (subspace_topology X TX U) p
                     else top1_fundamental_group_invg V (subspace_topology X TX V) p)"
      proof
        assume "\<alpha> = 0"
        thus ?thesis using hpiU_grp by (by100 simp)
      next
        assume "\<alpha> = 1"
        thus ?thesis using hpiV_grp by (by100 simp)
      qed
    qed
    obtain FP :: "(nat \<times> (real \<Rightarrow> 'a) set) list set"
        and mulFP eFP invgFP
        and \<iota>fam :: "nat \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (nat \<times> (real \<Rightarrow> 'a) set) list" where
        hFP: "top1_is_free_product_on FP mulFP eFP invgFP
            (\<lambda>i::nat. if i = 0 then ?piU else ?piV)
            (\<lambda>i. if i = 0 then ?mulU else ?mulV)
            \<iota>fam {0, 1}"
    proof -
      from Theorem_68_2_free_product_exists[OF hgroups_UV]
      show ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Step 9: Apply Corollary 70.3 (parameterized): \<pi>_1(X,p) \<cong> FP.\<close>
    have hSvK_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)
        FP mulFP"
      by (rule Corollary_70_3_simply_connected_intersection_param[OF
            hX_strict hU_open hV_open hUV_cover hUV_sc hU_pc hV_pc hp_UV hFP])
    \<comment> \<open>Step 10: \<pi>_1(U) \<cong> \<pi>_1(X') is free on n-1 generators.
       \<pi>_1(V) \<cong> \<pi>_1(C(n-1)) is free on 1 generator.
       We need to transfer the free group structures through the isomorphisms.\<close>
    \<comment> \<open>Step 10a: Get free group structures on \<pi>_1(U) and \<pi>_1(V) themselves.\<close>
    have hpiU_free: "\<exists>(GU::int set) mulU eU invgU (\<iota>U::nat \<Rightarrow> int).
        top1_is_free_group_full_on GU mulU eU invgU \<iota>U {..<(n-1)}
      \<and> top1_groups_isomorphic_on GU mulU ?piU ?mulU"
    proof -
      \<comment> \<open>Get group axioms for \<pi>_1(X').\<close>
      have hTX': "is_topology_on ?X' ?TX'"
        by (rule subspace_topology_is_topology_on[OF hTX hX'_sub])
      have hpiX'_grp: "top1_is_group_on
          (top1_fundamental_group_carrier ?X' ?TX' p)
          (top1_fundamental_group_mul ?X' ?TX' p)
          (top1_fundamental_group_id ?X' ?TX' p)
          (top1_fundamental_group_invg ?X' ?TX' p)"
        by (rule top1_fundamental_group_is_group[OF hTX' hp_X'])
      \<comment> \<open>Reverse hU_pi1: \<pi>_1(X') \<cong> \<pi>_1(U).\<close>
      have hX'_iso_U: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier ?X' ?TX' p)
          (top1_fundamental_group_mul ?X' ?TX' p) ?piU ?mulU"
        by (rule top1_groups_isomorphic_on_sym[OF hU_pi1 hpiU_grp hpiX'_grp])
      \<comment> \<open>Compose: G' \<cong> \<pi>_1(X') \<cong> \<pi>_1(U).\<close>
      have hG'_iso_U: "top1_groups_isomorphic_on G' mul' ?piU ?mulU"
        by (rule groups_isomorphic_trans_fwd[OF hG'_iso hX'_iso_U])
      thus ?thesis using hG'_free by (by100 blast)
    qed
    have hpiV_free: "\<exists>(GV::int set) mulV eV invgV (\<iota>V::nat \<Rightarrow> int).
        top1_is_free_group_full_on GV mulV eV invgV \<iota>V {0::nat}
      \<and> top1_groups_isomorphic_on GV mulV ?piV ?mulV"
    proof -
      \<comment> \<open>Get group axioms for \<pi>_1(C(n-1)).\<close>
      have hTCn': "is_topology_on ?Cn ?TCn"
        by (rule subspace_topology_is_topology_on[OF hTX hCn_sub])
      have hpiCn_grp: "top1_is_group_on
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p)
          (top1_fundamental_group_id ?Cn ?TCn p)
          (top1_fundamental_group_invg ?Cn ?TCn p)"
        by (rule top1_fundamental_group_is_group[OF hTCn' hp_Cn])
      \<comment> \<open>Reverse hV_pi1: \<pi>_1(C(n-1)) \<cong> \<pi>_1(V).\<close>
      have hCn_iso_V: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier ?Cn ?TCn p)
          (top1_fundamental_group_mul ?Cn ?TCn p) ?piV ?mulV"
        by (rule top1_groups_isomorphic_on_sym[OF hV_pi1 hpiV_grp hpiCn_grp])
      \<comment> \<open>Compose: G2 \<cong> \<pi>_1(C(n-1)) \<cong> \<pi>_1(V).\<close>
      have hG2_iso_V: "top1_groups_isomorphic_on G2 mul2 ?piV ?mulV"
        by (rule groups_isomorphic_trans_fwd[OF hG2_iso hCn_iso_V])
      thus ?thesis using hG2_free by (by100 blast)
    qed
    \<comment> \<open>Step 11: The free product of free groups is free (Theorem 69.2).
       free(n-1) * free(1) = free({..<n-1} \<union> {0}) where {0} is disjoint from {..<n-1}.
       Since we use shifted generators, the union gives {..<n}.\<close>
    \<comment> \<open>Step 11a: FP is isomorphic to \<pi>_1(X), and FP itself is a free product of
       groups isomorphic to free groups on n-1 and 1 generators.
       By composing these isomorphisms with the free product structure,
       we get that \<pi>_1(X) is isomorphic to a free group on n generators.\<close>
    have hfinal: "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
        top1_is_free_group_full_on G mul e invg \<iota> {..<n}
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX p)
          (top1_fundamental_group_mul X TX p)"
    proof -
      \<comment> \<open>Extract free group structures from hpiU_free and hpiV_free.\<close>
      obtain GU :: "int set" and mulU :: "int \<Rightarrow> int \<Rightarrow> int"
          and eU :: int and invgU :: "int \<Rightarrow> int" and \<iota>U :: "nat \<Rightarrow> int" where
          hGU_free: "top1_is_free_group_full_on GU mulU eU invgU \<iota>U {..<(n-1)}"
          and hGU_iso: "top1_groups_isomorphic_on GU mulU ?piU ?mulU"
        using hpiU_free by (by100 blast)
      obtain GV :: "int set" and mulV :: "int \<Rightarrow> int \<Rightarrow> int"
          and eV :: int and invgV :: "int \<Rightarrow> int" and \<iota>V :: "nat \<Rightarrow> int" where
          hGV_free: "top1_is_free_group_full_on GV mulV eV invgV \<iota>V {0::nat}"
          and hGV_iso: "top1_groups_isomorphic_on GV mulV ?piV ?mulV"
        using hpiV_free by (by100 blast)
      \<comment> \<open>Step A: Relabel GV from {0} to {n-1}.\<close>
      define \<iota>V' :: "nat \<Rightarrow> int" where "\<iota>V' = (\<lambda>k. \<iota>V 0)"
      have hGV_free': "top1_is_free_group_full_on GV mulV eV invgV \<iota>V' {n - 1}"
      proof -
        have hGV_grp: "top1_is_group_on GV mulV eV invgV"
          using hGV_free unfolding top1_is_free_group_full_on_def by (by100 blast)
        have h\<iota>V_in: "\<iota>V 0 \<in> GV"
          using hGV_free unfolding top1_is_free_group_full_on_def by (by100 force)
        have h\<iota>V'_in: "\<forall>s\<in>{n-1}. \<iota>V' s \<in> GV"
          using h\<iota>V_in unfolding \<iota>V'_def by (by100 simp)
        have h\<iota>V'_inj: "inj_on \<iota>V' {n-1}"
          by (by100 simp)
        have h\<iota>V'_image: "\<iota>V' ` {n-1} = \<iota>V ` {0::nat}"
          unfolding \<iota>V'_def by (by100 force)
        have hgen: "GV = top1_subgroup_generated_on GV mulV eV invgV (\<iota>V' ` {n-1})"
          using hGV_free h\<iota>V'_image unfolding top1_is_free_group_full_on_def by (by100 simp)
        have hred: "\<And>ws :: (nat \<times> bool) list. ws \<noteq> [] \<Longrightarrow>
            top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>V' s, b)) ws) \<Longrightarrow>
            (\<forall>i<length ws. fst (ws!i) \<in> {n-1}) \<Longrightarrow>
            top1_group_word_product mulV eV invgV (map (\<lambda>(s, b). (\<iota>V' s, b)) ws) \<noteq> eV"
        proof -
          fix ws :: "(nat \<times> bool) list"
          assume hws_ne: "ws \<noteq> []"
              and hws_red: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>V' s, b)) ws)"
              and hws_in: "\<forall>i<length ws. fst (ws!i) \<in> {n-1}"
          \<comment> \<open>Since all generators are n-1, and \<iota>V'(n-1) = \<iota>V(0), the mapped word is the same
             as mapping through \<iota>V with all indices replaced by 0.\<close>
          define ws0 :: "(nat \<times> bool) list" where "ws0 = map (\<lambda>(s,b). (0::nat, b)) ws"
          have hws0_ne: "ws0 \<noteq> []" using hws_ne unfolding ws0_def by (by100 simp)
          have hlen_eq: "length ws0 = length ws" unfolding ws0_def by (by100 simp)
          have hws0_in: "\<forall>i<length ws0. fst (ws0!i) \<in> {0::nat}"
          proof (intro allI impI)
            fix i assume hi: "i < length ws0"
            hence hi': "i < length ws" using hlen_eq by (by100 simp)
            obtain s b where hwsi: "ws ! i = (s, b)" by (cases "ws ! i")
            have "ws0 ! i = (0::nat, b)"
              unfolding ws0_def using hi' hwsi nth_map[of i ws "\<lambda>(s,b). (0::nat, b)"]
              by (by100 simp)
            thus "fst (ws0 ! i) \<in> {0::nat}" by (by100 simp)
          qed
          have hmap_eq: "map (\<lambda>(s, b). (\<iota>V' s, b)) ws = map (\<lambda>(s, b). (\<iota>V (0::nat), b)) ws"
            unfolding \<iota>V'_def using hws_in by (by100 auto)
          have hmap_eq2: "map (\<lambda>(s, b). (\<iota>V 0, b)) ws = map (\<lambda>(s, b). (\<iota>V s, b)) ws0"
            unfolding ws0_def by (by100 auto)
          have hmap_combined: "map (\<lambda>(s, b). (\<iota>V' s, b)) ws = map (\<lambda>(s, b). (\<iota>V s, b)) ws0"
            using hmap_eq hmap_eq2 by (by100 simp)
          have hws0_red: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>V s, b)) ws0)"
            using hws_red hmap_combined by (by100 simp)
          have hred_V: "top1_group_word_product mulV eV invgV
              (map (\<lambda>(s, b). (\<iota>V s, b)) ws0) \<noteq> eV"
            using hGV_free hws0_ne hws0_red hws0_in hlen_eq
            unfolding top1_is_free_group_full_on_def by (by100 blast)
          thus "top1_group_word_product mulV eV invgV (map (\<lambda>(s, b). (\<iota>V' s, b)) ws) \<noteq> eV"
            using hmap_combined by (by100 simp)
        qed
        show ?thesis unfolding top1_is_free_group_full_on_def
          using hGV_grp h\<iota>V'_in h\<iota>V'_inj hgen hred by (by100 blast)
      qed
      \<comment> \<open>Step B: The generator sets are disjoint: {..<(n-1)} \<inter> {n-1} = {}.\<close>
      have hS_disj: "{..<(n-1)} \<inter> {n - 1 :: nat} = {}"
        using hn2 by (by100 auto)
      \<comment> \<open>Step C: Apply Theorem 69.2 to get a free product that is free on {..<n}.\<close>
      from Theorem_69_2[OF hGU_free hGV_free' hS_disj]
      obtain FPZ :: "(nat \<times> int) list set" and mulFPZ eFPZ invgFPZ
          and \<iota>fam_Z :: "nat \<Rightarrow> int \<Rightarrow> (nat \<times> int) list"
          and \<iota>Z :: "nat \<Rightarrow> (nat \<times> int) list" where
          hFPZ: "top1_is_free_product_on FPZ mulFPZ eFPZ invgFPZ
              (\<lambda>i::nat. if i = 0 then GU else GV)
              (\<lambda>i. if i = 0 then mulU else mulV)
              \<iota>fam_Z {0, 1}"
          and hFPZ_free: "top1_is_free_group_full_on FPZ mulFPZ eFPZ invgFPZ \<iota>Z ({..<(n-1)} \<union> {n-1})"
          and hFPZ_comp1: "\<forall>s\<in>{..<(n-1)}. \<iota>Z s = \<iota>fam_Z 0 (\<iota>U s)"
          and hFPZ_comp2: "\<forall>s\<in>{n-1}. \<iota>Z s = \<iota>fam_Z 1 (\<iota>V' s)"
        by (by100 blast)
      \<comment> \<open>{..<(n-1)} \<union> {n-1} = {..<n}\<close>
      have hS_union: "{..<(n-1)} \<union> {n - 1 :: nat} = {..<n}"
        using hn2 by (by100 auto)
      have hFPZ_free_n: "top1_is_free_group_full_on FPZ mulFPZ eFPZ invgFPZ \<iota>Z {..<n}"
        using hFPZ_free hS_union by (by100 simp)
      \<comment> \<open>Step D: Build isomorphism FPZ \<cong> FP using extension property.
         We have GU \<cong> \<pi>U and GV \<cong> \<pi>V, and both FPZ and FP are free products
         of (GU, GV) and (\<pi>U, \<pi>V) respectively. We use the isomorphisms to
         create homomorphisms from the factors of FPZ into FP, then extend.\<close>
      have hFPZ_grp: "top1_is_group_on FPZ mulFPZ eFPZ invgFPZ"
        using hFPZ unfolding top1_is_free_product_on_def by (by100 blast)
      have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      have hGU_grp: "top1_is_group_on GU mulU eU invgU"
        using hGU_free unfolding top1_is_free_group_full_on_def by (by100 blast)
      have hGV_grp: "top1_is_group_on GV mulV eV invgV"
        using hGV_free unfolding top1_is_free_group_full_on_def by (by100 blast)
      \<comment> \<open>Get isomorphism witnesses fU: GU \<rightarrow> \<pi>U and fV: GV \<rightarrow> \<pi>V.\<close>
      obtain fU where hfU_hom: "top1_group_hom_on GU mulU ?piU ?mulU fU"
          and hfU_bij: "bij_betw fU GU ?piU"
        using hGU_iso unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
        by (by100 blast)
      obtain fV where hfV_hom: "top1_group_hom_on GV mulV ?piV ?mulV fV"
          and hfV_bij: "bij_betw fV GV ?piV"
        using hGV_iso unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
        by (by100 blast)
      \<comment> \<open>Build homomorphisms from factors of FPZ into FP:
         h0 = \<iota>fam(0) \<circ> fU : GU \<rightarrow> FP  and  h1 = \<iota>fam(1) \<circ> fV : GV \<rightarrow> FP.\<close>
      have h\<iota>fam_in: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV). \<iota>fam \<alpha> x \<in> FP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      have h\<iota>fam_hom: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV).
          \<forall>y\<in>(if \<alpha> = 0 then ?piU else ?piV).
          \<iota>fam \<alpha> ((if \<alpha> = 0 then ?mulU else ?mulV) x y) = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      \<comment> \<open>h0 = \<iota>fam 0 \<circ> fU is a group hom GU \<rightarrow> FP.\<close>
      have h0_hom: "top1_group_hom_on GU mulU FP mulFP (\<lambda>x. \<iota>fam 0 (fU x))"
        unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix x assume hx: "x \<in> GU"
        have "fU x \<in> ?piU" using hfU_bij hx unfolding bij_betw_def by (by100 blast)
        thus "\<iota>fam 0 (fU x) \<in> FP" using h\<iota>fam_in by (by100 auto)
      next
        fix x y assume hx: "x \<in> GU" and hy: "y \<in> GU"
        have hfUx: "fU x \<in> ?piU" using hfU_bij hx unfolding bij_betw_def by (by100 blast)
        have hfUy: "fU y \<in> ?piU" using hfU_bij hy unfolding bij_betw_def by (by100 blast)
        have "fU (mulU x y) = ?mulU (fU x) (fU y)"
          using hfU_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
        thus "\<iota>fam 0 (fU (mulU x y)) = mulFP (\<iota>fam 0 (fU x)) (\<iota>fam 0 (fU y))"
          using h\<iota>fam_hom hfUx hfUy by (by100 auto)
      qed
      \<comment> \<open>h1 = \<iota>fam 1 \<circ> fV is a group hom GV \<rightarrow> FP.\<close>
      have h1_hom: "top1_group_hom_on GV mulV FP mulFP (\<lambda>x. \<iota>fam 1 (fV x))"
        unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix x assume hx: "x \<in> GV"
        have "fV x \<in> ?piV" using hfV_bij hx unfolding bij_betw_def by (by100 blast)
        thus "\<iota>fam 1 (fV x) \<in> FP" using h\<iota>fam_in by (by100 auto)
      next
        fix x y assume hx: "x \<in> GV" and hy: "y \<in> GV"
        have hfVx: "fV x \<in> ?piV" using hfV_bij hx unfolding bij_betw_def by (by100 blast)
        have hfVy: "fV y \<in> ?piV" using hfV_bij hy unfolding bij_betw_def by (by100 blast)
        have "fV (mulV x y) = ?mulV (fV x) (fV y)"
          using hfV_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
        thus "\<iota>fam 1 (fV (mulV x y)) = mulFP (\<iota>fam 1 (fV x)) (\<iota>fam 1 (fV y))"
          using h\<iota>fam_hom hfVx hfVy by (by100 auto)
      qed
      \<comment> \<open>Assemble homomorphism family for extension property.\<close>
      define hfam_fwd :: "nat \<Rightarrow> int \<Rightarrow> (nat \<times> (real \<Rightarrow> 'a) set) list" where
        "hfam_fwd = (\<lambda>\<alpha>. if \<alpha> = 0 then (\<lambda>x. \<iota>fam 0 (fU x)) else (\<lambda>x. \<iota>fam 1 (fV x)))"
      have hfam_fwd_hom: "\<forall>\<alpha>\<in>{0::nat,1}. top1_group_hom_on
          (if \<alpha> = 0 then GU else GV) (if \<alpha> = 0 then mulU else mulV)
          FP mulFP (hfam_fwd \<alpha>)"
      proof (intro ballI)
        fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
        hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
        thus "top1_group_hom_on (if \<alpha> = 0 then GU else GV) (if \<alpha> = 0 then mulU else mulV)
            FP mulFP (hfam_fwd \<alpha>)"
        proof
          assume "\<alpha> = 0"
          thus ?thesis using h0_hom unfolding hfam_fwd_def by (by100 simp)
        next
          assume "\<alpha> = 1"
          thus ?thesis using h1_hom unfolding hfam_fwd_def by (by100 simp)
        qed
      qed
      have hGG_grps: "\<forall>\<alpha>\<in>{0::nat,1}. top1_is_group_on
          (if \<alpha> = 0 then GU else GV) (if \<alpha> = 0 then mulU else mulV)
          (if \<alpha> = 0 then eU else eV) (if \<alpha> = 0 then invgU else invgV)"
      proof (intro ballI)
        fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
        hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
        thus "top1_is_group_on (if \<alpha> = 0 then GU else GV) (if \<alpha> = 0 then mulU else mulV)
            (if \<alpha> = 0 then eU else eV) (if \<alpha> = 0 then invgU else invgV)"
        proof
          assume "\<alpha> = 0" thus ?thesis using hGU_grp by (by100 simp)
        next
          assume "\<alpha> = 1" thus ?thesis using hGV_grp by (by100 simp)
        qed
      qed
      \<comment> \<open>Apply extension property to get \<Phi>: FPZ \<rightarrow> FP.\<close>
      obtain \<Phi> where h\<Phi>_hom: "top1_group_hom_on FPZ mulFPZ FP mulFP \<Phi>"
          and h\<Phi>_ext: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV).
              \<Phi> (\<iota>fam_Z \<alpha> x) = hfam_fwd \<alpha> x"
        using Lemma_68_3_extension_property[OF hFPZ hFP_grp hfam_fwd_hom hGG_grps]
        by (by100 blast)
      \<comment> \<open>Step E: Show \<Phi> is an isomorphism, i.e. FPZ \<cong> FP.
         This requires building the reverse map \<Psi>: FP \<rightarrow> FPZ and showing \<Psi>\<circ>\<Phi> = id, \<Phi>\<circ>\<Psi> = id
         via the uniqueness part of the extension property. This is detailed but routine.\<close>
      have hFPZ_iso_FP: "top1_groups_isomorphic_on FPZ mulFPZ FP mulFP"
      proof -
        \<comment> \<open>Build reverse: inverse isomorphisms fU\<inverse>: \<pi>U \<rightarrow> GU and fV\<inverse>: \<pi>V \<rightarrow> GV.\<close>
        define fU_inv where "fU_inv = inv_into GU fU"
        define fV_inv where "fV_inv = inv_into GV fV"
        have hfU_inv_bij: "bij_betw fU_inv ?piU GU"
          unfolding fU_inv_def by (rule bij_betw_inv_into[OF hfU_bij])
        have hfV_inv_bij: "bij_betw fV_inv ?piV GV"
          unfolding fV_inv_def by (rule bij_betw_inv_into[OF hfV_bij])
        \<comment> \<open>fU_inv is a group hom \<pi>U \<rightarrow> GU.\<close>
        have hfU_inv_hom: "top1_group_hom_on ?piU ?mulU GU mulU fU_inv"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume hx: "x \<in> ?piU"
          show "fU_inv x \<in> GU" using hfU_inv_bij hx unfolding bij_betw_def by (by100 blast)
        next
          fix x y assume hx: "x \<in> ?piU" and hy: "y \<in> ?piU"
          show "fU_inv (?mulU x y) = mulU (fU_inv x) (fU_inv y)"
          proof -
            have hfU_inv_x: "fU_inv x \<in> GU"
              using hfU_inv_bij hx unfolding bij_betw_def by (by100 blast)
            have hfU_inv_y: "fU_inv y \<in> GU"
              using hfU_inv_bij hy unfolding bij_betw_def by (by100 blast)
            have hfU_fU_inv_x: "fU (fU_inv x) = x"
              unfolding fU_inv_def by (rule bij_betw_inv_into_right[OF hfU_bij hx])
            have hfU_fU_inv_y: "fU (fU_inv y) = y"
              unfolding fU_inv_def by (rule bij_betw_inv_into_right[OF hfU_bij hy])
            have hmul_in: "mulU (fU_inv x) (fU_inv y) \<in> GU"
              by (rule group_mul_closed[OF hGU_grp hfU_inv_x hfU_inv_y])
            have "fU (mulU (fU_inv x) (fU_inv y)) = ?mulU (fU (fU_inv x)) (fU (fU_inv y))"
              using hfU_hom hfU_inv_x hfU_inv_y unfolding top1_group_hom_on_def by (by100 blast)
            hence "fU (mulU (fU_inv x) (fU_inv y)) = ?mulU x y"
              using hfU_fU_inv_x hfU_fU_inv_y by (by100 simp)
            moreover have hmul_piU: "?mulU x y \<in> ?piU"
              using group_mul_closed[OF hpiU_grp hx hy]
              by (by100 blast)
            moreover have "fU (fU_inv (?mulU x y)) = ?mulU x y"
              unfolding fU_inv_def by (rule bij_betw_inv_into_right[OF hfU_bij hmul_piU])
            ultimately have "fU (mulU (fU_inv x) (fU_inv y)) = fU (fU_inv (?mulU x y))"
              by (by100 simp)
            moreover have "mulU (fU_inv x) (fU_inv y) \<in> GU" by (rule hmul_in)
            moreover have "fU_inv (?mulU x y) \<in> GU"
              using hfU_inv_bij hmul_piU unfolding bij_betw_def by (by100 blast)
            moreover have "inj_on fU GU" using hfU_bij unfolding bij_betw_def by (by100 blast)
            ultimately show ?thesis unfolding inj_on_def by (by100 blast)
          qed
        qed
        \<comment> \<open>fV_inv is a group hom \<pi>V \<rightarrow> GV.\<close>
        have hfV_inv_hom: "top1_group_hom_on ?piV ?mulV GV mulV fV_inv"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume hx: "x \<in> ?piV"
          show "fV_inv x \<in> GV" using hfV_inv_bij hx unfolding bij_betw_def by (by100 blast)
        next
          fix x y assume hx: "x \<in> ?piV" and hy: "y \<in> ?piV"
          show "fV_inv (?mulV x y) = mulV (fV_inv x) (fV_inv y)"
          proof -
            have hfV_inv_x: "fV_inv x \<in> GV"
              using hfV_inv_bij hx unfolding bij_betw_def by (by100 blast)
            have hfV_inv_y: "fV_inv y \<in> GV"
              using hfV_inv_bij hy unfolding bij_betw_def by (by100 blast)
            have hfV_fV_inv_x: "fV (fV_inv x) = x"
              unfolding fV_inv_def by (rule bij_betw_inv_into_right[OF hfV_bij hx])
            have hfV_fV_inv_y: "fV (fV_inv y) = y"
              unfolding fV_inv_def by (rule bij_betw_inv_into_right[OF hfV_bij hy])
            have hmul_in: "mulV (fV_inv x) (fV_inv y) \<in> GV"
              by (rule group_mul_closed[OF hGV_grp hfV_inv_x hfV_inv_y])
            have "fV (mulV (fV_inv x) (fV_inv y)) = ?mulV (fV (fV_inv x)) (fV (fV_inv y))"
              using hfV_hom hfV_inv_x hfV_inv_y unfolding top1_group_hom_on_def by (by100 blast)
            hence "fV (mulV (fV_inv x) (fV_inv y)) = ?mulV x y"
              using hfV_fV_inv_x hfV_fV_inv_y by (by100 simp)
            moreover have hmul_piV: "?mulV x y \<in> ?piV"
              using group_mul_closed[OF hpiV_grp hx hy]
              by (by100 blast)
            moreover have "fV (fV_inv (?mulV x y)) = ?mulV x y"
              unfolding fV_inv_def by (rule bij_betw_inv_into_right[OF hfV_bij hmul_piV])
            ultimately have "fV (mulV (fV_inv x) (fV_inv y)) = fV (fV_inv (?mulV x y))"
              by (by100 simp)
            moreover have "mulV (fV_inv x) (fV_inv y) \<in> GV" by (rule hmul_in)
            moreover have "fV_inv (?mulV x y) \<in> GV"
              using hfV_inv_bij hmul_piV unfolding bij_betw_def by (by100 blast)
            moreover have "inj_on fV GV" using hfV_bij unfolding bij_betw_def by (by100 blast)
            ultimately show ?thesis unfolding inj_on_def by (by100 blast)
          qed
        qed
        \<comment> \<open>Build reverse hom family: \<pi>U \<rightarrow> FPZ via \<iota>fam_Z(0) \<circ> fU\<inverse> and \<pi>V \<rightarrow> FPZ via \<iota>fam_Z(1) \<circ> fV\<inverse>.\<close>
        have h\<iota>fam_Z_in: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). \<iota>fam_Z \<alpha> x \<in> FPZ"
          using hFPZ unfolding top1_is_free_product_on_def by (by100 blast)
        have h\<iota>fam_Z_hom: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV).
            \<forall>y\<in>(if \<alpha> = 0 then GU else GV).
            \<iota>fam_Z \<alpha> ((if \<alpha> = 0 then mulU else mulV) x y) = mulFPZ (\<iota>fam_Z \<alpha> x) (\<iota>fam_Z \<alpha> y)"
          using hFPZ unfolding top1_is_free_product_on_def by (by100 blast)
        \<comment> \<open>\<iota>fam_Z(0) \<circ> fU\<inverse> : \<pi>U \<rightarrow> FPZ is a group hom.\<close>
        have h0_rev_hom: "top1_group_hom_on ?piU ?mulU FPZ mulFPZ (\<lambda>x. \<iota>fam_Z 0 (fU_inv x))"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume hx: "x \<in> ?piU"
          have "fU_inv x \<in> GU" using hfU_inv_bij hx unfolding bij_betw_def by (by100 blast)
          thus "\<iota>fam_Z 0 (fU_inv x) \<in> FPZ" using h\<iota>fam_Z_in by (by100 auto)
        next
          fix x y assume hx: "x \<in> ?piU" and hy: "y \<in> ?piU"
          have hfUix: "fU_inv x \<in> GU" using hfU_inv_bij hx unfolding bij_betw_def by (by100 blast)
          have hfUiy: "fU_inv y \<in> GU" using hfU_inv_bij hy unfolding bij_betw_def by (by100 blast)
          have "fU_inv (?mulU x y) = mulU (fU_inv x) (fU_inv y)"
            using hfU_inv_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
          thus "\<iota>fam_Z 0 (fU_inv (?mulU x y)) = mulFPZ (\<iota>fam_Z 0 (fU_inv x)) (\<iota>fam_Z 0 (fU_inv y))"
            using h\<iota>fam_Z_hom hfUix hfUiy by (by100 auto)
        qed
        \<comment> \<open>\<iota>fam_Z(1) \<circ> fV\<inverse> : \<pi>V \<rightarrow> FPZ is a group hom.\<close>
        have h1_rev_hom: "top1_group_hom_on ?piV ?mulV FPZ mulFPZ (\<lambda>x. \<iota>fam_Z 1 (fV_inv x))"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume hx: "x \<in> ?piV"
          have "fV_inv x \<in> GV" using hfV_inv_bij hx unfolding bij_betw_def by (by100 blast)
          thus "\<iota>fam_Z 1 (fV_inv x) \<in> FPZ" using h\<iota>fam_Z_in by (by100 auto)
        next
          fix x y assume hx: "x \<in> ?piV" and hy: "y \<in> ?piV"
          have hfVix: "fV_inv x \<in> GV" using hfV_inv_bij hx unfolding bij_betw_def by (by100 blast)
          have hfViy: "fV_inv y \<in> GV" using hfV_inv_bij hy unfolding bij_betw_def by (by100 blast)
          have "fV_inv (?mulV x y) = mulV (fV_inv x) (fV_inv y)"
            using hfV_inv_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
          thus "\<iota>fam_Z 1 (fV_inv (?mulV x y)) = mulFPZ (\<iota>fam_Z 1 (fV_inv x)) (\<iota>fam_Z 1 (fV_inv y))"
            using h\<iota>fam_Z_hom hfVix hfViy by (by100 auto)
        qed
        \<comment> \<open>Assemble reverse hom family for FP's extension property.\<close>
        define hfam_rev :: "nat \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (nat \<times> int) list" where
          "hfam_rev = (\<lambda>\<alpha>. if \<alpha> = 0 then (\<lambda>x. \<iota>fam_Z 0 (fU_inv x))
                                       else (\<lambda>x. \<iota>fam_Z 1 (fV_inv x)))"
        have hfam_rev_hom: "\<forall>\<alpha>\<in>{0::nat,1}. top1_group_hom_on
            (if \<alpha> = 0 then ?piU else ?piV) (if \<alpha> = 0 then ?mulU else ?mulV)
            FPZ mulFPZ (hfam_rev \<alpha>)"
        proof (intro ballI)
          fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
          hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
          thus "top1_group_hom_on (if \<alpha> = 0 then ?piU else ?piV) (if \<alpha> = 0 then ?mulU else ?mulV)
              FPZ mulFPZ (hfam_rev \<alpha>)"
          proof
            assume "\<alpha> = 0" thus ?thesis using h0_rev_hom unfolding hfam_rev_def by (by100 simp)
          next
            assume "\<alpha> = 1" thus ?thesis using h1_rev_hom unfolding hfam_rev_def by (by100 simp)
          qed
        qed
        \<comment> \<open>Apply extension property to get \<Psi>: FP \<rightarrow> FPZ.\<close>
        obtain \<Psi> where h\<Psi>_hom: "top1_group_hom_on FP mulFP FPZ mulFPZ \<Psi>"
            and h\<Psi>_ext: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV).
                \<Psi> (\<iota>fam \<alpha> x) = hfam_rev \<alpha> x"
            and h\<Psi>_unique: "\<forall>h'. top1_group_hom_on FP mulFP FPZ mulFPZ h'
                \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV).
                    h' (\<iota>fam \<alpha> x) = hfam_rev \<alpha> x)
                \<longrightarrow> (\<forall>g\<in>FP. h' g = \<Psi> g)"
          using Lemma_68_3_extension_property[OF hFP hFPZ_grp hfam_rev_hom hgroups_UV]
          by (by100 blast)
        \<comment> \<open>Show \<Psi> \<circ> \<Phi> = id on FPZ via uniqueness of 68.3 on FPZ.
           On generators: for x \<in> GU, (\<Psi>\<circ>\<Phi>)(\<iota>fam_Z 0 x) = \<Psi>(\<iota>fam 0 (fU x)) = \<iota>fam_Z 0 (fU\<inverse>(fU x)) = \<iota>fam_Z 0 x.
           Similarly for x \<in> GV.\<close>
        have h\<Psi>\<Phi>_on_gens: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV).
            \<Psi> (\<Phi> (\<iota>fam_Z \<alpha> x)) = \<iota>fam_Z \<alpha> x"
        proof (intro ballI)
          fix \<alpha> :: nat and x :: int assume h\<alpha>: "\<alpha> \<in> {0, 1}" and hx: "x \<in> (if \<alpha> = 0 then GU else GV)"
          have "\<alpha> = 0 \<or> \<alpha> = 1" using h\<alpha> by (by100 blast)
          thus "\<Psi> (\<Phi> (\<iota>fam_Z \<alpha> x)) = \<iota>fam_Z \<alpha> x"
          proof
            assume h\<alpha>0: "\<alpha> = 0"
            hence hx_GU: "x \<in> GU" using hx by (by100 simp)
            have "\<Phi> (\<iota>fam_Z 0 x) = hfam_fwd 0 x" using h\<Phi>_ext hx_GU by (by100 auto)
            hence "\<Phi> (\<iota>fam_Z 0 x) = \<iota>fam 0 (fU x)" unfolding hfam_fwd_def by (by100 simp)
            moreover have "\<Psi> (\<iota>fam 0 (fU x)) = hfam_rev 0 (fU x)"
            proof -
              have "fU x \<in> ?piU" using hfU_bij hx_GU unfolding bij_betw_def by (by100 blast)
              thus ?thesis using h\<Psi>_ext by (by100 auto)
            qed
            moreover have "hfam_rev 0 (fU x) = \<iota>fam_Z 0 (fU_inv (fU x))"
              unfolding hfam_rev_def by (by100 simp)
            moreover have "fU_inv (fU x) = x"
              unfolding fU_inv_def using hfU_bij hx_GU
              by (rule inv_into_f_f[OF bij_betw_imp_inj_on])
            ultimately show ?thesis using h\<alpha>0 by (by100 simp)
          next
            assume h\<alpha>1: "\<alpha> = 1"
            hence hx_GV: "x \<in> GV" using hx by (by100 simp)
            have "\<Phi> (\<iota>fam_Z 1 x) = hfam_fwd 1 x" using h\<Phi>_ext hx_GV by (by100 auto)
            hence "\<Phi> (\<iota>fam_Z 1 x) = \<iota>fam 1 (fV x)" unfolding hfam_fwd_def by (by100 simp)
            moreover have "\<Psi> (\<iota>fam 1 (fV x)) = hfam_rev 1 (fV x)"
            proof -
              have "fV x \<in> ?piV" using hfV_bij hx_GV unfolding bij_betw_def by (by100 blast)
              thus ?thesis using h\<Psi>_ext by (by100 auto)
            qed
            moreover have "hfam_rev 1 (fV x) = \<iota>fam_Z 1 (fV_inv (fV x))"
              unfolding hfam_rev_def by (by100 simp)
            moreover have "fV_inv (fV x) = x"
              unfolding fV_inv_def using hfV_bij hx_GV
              by (rule inv_into_f_f[OF bij_betw_imp_inj_on])
            ultimately show ?thesis using h\<alpha>1 by (by100 simp)
          qed
        qed
        \<comment> \<open>By uniqueness on FPZ: \<Psi>\<circ>\<Phi> agrees with id on generators, hence on all of FPZ.\<close>
        have hid_on_gens: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV).
            (\<lambda>g. g) (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x"
          by (by100 blast)
        \<comment> \<open>id: FPZ \<rightarrow> FPZ is a group hom.\<close>
        have hid_hom: "top1_group_hom_on FPZ mulFPZ FPZ mulFPZ (\<lambda>g. g)"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> FPZ" thus "x \<in> FPZ" .
        next
          fix x y assume "x \<in> FPZ" "y \<in> FPZ"
          thus "mulFPZ x y = mulFPZ x y" by (by100 simp)
        qed
        \<comment> \<open>\<Psi>\<circ>\<Phi>: FPZ \<rightarrow> FPZ is a group hom.\<close>
        have h\<Psi>\<Phi>_hom: "top1_group_hom_on FPZ mulFPZ FPZ mulFPZ (\<lambda>g. \<Psi> (\<Phi> g))"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume hx: "x \<in> FPZ"
          have "\<Phi> x \<in> FP" using h\<Phi>_hom hx unfolding top1_group_hom_on_def by (by100 blast)
          thus "\<Psi> (\<Phi> x) \<in> FPZ" using h\<Psi>_hom unfolding top1_group_hom_on_def by (by100 blast)
        next
          fix x y assume hx: "x \<in> FPZ" and hy: "y \<in> FPZ"
          have h\<Phi>x: "\<Phi> x \<in> FP" using h\<Phi>_hom hx unfolding top1_group_hom_on_def by (by100 blast)
          have h\<Phi>y: "\<Phi> y \<in> FP" using h\<Phi>_hom hy unfolding top1_group_hom_on_def by (by100 blast)
          have "\<Phi> (mulFPZ x y) = mulFP (\<Phi> x) (\<Phi> y)"
            using h\<Phi>_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
          moreover have "\<Psi> (mulFP (\<Phi> x) (\<Phi> y)) = mulFPZ (\<Psi> (\<Phi> x)) (\<Psi> (\<Phi> y))"
            using h\<Psi>_hom h\<Phi>x h\<Phi>y unfolding top1_group_hom_on_def by (by100 blast)
          ultimately show "\<Psi> (\<Phi> (mulFPZ x y)) = mulFPZ (\<Psi> (\<Phi> x)) (\<Psi> (\<Phi> y))" by (by100 simp)
        qed
        \<comment> \<open>By uniqueness: both \<Psi>\<circ>\<Phi> and id agree on generators, hence on all of FPZ.\<close>
        have h\<iota>Z_id_hom: "\<forall>\<alpha>\<in>{0::nat,1}. top1_group_hom_on
            (if \<alpha> = 0 then GU else GV) (if \<alpha> = 0 then mulU else mulV)
            FPZ mulFPZ (\<iota>fam_Z \<alpha>)"
        proof (intro ballI)
          fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
          show "top1_group_hom_on (if \<alpha> = 0 then GU else GV)
              (if \<alpha> = 0 then mulU else mulV) FPZ mulFPZ (\<iota>fam_Z \<alpha>)"
            unfolding top1_group_hom_on_def
          proof (intro conjI ballI)
            fix x assume hx: "x \<in> (if \<alpha> = 0 then GU else GV)"
            show "\<iota>fam_Z \<alpha> x \<in> FPZ" using h\<iota>fam_Z_in h\<alpha> hx by (by100 blast)
          next
            fix x y assume hx: "x \<in> (if \<alpha> = 0 then GU else GV)"
                and hy: "y \<in> (if \<alpha> = 0 then GU else GV)"
            show "\<iota>fam_Z \<alpha> ((if \<alpha> = 0 then mulU else mulV) x y) =
                mulFPZ (\<iota>fam_Z \<alpha> x) (\<iota>fam_Z \<alpha> y)"
              using h\<iota>fam_Z_hom h\<alpha> hx hy by (by100 blast)
          qed
        qed
        have h68_3_FPZ: "\<exists>h. top1_group_hom_on FPZ mulFPZ FPZ mulFPZ h
            \<and> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). h (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x)
            \<and> (\<forall>h'. top1_group_hom_on FPZ mulFPZ FPZ mulFPZ h'
                \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). h' (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x)
                \<longrightarrow> (\<forall>g\<in>FPZ. h' g = h g))"
          using Lemma_68_3_extension_property[OF hFPZ hFPZ_grp h\<iota>Z_id_hom hGG_grps] .
        \<comment> \<open>The uniqueness part of the extension property on FPZ: any two homs agreeing on
           generators agree everywhere.\<close>
        \<comment> \<open>Both id and \<Psi>\<circ>\<Phi> agree on generators, so they agree on all of FPZ.\<close>
        have h\<Psi>\<Phi>_is_id: "\<forall>g\<in>FPZ. \<Psi> (\<Phi> g) = g"
        proof -
          \<comment> \<open>\<Psi>\<circ>\<Phi> and id both agree on generators of FPZ, so by uniqueness of the
             extension property they agree everywhere. We use Lemma_68_3 directly.\<close>
          note h68_3_result = Lemma_68_3_extension_property[OF hFPZ hFPZ_grp h\<iota>Z_id_hom hGG_grps]
          \<comment> \<open>Extract uniqueness: any two homs agreeing on generators agree everywhere.\<close>
          show ?thesis
          proof (rule ballI)
            fix g assume hg: "g \<in> FPZ"
            from h68_3_result obtain hZ where
                hZ_uniq: "\<forall>h'. top1_group_hom_on FPZ mulFPZ FPZ mulFPZ h'
                    \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). h' (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x)
                    \<longrightarrow> (\<forall>g\<in>FPZ. h' g = hZ g)"
            proof -
              from h68_3_result
              have "\<exists>hZ0. (\<forall>h'. top1_group_hom_on FPZ mulFPZ FPZ mulFPZ h'
                       \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). h' (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x)
                       \<longrightarrow> (\<forall>g\<in>FPZ. h' g = hZ0 g))"
                apply (elim exE conjE)
                apply (rule exI)
                apply assumption
                done
              then obtain hZ0 where hZ0_uniq: "\<forall>h'. top1_group_hom_on FPZ mulFPZ FPZ mulFPZ h'
                       \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then GU else GV). h' (\<iota>fam_Z \<alpha> x) = \<iota>fam_Z \<alpha> x)
                       \<longrightarrow> (\<forall>g\<in>FPZ. h' g = hZ0 g)"
                by (by100 blast)
              thus ?thesis using that by (by100 blast)
            qed
            have "(\<lambda>g. \<Psi> (\<Phi> g)) g = hZ g"
              using hZ_uniq h\<Psi>\<Phi>_hom h\<Psi>\<Phi>_on_gens hg by (by100 blast)
            moreover have "g = hZ g"
              using hZ_uniq hid_hom hid_on_gens hg by (by100 blast)
            ultimately show "\<Psi> (\<Phi> g) = g" by (by100 simp)
          qed
        qed
        \<comment> \<open>Similarly show \<Phi>\<circ>\<Psi> = id on FP.\<close>
        have h\<Phi>\<Psi>_on_gens: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV).
            \<Phi> (\<Psi> (\<iota>fam \<alpha> x)) = \<iota>fam \<alpha> x"
        proof (intro ballI)
          fix \<alpha> :: nat and x assume h\<alpha>: "\<alpha> \<in> {0::nat, 1}"
              and hx: "x \<in> (if \<alpha> = 0 then ?piU else ?piV)"
          have "\<alpha> = 0 \<or> \<alpha> = 1" using h\<alpha> by (by100 blast)
          thus "\<Phi> (\<Psi> (\<iota>fam \<alpha> x)) = \<iota>fam \<alpha> x"
          proof
            assume h\<alpha>0: "\<alpha> = 0"
            hence hx_piU: "x \<in> ?piU" using hx by (by100 simp)
            have h1: "\<Psi> (\<iota>fam 0 x) = hfam_rev 0 x"
              using h\<Psi>_ext hx_piU by (by100 auto)
            have h2: "hfam_rev 0 x = \<iota>fam_Z 0 (fU_inv x)"
              unfolding hfam_rev_def by (by100 simp)
            have hfUi_in: "fU_inv x \<in> GU"
              using hfU_inv_bij hx_piU unfolding bij_betw_def by (by100 blast)
            have h3: "\<Phi> (\<iota>fam_Z 0 (fU_inv x)) = hfam_fwd 0 (fU_inv x)"
              using h\<Phi>_ext hfUi_in by (by100 auto)
            have h4: "hfam_fwd 0 (fU_inv x) = \<iota>fam 0 (fU (fU_inv x))"
              unfolding hfam_fwd_def by (by100 simp)
            have h5: "fU (fU_inv x) = x"
              unfolding fU_inv_def by (rule bij_betw_inv_into_right[OF hfU_bij hx_piU])
            show ?thesis using h\<alpha>0 h1 h2 h3 h4 h5 by (by100 simp)
          next
            assume h\<alpha>1: "\<alpha> = 1"
            hence hx_piV: "x \<in> ?piV" using hx by (by100 simp)
            have h1: "\<Psi> (\<iota>fam 1 x) = hfam_rev 1 x"
              using h\<Psi>_ext hx_piV by (by100 auto)
            have h2: "hfam_rev 1 x = \<iota>fam_Z 1 (fV_inv x)"
              unfolding hfam_rev_def by (by100 simp)
            have hfVi_in: "fV_inv x \<in> GV"
              using hfV_inv_bij hx_piV unfolding bij_betw_def by (by100 blast)
            have h3: "\<Phi> (\<iota>fam_Z 1 (fV_inv x)) = hfam_fwd 1 (fV_inv x)"
              using h\<Phi>_ext hfVi_in by (by100 auto)
            have h4: "hfam_fwd 1 (fV_inv x) = \<iota>fam 1 (fV (fV_inv x))"
              unfolding hfam_fwd_def by (by100 simp)
            have h5: "fV (fV_inv x) = x"
              unfolding fV_inv_def by (rule bij_betw_inv_into_right[OF hfV_bij hx_piV])
            show ?thesis using h\<alpha>1 h1 h2 h3 h4 h5 by (by100 simp)
          qed
        qed
        \<comment> \<open>By uniqueness on FP: \<Phi>\<circ>\<Psi> = id on FP.
           Uses the same uniqueness argument as for FPZ above.\<close>
        have h\<Phi>\<Psi>_is_id: "\<forall>g\<in>FP. \<Phi> (\<Psi> g) = g"
        proof -
          \<comment> \<open>Build hom family: \<iota>fam_\<alpha> is a hom from factor_\<alpha> to FP.\<close>
          have h\<iota>fam_id_hom: "\<forall>\<alpha>\<in>{0::nat,1}. top1_group_hom_on
              (if \<alpha> = 0 then ?piU else ?piV) (if \<alpha> = 0 then ?mulU else ?mulV)
              FP mulFP (\<iota>fam \<alpha>)"
          proof (intro ballI)
            fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
            show "top1_group_hom_on (if \<alpha> = 0 then ?piU else ?piV)
                (if \<alpha> = 0 then ?mulU else ?mulV) FP mulFP (\<iota>fam \<alpha>)"
              unfolding top1_group_hom_on_def
            proof (intro conjI ballI)
              fix x assume hx: "x \<in> (if \<alpha> = 0 then ?piU else ?piV)"
              show "\<iota>fam \<alpha> x \<in> FP" using h\<iota>fam_in h\<alpha> hx by (by100 blast)
            next
              fix x y assume hx: "x \<in> (if \<alpha> = 0 then ?piU else ?piV)"
                  and hy: "y \<in> (if \<alpha> = 0 then ?piU else ?piV)"
              show "\<iota>fam \<alpha> ((if \<alpha> = 0 then ?mulU else ?mulV) x y) =
                  mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
                using h\<iota>fam_hom h\<alpha> hx hy by (by100 blast)
            qed
          qed
          note h68_3_FP = Lemma_68_3_extension_property[OF hFP hFP_grp h\<iota>fam_id_hom hgroups_UV]
          show ?thesis
          proof (rule ballI)
            fix g assume hg: "g \<in> FP"
            from h68_3_FP
            have "\<exists>hFP0. (\<forall>h'. top1_group_hom_on FP mulFP FP mulFP h'
                       \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV). h' (\<iota>fam \<alpha> x) = \<iota>fam \<alpha> x)
                       \<longrightarrow> (\<forall>g\<in>FP. h' g = hFP0 g))"
              apply (elim exE conjE)
              apply (rule exI)
              apply assumption
              done
            then obtain hFP0 where hFP0_uniq: "\<forall>h'. top1_group_hom_on FP mulFP FP mulFP h'
                       \<longrightarrow> (\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?piU else ?piV). h' (\<iota>fam \<alpha> x) = \<iota>fam \<alpha> x)
                       \<longrightarrow> (\<forall>g\<in>FP. h' g = hFP0 g)"
              by (by100 blast)
            \<comment> \<open>\<Phi>\<circ>\<Psi> is a group hom FP \<rightarrow> FP.\<close>
            have h\<Phi>\<Psi>_hom: "top1_group_hom_on FP mulFP FP mulFP (\<lambda>g. \<Phi> (\<Psi> g))"
              unfolding top1_group_hom_on_def
            proof (intro conjI ballI)
              fix x assume hx: "x \<in> FP"
              have "\<Psi> x \<in> FPZ" using h\<Psi>_hom hx unfolding top1_group_hom_on_def by (by100 blast)
              thus "\<Phi> (\<Psi> x) \<in> FP" using h\<Phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
            next
              fix x y assume hx: "x \<in> FP" and hy: "y \<in> FP"
              have h\<Psi>x: "\<Psi> x \<in> FPZ" using h\<Psi>_hom hx unfolding top1_group_hom_on_def by (by100 blast)
              have h\<Psi>y: "\<Psi> y \<in> FPZ" using h\<Psi>_hom hy unfolding top1_group_hom_on_def by (by100 blast)
              have "\<Psi> (mulFP x y) = mulFPZ (\<Psi> x) (\<Psi> y)"
                using h\<Psi>_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
              moreover have "\<Phi> (mulFPZ (\<Psi> x) (\<Psi> y)) = mulFP (\<Phi> (\<Psi> x)) (\<Phi> (\<Psi> y))"
                using h\<Phi>_hom h\<Psi>x h\<Psi>y unfolding top1_group_hom_on_def by (by100 blast)
              ultimately show "\<Phi> (\<Psi> (mulFP x y)) = mulFP (\<Phi> (\<Psi> x)) (\<Phi> (\<Psi> y))" by (by100 simp)
            qed
            have hid_FP_hom: "top1_group_hom_on FP mulFP FP mulFP (\<lambda>g. g)"
              unfolding top1_group_hom_on_def by (by100 blast)
            have "(\<lambda>g. \<Phi> (\<Psi> g)) g = hFP0 g"
              using hFP0_uniq h\<Phi>\<Psi>_hom h\<Phi>\<Psi>_on_gens hg by (by100 blast)
            moreover have "g = hFP0 g"
              using hFP0_uniq hid_FP_hom hg by (by100 auto)
            ultimately show "\<Phi> (\<Psi> g) = g" by (by100 simp)
          qed
        qed
        \<comment> \<open>Now \<Phi> is a bijection with inverse \<Psi>.\<close>
        have h\<Phi>_surj: "\<Phi> ` FPZ = FP"
        proof
          show "\<Phi> ` FPZ \<subseteq> FP"
            using h\<Phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
        next
          show "FP \<subseteq> \<Phi> ` FPZ"
          proof
            fix y assume hy: "y \<in> FP"
            have h\<Psi>y: "\<Psi> y \<in> FPZ"
              using h\<Psi>_hom hy unfolding top1_group_hom_on_def by (by100 blast)
            have h\<Phi>\<Psi>y: "\<Phi> (\<Psi> y) = y" using h\<Phi>\<Psi>_is_id hy by (by100 blast)
            have "y = \<Phi> (\<Psi> y)" using h\<Phi>\<Psi>y by (by100 simp)
            thus "y \<in> \<Phi> ` FPZ" using h\<Psi>y by (by100 force)
          qed
        qed
        have h\<Phi>_inj: "inj_on \<Phi> FPZ"
        proof (rule inj_onI)
          fix x y assume hx: "x \<in> FPZ" and hy: "y \<in> FPZ" and heq: "\<Phi> x = \<Phi> y"
          have hx': "\<Psi> (\<Phi> x) = x" using h\<Psi>\<Phi>_is_id hx by (by100 blast)
          have hy': "\<Psi> (\<Phi> y) = y" using h\<Psi>\<Phi>_is_id hy by (by100 blast)
          have "\<Psi> (\<Phi> x) = \<Psi> (\<Phi> y)" using heq by (by100 simp)
          thus "x = y" using hx' hy' by (by100 simp)
        qed
        have h\<Phi>_bij: "bij_betw \<Phi> FPZ FP"
          unfolding bij_betw_def using h\<Phi>_inj h\<Phi>_surj by (by100 blast)
        \<comment> \<open>Conclude FPZ \<cong> FP.\<close>
        show ?thesis
          unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
          using h\<Phi>_hom h\<Phi>_bij by (by100 blast)
      qed
      \<comment> \<open>Step F: Chain isomorphisms: FPZ \<cong> FP and \<pi>_1(X) \<cong> FP, so FPZ \<cong> \<pi>_1(X).\<close>
      have hFPZ_iso_piX: "top1_groups_isomorphic_on FPZ mulFPZ
          (top1_fundamental_group_carrier X TX p)
          (top1_fundamental_group_mul X TX p)"
        by (rule groups_isomorphic_trans_fwd[OF hFPZ_iso_FP
            top1_groups_isomorphic_on_sym[OF hSvK_iso
              top1_fundamental_group_is_group[OF hTX hp_X]
              hFP_grp]])
      \<comment> \<open>FPZ is free on {..<n} and isomorphic to \<pi>_1(X).
         Type transfer: FPZ :: (nat \<times> int) list set, but we need G :: int set.
         Since (nat \<times> int) list is countable, there exists a bijection to int.
         Transport the group structure through this bijection to get a free group on int set.\<close>
      have hFPZ_free_and_iso: "top1_is_free_group_full_on FPZ mulFPZ eFPZ invgFPZ \<iota>Z {..<n}
          \<and> top1_groups_isomorphic_on FPZ mulFPZ
              (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p)"
        using hFPZ_free_n hFPZ_iso_piX by (by100 blast)
      \<comment> \<open>Transport via encoding: there exists a bijection \<sigma>: (nat \<times> int) list \<rightarrow> int.
         Define G = \<sigma> ` FPZ, mul_G a b = \<sigma> (mulFPZ (\<sigma>\<inverse> a) (\<sigma>\<inverse> b)), etc.
         Then G :: int set is a free group on {..<n} and isomorphic to \<pi>_1(X).\<close>
      obtain \<sigma> :: "(nat \<times> int) list \<Rightarrow> int" where
          h\<sigma>_bij: "bij \<sigma>"
      proof -
        \<comment> \<open>Define int_to_nat: injective encoding of int as nat.\<close>
        define int_to_nat :: "int \<Rightarrow> nat" where
          "int_to_nat i = (if i \<ge> 0 then 2 * nat i else 2 * nat (- i - 1) + 1)" for i
        have int_to_nat_inj: "inj int_to_nat"
        proof (rule injI)
          fix i j :: int assume h: "int_to_nat i = int_to_nat j"
          show "i = j"
          proof (cases "i \<ge> 0")
            case True note hi = True
            show ?thesis
            proof (cases "j \<ge> 0")
              case True
              have "2 * nat i = 2 * nat j" using h hi True unfolding int_to_nat_def by (by100 simp)
              hence "nat i = nat j" by (by100 simp)
              thus ?thesis using hi True by (by100 simp)
            next
              case False
              have h2: "2 * nat i = 2 * nat (- j - 1) + 1"
                using h hi False unfolding int_to_nat_def by (by100 simp)
              have "even (2 * nat i :: nat)" by (by100 simp)
              hence "even (2 * nat (- j - 1) + 1 :: nat)" using h2 by (by100 simp)
              moreover have "odd (2 * nat (- j - 1) + 1 :: nat)" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
          next
            case False note hi = False
            show ?thesis
            proof (cases "j \<ge> 0")
              case True
              have "2 * nat (- i - 1) + 1 = 2 * nat j"
                using h hi True unfolding int_to_nat_def by (by100 simp)
              hence "even (2 * nat (- i - 1) + 1 :: nat)" by (by100 simp)
              thus ?thesis by (by100 simp)
            next
              case False
              have "2 * nat (- i - 1) + 1 = 2 * nat (- j - 1) + 1"
                using h hi False unfolding int_to_nat_def by (by100 simp)
              hence "nat (- i - 1) = nat (- j - 1)" by (by100 simp)
              thus ?thesis using hi False by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Define modified Cantor pairing (without div, using 2*cantor pairing).\<close>
        define cpair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
          "cpair m n = (m + n) * (m + n + 1) + 2 * m" for m n
        have cpair_inj: "\<And>m1 n1 m2 n2. cpair m1 n1 = cpair m2 n2 \<Longrightarrow> m1 = m2 \<and> n1 = n2"
        proof -
          fix m1 n1 m2 n2 :: nat
          assume h: "cpair m1 n1 = cpair m2 n2"
          define s1 where "s1 = m1 + n1"
          define s2 where "s2 = m2 + n2"
          have hc1: "cpair m1 n1 = s1 * (s1 + 1) + 2 * m1"
            unfolding cpair_def s1_def by (by100 simp)
          have hc2: "cpair m2 n2 = s2 * (s2 + 1) + 2 * m2"
            unfolding cpair_def s2_def by (by100 simp)
          have hm1_le: "m1 \<le> s1" unfolding s1_def by (by100 simp)
          have hm2_le: "m2 \<le> s2" unfolding s2_def by (by100 simp)
          \<comment> \<open>Key: s*(s+1) \<le> cpair m n \<le> s*(s+1) + 2*s < (s+1)*(s+2), so s is determined.\<close>
          have hbound1: "cpair m1 n1 < (s1 + 1) * (s1 + 2)"
          proof -
            have "cpair m1 n1 \<le> s1 * (s1 + 1) + 2 * s1" using hc1 hm1_le by (by100 linarith)
            also have "\<dots> = s1 * s1 + 3 * s1" by (by100 simp)
            also have "\<dots> < s1 * s1 + 3 * s1 + 2" by (by100 simp)
            also have "\<dots> = (s1 + 1) * (s1 + 2)" by (by100 simp)
            finally show ?thesis .
          qed
          have hbound2: "cpair m2 n2 < (s2 + 1) * (s2 + 2)"
          proof -
            have "cpair m2 n2 \<le> s2 * (s2 + 1) + 2 * s2" using hc2 hm2_le by (by100 linarith)
            also have "\<dots> = s2 * s2 + 3 * s2" by (by100 simp)
            also have "\<dots> < s2 * s2 + 3 * s2 + 2" by (by100 simp)
            also have "\<dots> = (s2 + 1) * (s2 + 2)" by (by100 simp)
            finally show ?thesis .
          qed
          have hlower1: "s1 * (s1 + 1) \<le> cpair m1 n1"
            using hc1 by (by100 linarith)
          have hlower2: "s2 * (s2 + 1) \<le> cpair m2 n2"
            using hc2 by (by100 linarith)
          have hs_eq: "s1 = s2"
          proof (rule ccontr)
            assume "s1 \<noteq> s2"
            show False
            proof (cases "s1 < s2")
              case True
              hence "s1 + 1 \<le> s2" by (by100 simp)
              have hs12: "s1 + 2 \<le> s2 + 1" using \<open>s1 + 1 \<le> s2\<close> by (by100 simp)
              have "(s1 + 1) * (s1 + 2) \<le> s2 * (s2 + 1)"
                using mult_le_mono[OF \<open>s1 + 1 \<le> s2\<close> hs12] by (by100 simp)
              hence "cpair m1 n1 < cpair m2 n2"
                using hbound1 hlower2 by (by100 linarith)
              thus False using h by (by100 simp)
            next
              case False
              hence "s2 < s1" using \<open>s1 \<noteq> s2\<close> by (by100 simp)
              hence "s2 + 1 \<le> s1" by (by100 simp)
              have hs22: "s2 + 2 \<le> s1 + 1" using \<open>s2 + 1 \<le> s1\<close> by (by100 simp)
              have "(s2 + 1) * (s2 + 2) \<le> s1 * (s1 + 1)"
                using mult_le_mono[OF \<open>s2 + 1 \<le> s1\<close> hs22] by (by100 simp)
              hence "cpair m2 n2 < cpair m1 n1"
                using hbound2 hlower1 by (by100 linarith)
              thus False using h by (by100 simp)
            qed
          qed
          have hceq: "s1 * (s1 + 1) + 2 * m1 = s2 * (s2 + 1) + 2 * m2"
            using h hc1 hc2 by (by100 linarith)
          hence "2 * m1 = 2 * m2" using hs_eq by (by100 simp)
          hence "m1 = m2" by (by100 simp)
          moreover hence "n1 = n2" using hs_eq unfolding s1_def s2_def by (by100 simp)
          ultimately show "m1 = m2 \<and> n1 = n2" by (by100 blast)
        qed
        \<comment> \<open>Define encoding of (nat \<times> int) as nat.\<close>
        define pair_enc :: "nat \<times> int \<Rightarrow> nat" where
          "pair_enc p = cpair (fst p) (int_to_nat (snd p))" for p
        have pair_enc_inj: "inj pair_enc"
        proof (rule injI)
          fix p q :: "nat \<times> int" assume h: "pair_enc p = pair_enc q"
          have "fst p = fst q \<and> int_to_nat (snd p) = int_to_nat (snd q)"
            using cpair_inj h unfolding pair_enc_def by (by100 blast)
          hence "fst p = fst q" "snd p = snd q"
            using injD[OF int_to_nat_inj] by (by100 blast)+
          thus "p = q" by (cases p, cases q) (by100 simp)
        qed
        \<comment> \<open>Define encoding of (nat \<times> int) list as nat.\<close>
        define list_enc :: "(nat \<times> int) list \<Rightarrow> nat" where
          "list_enc xs = rec_list 0 (\<lambda>x _ r. cpair (pair_enc x + 1) r + 1) xs" for xs
        have list_enc_nil: "list_enc [] = 0"
          unfolding list_enc_def by (by100 simp)
        have list_enc_cons: "\<And>x xs. list_enc (x # xs) = cpair (pair_enc x + 1) (list_enc xs) + 1"
          unfolding list_enc_def by (by100 simp)
        have list_enc_inj: "inj list_enc"
        proof (rule injI)
          fix xs ys :: "(nat \<times> int) list"
          show "list_enc xs = list_enc ys \<Longrightarrow> xs = ys"
          proof (induction xs arbitrary: ys)
            case Nil
            thus ?case
            proof (cases ys)
              case Nil thus ?thesis by (by100 simp)
            next
              case (Cons b bs)
              have "0 = cpair (pair_enc b + 1) (list_enc bs) + 1"
                using \<open>list_enc [] = list_enc ys\<close> list_enc_nil list_enc_cons Cons by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
          next
            case (Cons a as)
            thus ?case
            proof (cases ys)
              case Nil
              have "cpair (pair_enc a + 1) (list_enc as) + 1 = 0"
                using Cons.prems Nil list_enc_nil list_enc_cons by (by100 simp)
              thus ?thesis by (by100 simp)
            next
              case (Cons b bs)
              have ha: "list_enc (a # as) = cpair (pair_enc a + 1) (list_enc as) + 1"
                using list_enc_cons by (by100 simp)
              have hb: "list_enc (b # bs) = cpair (pair_enc b + 1) (list_enc bs) + 1"
                using list_enc_cons by (by100 simp)
              have "cpair (pair_enc a + 1) (list_enc as) = cpair (pair_enc b + 1) (list_enc bs)"
                using Cons.prems Cons ha hb by (by100 simp)
              hence "pair_enc a + 1 = pair_enc b + 1 \<and> list_enc as = list_enc bs"
                using cpair_inj by (by100 blast)
              hence "pair_enc a = pair_enc b" "list_enc as = list_enc bs" by (by100 simp)+
              hence "a = b" using injD[OF pair_enc_inj] by (by100 blast)
              moreover have "as = bs" using Cons.IH \<open>list_enc as = list_enc bs\<close> .
              ultimately show ?thesis using Cons by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Compose: list_enc followed by of_nat gives injection (nat \<times> int) list \<rightarrow> int.\<close>
        have f_inj: "inj (int \<circ> list_enc)"
          using inj_of_nat list_enc_inj by (rule inj_compose)
        \<comment> \<open>The other direction: int \<rightarrow> (nat \<times> int) list via \<lambda>i. [(0, i)].\<close>
        have g_inj: "inj (\<lambda>i::int. [(0::nat, i)])"
          by (rule injI) (by100 simp)
        \<comment> \<open>Apply Schroeder-Bernstein to get a bijection.\<close>
        have "\<exists>h. bij_betw h (UNIV :: (nat \<times> int) list set) (UNIV :: int set)"
          using Schroeder_Bernstein[where f="int \<circ> list_enc" and g="\<lambda>i. [(0, i)]"
              and A=UNIV and B=UNIV]
          using f_inj g_inj by (by100 simp)
        then obtain h :: "(nat \<times> int) list \<Rightarrow> int" where "bij_betw h UNIV UNIV" by (by100 blast)
        hence "bij h"
        proof -
          have "inj h" using \<open>bij_betw h UNIV UNIV\<close> unfolding bij_betw_def inj_on_def by (by100 blast)
          moreover have "surj h" using \<open>bij_betw h UNIV UNIV\<close> using bij_betw_imp_surj by (by100 blast)
          ultimately show "bij h" unfolding bij_def by (by100 blast)
        qed
        thus ?thesis using that by (by100 blast)
      qed
      define G_int :: "int set" where "G_int = \<sigma> ` FPZ"
      define \<sigma>_inv :: "int \<Rightarrow> (nat \<times> int) list" where "\<sigma>_inv = inv_into UNIV \<sigma>"
      have h\<sigma>_surj: "surj \<sigma>" using h\<sigma>_bij unfolding bij_def by (by100 blast)
      have h\<sigma>_inj: "inj \<sigma>" using h\<sigma>_bij unfolding bij_def by (by100 blast)
      have h\<sigma>_inv: "\<And>x. \<sigma> (\<sigma>_inv x) = x"
        unfolding \<sigma>_inv_def using h\<sigma>_surj surj_f_inv_f
        by (by100 fastforce)
      have h\<sigma>_inv2: "\<And>x. \<sigma>_inv (\<sigma> x) = x"
        unfolding \<sigma>_inv_def using h\<sigma>_inj inv_into_f_f
        by (by100 fastforce)
      define mul_int :: "int \<Rightarrow> int \<Rightarrow> int" where "mul_int = (\<lambda>a b. \<sigma> (mulFPZ (\<sigma>_inv a) (\<sigma>_inv b)))"
      define e_int :: int where "e_int = \<sigma> eFPZ"
      define invg_int :: "int \<Rightarrow> int" where "invg_int = (\<lambda>a. \<sigma> (invgFPZ (\<sigma>_inv a)))"
      define \<iota>_int :: "nat \<Rightarrow> int" where "\<iota>_int = (\<lambda>s. \<sigma> (\<iota>Z s))"
      \<comment> \<open>First prove G_int is a group (needed for both free group and isomorphism proofs).\<close>
      have he_FPZ: "eFPZ \<in> FPZ" using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
      have hmul_FPZ: "\<And>a b. a \<in> FPZ \<Longrightarrow> b \<in> FPZ \<Longrightarrow> mulFPZ a b \<in> FPZ"
        using hFPZ_grp by (rule group_mul_closed)
      have hinv_FPZ: "\<And>a. a \<in> FPZ \<Longrightarrow> invgFPZ a \<in> FPZ"
        using hFPZ_grp by (rule group_inv_closed)
      have hmul_transport: "\<And>a b. a \<in> FPZ \<Longrightarrow> b \<in> FPZ \<Longrightarrow>
          mul_int (\<sigma> a) (\<sigma> b) = \<sigma> (mulFPZ a b)"
        unfolding mul_int_def using h\<sigma>_inv2 by (by100 simp)
      have hinvg_transport: "\<And>a. a \<in> FPZ \<Longrightarrow>
          invg_int (\<sigma> a) = \<sigma> (invgFPZ a)"
        unfolding invg_int_def using h\<sigma>_inv2 by (by100 simp)
      have hG_int_grp: "top1_is_group_on G_int mul_int e_int invg_int"
      proof -
        have hassoc_FPZ: "\<And>a b c. a \<in> FPZ \<Longrightarrow> b \<in> FPZ \<Longrightarrow> c \<in> FPZ \<Longrightarrow>
            mulFPZ (mulFPZ a b) c = mulFPZ a (mulFPZ b c)"
          using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
        have hid_FPZ: "\<And>a. a \<in> FPZ \<Longrightarrow> mulFPZ eFPZ a = a \<and> mulFPZ a eFPZ = a"
          using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
        have hinvlaw_FPZ: "\<And>a. a \<in> FPZ \<Longrightarrow> mulFPZ (invgFPZ a) a = eFPZ \<and> mulFPZ a (invgFPZ a) = eFPZ"
          using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
        show ?thesis unfolding top1_is_group_on_def
        proof (intro conjI)
          show "e_int \<in> G_int" unfolding G_int_def e_int_def using he_FPZ by (by100 blast)
        next
          show "\<forall>x\<in>G_int. \<forall>y\<in>G_int. mul_int x y \<in> G_int"
          proof (intro ballI)
            fix x y assume hx: "x \<in> G_int" and hy: "y \<in> G_int"
            obtain x' where hx': "x' \<in> FPZ" "x = \<sigma> x'" using hx unfolding G_int_def by (by100 blast)
            obtain y' where hy': "y' \<in> FPZ" "y = \<sigma> y'" using hy unfolding G_int_def by (by100 blast)
            have "mul_int x y = \<sigma> (mulFPZ x' y')" using hmul_transport[OF hx'(1) hy'(1)] hx'(2) hy'(2) by (by100 simp)
            thus "mul_int x y \<in> G_int" unfolding G_int_def using hmul_FPZ[OF hx'(1) hy'(1)] by (by100 blast)
          qed
        next
          show "\<forall>x\<in>G_int. invg_int x \<in> G_int"
          proof (intro ballI)
            fix x assume hx: "x \<in> G_int"
            obtain x' where hx': "x' \<in> FPZ" "x = \<sigma> x'" using hx unfolding G_int_def by (by100 blast)
            have "invg_int x = \<sigma> (invgFPZ x')" using hinvg_transport[OF hx'(1)] hx'(2) by (by100 simp)
            thus "invg_int x \<in> G_int" unfolding G_int_def using hinv_FPZ[OF hx'(1)] by (by100 blast)
          qed
        next
          show "\<forall>x\<in>G_int. \<forall>y\<in>G_int. \<forall>z\<in>G_int.
              mul_int (mul_int x y) z = mul_int x (mul_int y z)"
          proof (intro ballI)
            fix x y z assume hx: "x \<in> G_int" and hy: "y \<in> G_int" and hz: "z \<in> G_int"
            obtain x' where hx': "x' \<in> FPZ" "x = \<sigma> x'" using hx unfolding G_int_def by (by100 blast)
            obtain y' where hy': "y' \<in> FPZ" "y = \<sigma> y'" using hy unfolding G_int_def by (by100 blast)
            obtain z' where hz': "z' \<in> FPZ" "z = \<sigma> z'" using hz unfolding G_int_def by (by100 blast)
            have hxy: "mulFPZ x' y' \<in> FPZ" by (rule hmul_FPZ[OF hx'(1) hy'(1)])
            have hyz: "mulFPZ y' z' \<in> FPZ" by (rule hmul_FPZ[OF hy'(1) hz'(1)])
            show "mul_int (mul_int x y) z = mul_int x (mul_int y z)"
              unfolding mul_int_def hx'(2) hy'(2) hz'(2)
              using h\<sigma>_inv2 hassoc_FPZ[OF hx'(1) hy'(1) hz'(1)] by (by100 simp)
          qed
        next
          show "\<forall>x\<in>G_int. mul_int e_int x = x \<and> mul_int x e_int = x"
          proof (intro ballI)
            fix x assume hx: "x \<in> G_int"
            obtain x' where hx': "x' \<in> FPZ" "x = \<sigma> x'" using hx unfolding G_int_def by (by100 blast)
            show "mul_int e_int x = x \<and> mul_int x e_int = x"
              unfolding mul_int_def e_int_def hx'(2) using h\<sigma>_inv2 hid_FPZ[OF hx'(1)] by (by100 simp)
          qed
        next
          show "\<forall>x\<in>G_int. mul_int (invg_int x) x = e_int \<and> mul_int x (invg_int x) = e_int"
          proof (intro ballI)
            fix x assume hx: "x \<in> G_int"
            obtain x' where hx': "x' \<in> FPZ" "x = \<sigma> x'" using hx unfolding G_int_def by (by100 blast)
            have hinvx: "invgFPZ x' \<in> FPZ" by (rule hinv_FPZ[OF hx'(1)])
            show "mul_int (invg_int x) x = e_int \<and> mul_int x (invg_int x) = e_int"
              unfolding mul_int_def invg_int_def e_int_def hx'(2) using h\<sigma>_inv2 hinvlaw_FPZ[OF hx'(1)] by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>Transfer the free group property and isomorphism through \<sigma>.\<close>
      have hG_int_free: "top1_is_free_group_full_on G_int mul_int e_int invg_int \<iota>_int {..<n}"
      proof -
        note hfree = hFPZ_free_n[unfolded top1_is_free_group_full_on_def]
        have h\<iota>Z_in: "\<forall>s\<in>{..<n}. \<iota>Z s \<in> FPZ" using hfree by (by100 blast)
        have h\<iota>Z_inj: "inj_on \<iota>Z {..<n}" using hfree by (by100 blast)
        \<comment> \<open>Condition 1: G_int is a group (already proved).\<close>
        \<comment> \<open>Condition 2: \<iota>_int maps {..<n} into G_int.\<close>
        have h\<iota>_int_in: "\<forall>s\<in>{..<n}. \<iota>_int s \<in> G_int"
        proof (intro ballI)
          fix s assume hs: "s \<in> {..<n}"
          have "\<iota>Z s \<in> FPZ" using h\<iota>Z_in hs by (by100 blast)
          thus "\<iota>_int s \<in> G_int" unfolding \<iota>_int_def G_int_def by (by100 blast)
        qed
        \<comment> \<open>Condition 3: \<iota>_int is injective on {..<n}.\<close>
        have h\<iota>_int_inj: "inj_on \<iota>_int {..<n}"
        proof (rule inj_onI)
          fix s t assume hs: "s \<in> {..<n}" and ht: "t \<in> {..<n}" and heq: "\<iota>_int s = \<iota>_int t"
          have "\<sigma> (\<iota>Z s) = \<sigma> (\<iota>Z t)" using heq unfolding \<iota>_int_def by (by100 simp)
          hence "\<iota>Z s = \<iota>Z t" using h\<sigma>_inj unfolding inj_def by (by100 blast)
          thus "s = t" using h\<iota>Z_inj hs ht unfolding inj_on_def by (by100 blast)
        qed
        \<comment> \<open>Conditions 4 (generation) and 5 (reduced word) transport through \<sigma>.\<close>
        have hgen_FPZ: "FPZ = top1_subgroup_generated_on FPZ mulFPZ eFPZ invgFPZ (\<iota>Z ` {..<n})"
          using hfree by (by100 blast)
        have hred_FPZ: "\<And>ws :: (nat \<times> bool) list. ws \<noteq> [] \<Longrightarrow>
            top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>Z s, b)) ws) \<Longrightarrow>
            (\<forall>i<length ws. fst (ws!i) \<in> {..<n}) \<Longrightarrow>
            top1_group_word_product mulFPZ eFPZ invgFPZ (map (\<lambda>(s, b). (\<iota>Z s, b)) ws) \<noteq> eFPZ"
          using hfree by (by100 blast)
        \<comment> \<open>Generation: G_int = \<sigma>(FPZ) = \<sigma>(generated by \<iota>Z({..<n}))
           = generated by \<sigma>(\<iota>Z({..<n})) = generated by \<iota>_int({..<n}).\<close>
        have hgen_int: "G_int = top1_subgroup_generated_on G_int mul_int e_int invg_int (\<iota>_int ` {..<n})"
        proof (rule antisym)
          have h\<iota>_int_im_sub: "\<iota>_int ` {..<n} \<subseteq> G_int"
            using h\<iota>_int_in by (by100 blast)
          show "top1_subgroup_generated_on G_int mul_int e_int invg_int (\<iota>_int ` {..<n}) \<subseteq> G_int"
            using subgroup_generated_subset[OF hG_int_grp h\<iota>_int_im_sub] .
        next
          show "G_int \<subseteq> top1_subgroup_generated_on G_int mul_int e_int invg_int (\<iota>_int ` {..<n})"
            unfolding top1_subgroup_generated_on_def
          proof (rule Inter_greatest)
            fix H assume hH: "H \<in> {H. \<iota>_int ` {..<n} \<subseteq> H \<and> H \<subseteq> G_int \<and> top1_is_group_on H mul_int e_int invg_int}"
            hence hgens_H: "\<iota>_int ` {..<n} \<subseteq> H" and hH_sub: "H \<subseteq> G_int"
                and hH_grp: "top1_is_group_on H mul_int e_int invg_int"
              by (by100 blast)+
            \<comment> \<open>Define H' = \<sigma>_inv ` H, and show it is a subgroup of FPZ containing \<iota>Z ` {..<n}.\<close>
            define H' where "H' = \<sigma>_inv ` H"
            have hH'_sub_FPZ: "H' \<subseteq> FPZ"
            proof (rule subsetI)
              fix x assume "x \<in> H'"
              then obtain h where hh: "h \<in> H" "x = \<sigma>_inv h" unfolding H'_def by (by100 blast)
              have "h \<in> G_int" using hh(1) hH_sub by (by100 blast)
              then obtain f where hf: "f \<in> FPZ" "h = \<sigma> f" unfolding G_int_def by (by100 blast)
              have "x = \<sigma>_inv (\<sigma> f)" using hh(2) hf(2) by (by100 simp)
              hence "x = f" using h\<sigma>_inv2 by (by100 simp)
              thus "x \<in> FPZ" using hf(1) by (by100 simp)
            qed
            have hgens_H': "\<iota>Z ` {..<n} \<subseteq> H'"
            proof (rule subsetI)
              fix x assume "x \<in> \<iota>Z ` {..<n}"
              then obtain s where hs: "s \<in> {..<n}" "x = \<iota>Z s" by (by100 blast)
              have "\<iota>_int s \<in> H" using hgens_H hs(1) by (by100 blast)
              have "\<sigma>_inv (\<iota>_int s) = \<sigma>_inv (\<sigma> (\<iota>Z s))" unfolding \<iota>_int_def by (by100 simp)
              also have "\<dots> = \<iota>Z s" using h\<sigma>_inv2 by (by100 simp)
              finally have "\<sigma>_inv (\<iota>_int s) = \<iota>Z s" .
              hence "\<iota>Z s \<in> H'" unfolding H'_def using \<open>\<iota>_int s \<in> H\<close> by (by100 force)
              thus "x \<in> H'" using hs(2) by (by100 simp)
            qed
            have hH'_grp: "top1_is_group_on H' mulFPZ eFPZ invgFPZ"
              unfolding top1_is_group_on_def
            proof (intro conjI)
              have he_H: "e_int \<in> H" using hH_grp unfolding top1_is_group_on_def by (by100 blast)
              have "\<sigma>_inv e_int = \<sigma>_inv (\<sigma> eFPZ)" unfolding e_int_def by (by100 simp)
              hence "\<sigma>_inv e_int = eFPZ" using h\<sigma>_inv2 by (by100 simp)
              thus "eFPZ \<in> H'" unfolding H'_def using he_H by (by100 force)
            next
              show "\<forall>x\<in>H'. \<forall>y\<in>H'. mulFPZ x y \<in> H'"
              proof (intro ballI)
                fix x y assume hx: "x \<in> H'" and hy: "y \<in> H'"
                obtain hx0 where hhx: "hx0 \<in> H" "x = \<sigma>_inv hx0" using hx unfolding H'_def by (by100 blast)
                obtain hy0 where hhy: "hy0 \<in> H" "y = \<sigma>_inv hy0" using hy unfolding H'_def by (by100 blast)
                have hx0_G: "hx0 \<in> G_int" using hhx(1) hH_sub by (by100 blast)
                have hy0_G: "hy0 \<in> G_int" using hhy(1) hH_sub by (by100 blast)
                have hmul_H: "mul_int hx0 hy0 \<in> H"
                  using hH_grp hhx(1) hhy(1) unfolding top1_is_group_on_def by (by100 blast)
                obtain x' where hx': "x' \<in> FPZ" "hx0 = \<sigma> x'"
                  using hx0_G unfolding G_int_def by (by100 blast)
                obtain y' where hy': "y' \<in> FPZ" "hy0 = \<sigma> y'"
                  using hy0_G unfolding G_int_def by (by100 blast)
                have "x = x'" using hhx(2) hx'(2) h\<sigma>_inv2 by (by100 simp)
                have "y = y'" using hhy(2) hy'(2) h\<sigma>_inv2 by (by100 simp)
                have "mul_int hx0 hy0 = \<sigma> (mulFPZ x' y')"
                  using hmul_transport[OF hx'(1) hy'(1)] hx'(2) hy'(2) by (by100 simp)
                hence "\<sigma>_inv (mul_int hx0 hy0) = mulFPZ x' y'"
                  using h\<sigma>_inv2 by (by100 simp)
                hence "\<sigma>_inv (mul_int hx0 hy0) = mulFPZ x y"
                  using \<open>x = x'\<close> \<open>y = y'\<close> by (by100 simp)
                thus "mulFPZ x y \<in> H'" unfolding H'_def using hmul_H by (by100 force)
              qed
            next
              show "\<forall>x\<in>H'. invgFPZ x \<in> H'"
              proof (intro ballI)
                fix x assume hx: "x \<in> H'"
                obtain hx0 where hhx: "hx0 \<in> H" "x = \<sigma>_inv hx0" using hx unfolding H'_def by (by100 blast)
                have hx0_G: "hx0 \<in> G_int" using hhx(1) hH_sub by (by100 blast)
                have hinv_H: "invg_int hx0 \<in> H"
                  using hH_grp hhx(1) unfolding top1_is_group_on_def by (by100 blast)
                obtain x' where hx': "x' \<in> FPZ" "hx0 = \<sigma> x'"
                  using hx0_G unfolding G_int_def by (by100 blast)
                have "x = x'" using hhx(2) hx'(2) h\<sigma>_inv2 by (by100 simp)
                have "invg_int hx0 = \<sigma> (invgFPZ x')"
                  using hinvg_transport[OF hx'(1)] hx'(2) by (by100 simp)
                hence "\<sigma>_inv (invg_int hx0) = invgFPZ x'"
                  using h\<sigma>_inv2 by (by100 simp)
                hence "\<sigma>_inv (invg_int hx0) = invgFPZ x"
                  using \<open>x = x'\<close> by (by100 simp)
                thus "invgFPZ x \<in> H'" unfolding H'_def using hinv_H by (by100 force)
              qed
            next
              show "\<forall>x\<in>H'. \<forall>y\<in>H'. \<forall>z\<in>H'. mulFPZ (mulFPZ x y) z = mulFPZ x (mulFPZ y z)"
              proof (intro ballI)
                fix x y z assume "x \<in> H'" "y \<in> H'" "z \<in> H'"
                hence "x \<in> FPZ" "y \<in> FPZ" "z \<in> FPZ" using hH'_sub_FPZ by (by100 blast)+
                thus "mulFPZ (mulFPZ x y) z = mulFPZ x (mulFPZ y z)"
                  using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
              qed
            next
              show "\<forall>x\<in>H'. mulFPZ eFPZ x = x \<and> mulFPZ x eFPZ = x"
              proof (intro ballI)
                fix x assume "x \<in> H'"
                hence "x \<in> FPZ" using hH'_sub_FPZ by (by100 blast)
                thus "mulFPZ eFPZ x = x \<and> mulFPZ x eFPZ = x"
                  using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
              qed
            next
              show "\<forall>x\<in>H'. mulFPZ (invgFPZ x) x = eFPZ \<and> mulFPZ x (invgFPZ x) = eFPZ"
              proof (intro ballI)
                fix x assume "x \<in> H'"
                hence "x \<in> FPZ" using hH'_sub_FPZ by (by100 blast)
                thus "mulFPZ (invgFPZ x) x = eFPZ \<and> mulFPZ x (invgFPZ x) = eFPZ"
                  using hFPZ_grp unfolding top1_is_group_on_def by (by100 blast)
              qed
            qed
            \<comment> \<open>Since FPZ = subgroup_generated by \<iota>Z ` {..<n}, and H' is a subgroup containing those generators,
               FPZ \<subseteq> H'. Therefore G_int = \<sigma> ` FPZ \<subseteq> \<sigma> ` H' = H.\<close>
            have "FPZ \<subseteq> H'"
            proof -
              have "H' \<in> {K. \<iota>Z ` {..<n} \<subseteq> K \<and> K \<subseteq> FPZ \<and> top1_is_group_on K mulFPZ eFPZ invgFPZ}"
                using hgens_H' hH'_sub_FPZ hH'_grp by (by100 blast)
              hence "top1_subgroup_generated_on FPZ mulFPZ eFPZ invgFPZ (\<iota>Z ` {..<n}) \<subseteq> H'"
                unfolding top1_subgroup_generated_on_def by (rule Inter_lower)
              thus ?thesis using hgen_FPZ by (by100 simp)
            qed
            show "G_int \<subseteq> H"
            proof (rule subsetI)
              fix x assume "x \<in> G_int"
              then obtain f where hf: "f \<in> FPZ" "x = \<sigma> f" unfolding G_int_def by (by100 blast)
              have "f \<in> H'" using \<open>FPZ \<subseteq> H'\<close> hf(1) by (by100 blast)
              then obtain h where hh: "h \<in> H" "f = \<sigma>_inv h" unfolding H'_def by (by100 blast)
              have "x = \<sigma> (\<sigma>_inv h)" using hf(2) hh(2) by (by100 simp)
              hence "x = h" using h\<sigma>_inv by (by100 simp)
              thus "x \<in> H" using hh(1) by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Reduced word property: transport through \<sigma>.\<close>
        have hred_int: "\<And>ws :: (nat \<times> bool) list. ws \<noteq> [] \<Longrightarrow>
            top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>_int s, b)) ws) \<Longrightarrow>
            (\<forall>i<length ws. fst (ws!i) \<in> {..<n}) \<Longrightarrow>
            top1_group_word_product mul_int e_int invg_int (map (\<lambda>(s, b). (\<iota>_int s, b)) ws) \<noteq> e_int"
        proof -
          fix ws :: "(nat \<times> bool) list"
          assume hne: "ws \<noteq> []"
              and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>_int s, b)) ws)"
              and hin: "\<forall>i<length ws. fst (ws!i) \<in> {..<n}"
          \<comment> \<open>Key: map (\<lambda>(s,b). (\<iota>_int s, b)) ws = map (\<lambda>(s,b). (\<sigma>(\<iota>Z s), b)) ws.
             Since \<sigma> is injective, the reduced word property on \<iota>_int-words
             is equivalent to the reduced word property on \<iota>Z-words.\<close>
          have hmap_eq: "map (\<lambda>(s, b). (\<iota>_int s, b)) ws = map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ws"
            unfolding \<iota>_int_def by (by100 simp)
          \<comment> \<open>reduced_word(\<iota>_int) \<longleftrightarrow> reduced_word(\<iota>Z) since \<sigma> is injective.\<close>
          have hred_Z: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>Z s, b)) ws)"
          proof -
            \<comment> \<open>top1_is_reduced_word checks that consecutive pairs differ.
               Since \<sigma> is injective, (\<sigma>(\<iota>Z s), b) pairs differ iff (\<iota>Z s, b) pairs differ.\<close>
            have "top1_is_reduced_word (map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ws)"
              using hred hmap_eq by (by100 simp)
            have hred_transfer: "\<And>ws'. top1_is_reduced_word (map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ws')
                \<Longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>Z s, b)) ws')"
            proof -
              fix ws' :: "(nat \<times> bool) list"
              show "top1_is_reduced_word (map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ws')
                  \<Longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>Z s, b)) ws')"
              proof (induction ws' rule: top1_is_reduced_word.induct)
                case 1 thus ?case by (by100 simp)
              next
                case (2 x) thus ?case by (by100 simp)
              next
                case (3 x bx y cy ws'')
                have hpair: "\<sigma> (\<iota>Z x) \<noteq> \<sigma> (\<iota>Z y) \<or> bx = cy"
                  using 3(2) by (by100 simp)
                have hpair': "\<iota>Z x \<noteq> \<iota>Z y \<or> bx = cy"
                proof (cases "bx = cy")
                  case True thus ?thesis by (by100 simp)
                next
                  case False
                  hence "\<sigma> (\<iota>Z x) \<noteq> \<sigma> (\<iota>Z y)" using hpair by (by100 simp)
                  hence "\<iota>Z x \<noteq> \<iota>Z y" using injD[OF h\<sigma>_inj] by (by100 metis)
                  thus ?thesis by (by100 simp)
                qed
                have htail: "top1_is_reduced_word (map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ((y, cy) # ws''))"
                  using 3(2) by (by100 simp)
                have htail': "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>Z s, b)) ((y, cy) # ws''))"
                  using 3(1)[OF htail] .
                show ?case using hpair' htail' by (by100 simp)
              qed
            qed
            from this[OF \<open>top1_is_reduced_word (map (\<lambda>(s, b). (\<sigma> (\<iota>Z s), b)) ws)\<close>]
            show ?thesis .
          qed
          have hprod_ne: "top1_group_word_product mulFPZ eFPZ invgFPZ
              (map (\<lambda>(s, b). (\<iota>Z s, b)) ws) \<noteq> eFPZ"
            using hred_FPZ[OF hne hred_Z hin] .
          \<comment> \<open>The word product with \<iota>_int = \<sigma> \<circ> \<iota>Z and mul_int = \<sigma> \<circ> mulFPZ \<circ> (\<sigma>\<inverse> \<times> \<sigma>\<inverse>)
             equals \<sigma>(word product with \<iota>Z and mulFPZ).\<close>
          have hprod_transport: "top1_group_word_product mul_int e_int invg_int
              (map (\<lambda>(s, b). (\<iota>_int s, b)) ws) =
              \<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ (map (\<lambda>(s, b). (\<iota>Z s, b)) ws))"
          proof -
            have haux: "\<And>ws'. top1_group_word_product mul_int e_int invg_int
                (map (\<lambda>(s, b). (\<iota>_int s, b)) ws') =
                \<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'))"
            proof -
              fix ws' :: "(nat \<times> bool) list"
              show "top1_group_word_product mul_int e_int invg_int
                  (map (\<lambda>(s, b). (\<iota>_int s, b)) ws') =
                  \<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'))"
              proof (induction ws')
                case Nil
                show ?case unfolding e_int_def by (by100 simp)
              next
                case (Cons a ws'')
                obtain s b where ha: "a = (s, b)" by (cases a)
                show ?case
                proof (cases b)
                  case True
                  have "top1_group_word_product mul_int e_int invg_int
                      (map (\<lambda>(s, b). (\<iota>_int s, b)) (a # ws''))
                      = mul_int (\<iota>_int s) (top1_group_word_product mul_int e_int invg_int
                          (map (\<lambda>(s, b). (\<iota>_int s, b)) ws''))"
                    using ha True by (by100 simp)
                  also have "\<dots> = mul_int (\<iota>_int s)
                      (\<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ
                          (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'')))"
                    using Cons.IH by (by100 simp)
                  also have "\<dots> = \<sigma> (mulFPZ (\<iota>Z s)
                      (top1_group_word_product mulFPZ eFPZ invgFPZ
                          (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'')))"
                    unfolding mul_int_def \<iota>_int_def using h\<sigma>_inv2 by (by100 simp)
                  also have "\<dots> = \<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ
                      (map (\<lambda>(s, b). (\<iota>Z s, b)) (a # ws'')))"
                    using ha True by (by100 simp)
                  finally show ?thesis .
                next
                  case False
                  have "top1_group_word_product mul_int e_int invg_int
                      (map (\<lambda>(s, b). (\<iota>_int s, b)) (a # ws''))
                      = mul_int (invg_int (\<iota>_int s)) (top1_group_word_product mul_int e_int invg_int
                          (map (\<lambda>(s, b). (\<iota>_int s, b)) ws''))"
                    using ha False by (by100 simp)
                  also have "\<dots> = mul_int (invg_int (\<iota>_int s))
                      (\<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ
                          (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'')))"
                    using Cons.IH by (by100 simp)
                  also have "\<dots> = \<sigma> (mulFPZ (invgFPZ (\<iota>Z s))
                      (top1_group_word_product mulFPZ eFPZ invgFPZ
                          (map (\<lambda>(s, b). (\<iota>Z s, b)) ws'')))"
                    unfolding mul_int_def invg_int_def \<iota>_int_def using h\<sigma>_inv2 by (by100 simp)
                  also have "\<dots> = \<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ
                      (map (\<lambda>(s, b). (\<iota>Z s, b)) (a # ws'')))"
                    using ha False by (by100 simp)
                  finally show ?thesis .
                qed
              qed
            qed
            show ?thesis using haux[of ws] .
          qed
          show "top1_group_word_product mul_int e_int invg_int
              (map (\<lambda>(s, b). (\<iota>_int s, b)) ws) \<noteq> e_int"
          proof
            assume "top1_group_word_product mul_int e_int invg_int
                (map (\<lambda>(s, b). (\<iota>_int s, b)) ws) = e_int"
            hence "\<sigma> (top1_group_word_product mulFPZ eFPZ invgFPZ
                (map (\<lambda>(s, b). (\<iota>Z s, b)) ws)) = \<sigma> eFPZ"
              using hprod_transport unfolding e_int_def by (by100 simp)
            hence "top1_group_word_product mulFPZ eFPZ invgFPZ
                (map (\<lambda>(s, b). (\<iota>Z s, b)) ws) = eFPZ"
              using h\<sigma>_inj unfolding inj_def by (by100 blast)
            thus False using hprod_ne by (by100 simp)
          qed
        qed
        show ?thesis unfolding top1_is_free_group_full_on_def
          using hG_int_grp h\<iota>_int_in h\<iota>_int_inj hgen_int hred_int by (by100 blast)
      qed
      have hG_int_iso: "top1_groups_isomorphic_on G_int mul_int
          (top1_fundamental_group_carrier X TX p)
          (top1_fundamental_group_mul X TX p)"
      proof -
        \<comment> \<open>\<sigma>: FPZ \<rightarrow> G_int is an isomorphism by construction.\<close>
        have h\<sigma>_hom: "top1_group_hom_on FPZ mulFPZ G_int mul_int \<sigma>"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> FPZ"
          thus "\<sigma> x \<in> G_int" unfolding G_int_def by (by100 blast)
        next
          fix x y assume hx: "x \<in> FPZ" and hy: "y \<in> FPZ"
          show "\<sigma> (mulFPZ x y) = mul_int (\<sigma> x) (\<sigma> y)"
            unfolding mul_int_def using h\<sigma>_inv2 by (by100 simp)
        qed
        have h\<sigma>_bij_betw: "bij_betw \<sigma> FPZ G_int"
          unfolding bij_betw_def G_int_def
        proof (intro conjI)
          show "inj_on \<sigma> FPZ" using h\<sigma>_inj unfolding inj_on_def by (by100 blast)
        next
          show "\<sigma> ` FPZ = \<sigma> ` FPZ" by (by100 blast)
        qed
        have h\<sigma>_iso: "top1_groups_isomorphic_on FPZ mulFPZ G_int mul_int"
          unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
          using h\<sigma>_hom h\<sigma>_bij_betw by (by100 blast)
        have h\<sigma>_iso_rev: "top1_groups_isomorphic_on G_int mul_int FPZ mulFPZ"
          by (rule top1_groups_isomorphic_on_sym[OF h\<sigma>_iso hFPZ_grp hG_int_grp])
        show ?thesis by (rule groups_isomorphic_trans_fwd[OF h\<sigma>_iso_rev hFPZ_iso_piX])
      qed
      show ?thesis using hG_int_free hG_int_iso by (by100 blast)
    qed
    show "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
      using hfinal by (by100 blast)
  qed
  show ?case
  proof -
    have "n = 1 \<or> n \<ge> 2" using hn_pos by (by100 linarith)
    thus ?case using hbase1 hstep by (by100 blast)
  qed
qed

text \<open>Lemma 60.5 (Munkres): The fundamental group of the figure eight is not abelian.\<close>
lemma Lemma_60_5_figure_eight_not_abelian:
  assumes "is_topology_on X TX"
      and "top1_is_wedge_of_circles_on X TX {0::nat, 1} p"
  shows "\<not> (\<forall>a\<in>top1_fundamental_group_carrier X TX p.
             \<forall>b\<in>top1_fundamental_group_carrier X TX p.
               top1_fundamental_group_mul X TX p a b = top1_fundamental_group_mul X TX p b a)"
proof -
  \<comment> \<open>By Theorem 71.1: \<pi>_1(X,p) \<cong> free group on {0,1} (= {..<2}).\<close>
  have "{0::nat, 1} = {..<(2::nat)}" by (by100 auto)
  hence hwedge2: "top1_is_wedge_of_circles_on X TX {..<(2::nat)} p" using assms(2) by (by100 simp)
  from Theorem_71_1_wedge_of_circles_finite[OF hwedge2]
  obtain G :: "int set" and mul :: "int \<Rightarrow> int \<Rightarrow> int"
      and e :: int and invg :: "int \<Rightarrow> int" and \<iota> :: "nat \<Rightarrow> int" where
      hfree: "top1_is_free_group_full_on G mul e invg \<iota> {..<2::nat}"
      and hiso: "top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX p)
          (top1_fundamental_group_mul X TX p)"
    by (by100 blast)
  \<comment> \<open>In the free group on 2 generators, the commutator word [(0,T),(1,T),(0,F),(1,F)] is
     reduced and non-empty, hence evaluates to non-identity. This means \<iota>(0)\<cdot>\<iota>(1) \<noteq> \<iota>(1)\<cdot>\<iota>(0).\<close>
  have hG_not_abelian: "\<not> (\<forall>a\<in>G. \<forall>b\<in>G. mul a b = mul b a)"
  proof
    assume habel: "\<forall>a\<in>G. \<forall>b\<in>G. mul a b = mul b a"
    note hfr = hfree[unfolded top1_is_free_group_full_on_def]
    have hG_grp: "top1_is_group_on G mul e invg" using hfr[THEN conjunct1] .
    note h\<iota>_in = hfr[THEN conjunct2, THEN conjunct1]
    have h\<iota>0: "\<iota> 0 \<in> G" using h\<iota>_in by (by100 force)
    have h\<iota>1: "\<iota> 1 \<in> G" using h\<iota>_in by (by100 force)
    note h\<iota>_inj = hfr[THEN conjunct2, THEN conjunct2, THEN conjunct1]
    hence h01_ne: "\<iota> 0 \<noteq> \<iota> 1" unfolding inj_on_def by (by100 force)
    \<comment> \<open>Commutator = e under abelian assumption.\<close>
    have hcomm: "mul (\<iota> 0) (mul (\<iota> 1) (mul (invg (\<iota> 0)) (invg (\<iota> 1)))) = e"
    proof -
      let ?a = "\<iota> 0" and ?b = "\<iota> 1"
      have hab: "mul ?a ?b = mul ?b ?a" using habel h\<iota>0 h\<iota>1 by (by100 blast)
      have hinva: "invg ?a \<in> G" by (rule group_inv_closed[OF hG_grp h\<iota>0])
      have hinvb: "invg ?b \<in> G" by (rule group_inv_closed[OF hG_grp h\<iota>1])
      have hab_G: "mul ?a ?b \<in> G" by (rule group_mul_closed[OF hG_grp h\<iota>0 h\<iota>1])
      \<comment> \<open>a \<cdot> (b \<cdot> (a\<inverse> \<cdot> b\<inverse>)) = a \<cdot> (b \<cdot> a\<inverse>) \<cdot> b\<inverse> = a \<cdot> (a\<inverse> \<cdot> b) \<cdot> b\<inverse> (using ab=ba \<Rightarrow> ba\<inverse> = a\<inverse>b)...\<close>
      \<comment> \<open>Simpler: aba\<inverse>b\<inverse> = a(ba\<inverse>)b\<inverse>. Since ab=ba, ba\<inverse> = a\<inverse>b (from ab=ba \<Rightarrow> a\<inverse>ba = b \<Rightarrow> ba\<inverse> = ...).
         Actually, simpler still: a(b(a\<inverse>(b\<inverse>))) = (ab)(a\<inverse>b\<inverse>) = (ab)((ab)\<inverse>) = e.
         Since inv(ab) = inv(b)\<cdot>inv(a) = inv(a)\<cdot>inv(b) (abelian), and (ab)(inv(a)inv(b)) = e.\<close>
      note hinvmul = group_inv_mul[OF hG_grp h\<iota>0 h\<iota>1]
      have "mul (invg ?b) (invg ?a) = invg (mul ?a ?b)"
        using hinvmul by (by100 simp)
      moreover have "mul (invg ?a) (invg ?b) = mul (invg ?b) (invg ?a)"
        using habel hinva hinvb by (by100 blast)
      ultimately have hinvab: "mul (invg ?a) (invg ?b) = invg (mul ?a ?b)" by (by100 simp)
      have "mul ?a (mul ?b (mul (invg ?a) (invg ?b)))
          = mul ?a (mul ?b (invg (mul ?a ?b)))" using hinvab by (by100 simp)
      also have "\<dots> = mul (mul ?a ?b) (invg (mul ?a ?b))"
      proof -
        have hinvab_G: "invg (mul ?a ?b) \<in> G" by (rule group_inv_closed[OF hG_grp hab_G])
        have "mul ?b (invg (mul ?a ?b)) \<in> G" by (rule group_mul_closed[OF hG_grp h\<iota>1 hinvab_G])
        have "mul ?a (mul ?b (invg (mul ?a ?b)))
            = mul (mul ?a ?b) (invg (mul ?a ?b))"
          using group_assoc[OF hG_grp h\<iota>0 h\<iota>1 hinvab_G, symmetric] .
        thus ?thesis .
      qed
      finally have "mul (\<iota> 0) (mul (\<iota> 1) (mul (invg (\<iota> 0)) (invg (\<iota> 1))))
          = mul (mul ?a ?b) (invg (mul ?a ?b))" .
      also have "\<dots> = e" by (rule group_inv_right[OF hG_grp hab_G])
      finally show ?thesis .
    qed
    \<comment> \<open>But the commutator word is reduced and non-empty \<Rightarrow> word product \<noteq> e.\<close>
    let ?ws = "[(0::nat, True), (1::nat, True), (0, False), (1, False)]"
    have hws_ne: "?ws \<noteq> []" by (by100 simp)
    have hws_S: "\<forall>i<length ?ws. fst (?ws!i) \<in> {..<2::nat}"
      by (intro allI impI, simp add: nth_Cons' split: nat.splits)
    have hws_red: "top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ?ws)"
      using h01_ne by (by100 simp)
    have "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws) \<noteq> e"
      using hfree hws_ne hws_red hws_S unfolding top1_is_free_group_full_on_def by (by100 blast)
    \<comment> \<open>Word product = commutator.\<close>
    have hwp_unfold: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws)
        = mul (\<iota> 0) (mul (\<iota> 1) (mul (invg (\<iota> 0)) (mul (invg (\<iota> 1)) e)))"
      by (by100 simp)
    have hid_inv1: "mul (invg (\<iota> 1)) e = invg (\<iota> 1)"
      by (rule group_id_right[OF hG_grp]) (rule group_inv_closed[OF hG_grp h\<iota>1])
    have hwp_eq: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws)
        = mul (\<iota> 0) (mul (\<iota> 1) (mul (invg (\<iota> 0)) (invg (\<iota> 1))))"
      using hwp_unfold hid_inv1 by (by100 simp)
    moreover note \<open>top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws) \<noteq> e\<close>
    ultimately have "mul (\<iota> 0) (mul (\<iota> 1) (mul (invg (\<iota> 0)) (invg (\<iota> 1)))) \<noteq> e" by (by100 simp)
    thus False using hcomm by (by100 blast)
  qed
  \<comment> \<open>Transfer via isomorphism: G non-abelian + G \<cong> \<pi>_1(X) \<Rightarrow> \<pi>_1(X) non-abelian.\<close>
  \<comment> \<open>Transfer: G non-abelian + G \<cong> \<pi>_1(X) \<Rightarrow> \<pi>_1(X) non-abelian.\<close>
  obtain f where hf_bij: "bij_betw f G (top1_fundamental_group_carrier X TX p)"
      and hf_hom: "\<forall>a\<in>G. \<forall>b\<in>G. f (mul a b) = top1_fundamental_group_mul X TX p (f a) (f b)"
    using hiso unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def top1_group_hom_on_def
    by (by100 blast)
  from hG_not_abelian obtain a b where ha: "a \<in> G" and hb: "b \<in> G"
      and hab: "mul a b \<noteq> mul b a" by (by100 blast)
  have "f (mul a b) \<noteq> f (mul b a)"
  proof -
    have hG_grp: "top1_is_group_on G mul e invg"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    have "mul a b \<in> G" using hG_grp ha hb unfolding top1_is_group_on_def by (by100 blast)
    moreover have "mul b a \<in> G" using hG_grp ha hb unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis using hab \<open>inj_on f G\<close> unfolding inj_on_def by (by100 blast)
  qed
  hence "top1_fundamental_group_mul X TX p (f a) (f b) \<noteq>
         top1_fundamental_group_mul X TX p (f b) (f a)"
    using hf_hom ha hb by (by100 simp)
  moreover have "f a \<in> top1_fundamental_group_carrier X TX p"
    using hf_bij ha unfolding bij_betw_def by (by100 blast)
  moreover have "f b \<in> top1_fundamental_group_carrier X TX p"
    using hf_bij hb unfolding bij_betw_def by (by100 blast)
  ultimately show ?thesis by (by100 blast)
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
  \<comment> \<open>Step 1: For each finite F \<subseteq> J, the sub-wedge X_F has free \<pi>_1 on F
     (by Theorem 71.1 for finite wedges).\<close>
  \<comment> \<open>Step 2: The inclusions X_F \<hookrightarrow> X_G for F \<subseteq> G give a directed system.
     The direct limit of free groups on finite subsets = free group on J.\<close>
  \<comment> \<open>Step 3: \<pi>_1(X) = direct limit of \<pi>_1(X_F) by the weak topology on X
     (a loop in X is compact, hence contained in some finite sub-wedge).\<close>
  show ?thesis sorry \<comment> \<open>Direct limit argument: finite sub-wedges (Thm 71.1) + compactness of loops.\<close>
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
  \<comment> \<open>Step 1: The torus is the quotient of the square by scheme aba\<inverse>b\<inverse>. Extract the
     attaching data: 1-skeleton A (wedge of 2 circles), attaching map h: B² \<rightarrow> T.\<close>
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_sub: "closedin_on T_torus TT A"
      and hA_wedge: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {0::nat, 1} x0"
      and hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology T_torus TT h"
      and hh_S1_A: "h ` top1_S1 \<subseteq> A"
    sorry \<comment> \<open>From torus definition: quotient of square by aba\<inverse>b\<inverse>. 1-skeleton = wedge of 2 circles.\<close>
  \<comment> \<open>Step 2: By Theorem 72.1, \<pi>_1(T) \<cong> \<pi>_1(A)/\<langle>\<langle>k_*([p])\<rangle>\<rangle> where k = h|_{S¹}.
     \<pi>_1(A) is free on {a, b}. The relator is aba\<inverse>b\<inverse>.\<close>
  have hA_free: "\<exists>(F::'g set) mulF eF invgF (\<iota>F::nat \<Rightarrow> 'g).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F {0::nat, 1}
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
          (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
    sorry \<comment> \<open>\<pi>_1 of wedge of 2 circles is free on 2 generators (Theorem 71.1).\<close>
  \<comment> \<open>Step 3: The quotient F({a,b})/\<langle>\<langle>aba\<inverse>b\<inverse>\<rangle>\<rangle>: since aba\<inverse>b\<inverse>=1 means ab=ba,
     the quotient is the free abelian group on {a,b}, which is Z \<times> Z.\<close>
  have hquotient_ZZ: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier T_torus TT x0)
      (top1_fundamental_group_mul T_torus TT x0)
      (UNIV::(int \<times> int) set) (\<lambda>(a1,a2) (b1,b2). (a1+b1, a2+b2))"
    sorry \<comment> \<open>Theorem 72.1 + abelianization: F(a,b)/\<langle>\<langle>[a,b]\<rangle>\<rangle> \<cong> Z\<times>Z.\<close>
  show ?thesis by (rule hquotient_ZZ)
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
  \<comment> \<open>Step 1: The dunce cap has 1-skeleton A = single circle (\<cong> S¹).
     The attaching map wraps S¹ n times around A.\<close>
  obtain A :: "'a set" and h :: "real \<times> real \<Rightarrow> 'a"
    where hA_circle: "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
             A (subspace_topology X TX A) f"
      and hh_att: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and hh_wrap: "\<forall>s\<in>I_set. h (cos (2*pi*s), sin (2*pi*s)) = h (cos (2*pi*n*s), sin (2*pi*n*s))"
    sorry \<comment> \<open>From dunce cap definition: quotient of B² by n-fold rotation on S¹.\<close>
  \<comment> \<open>Step 2: \<pi>_1(A) \<cong> Z (fundamental group of circle).\<close>
  have hA_Z: "\<exists>f. top1_group_iso_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (UNIV::int set) (\<lambda>a b. a + b) f"
    sorry \<comment> \<open>\<pi>_1(S¹) \<cong> Z (Theorem 54.5/55.1).\<close>
  \<comment> \<open>Step 3: By Theorem 72.1, \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.
     The relator is aⁿ (the standard loop wrapped n times).\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + Z/\<langle>\<langle>n\<rangle>\<rangle> \<cong> Z/nZ.\<close>
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
    fix F' assume hF'1: "F' \<subseteq> \<U>" and hF'2: "finite F'" and hF'3: "B \<subseteq> \<Union>F'"
    show thesis by (rule that[OF hF'2 hF'1 hF'3])
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
  have hSC_open: "open (- C)" using assms(2) unfolding closed_def by blast
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

text \<open>Cone superset: cone(conv n, v_n) \<subseteq> conv(Suc n).\<close>
lemma convex_hull_cone_sup:
  fixes vx vy :: "nat \<Rightarrow> real"
  shows "(\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})
    \<subseteq> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
proof (rule subsetI)
  fix q assume hq_mem: "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  then obtain p where hp: "p \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
      \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      and hq: "q = (case p of (t, x', y') \<Rightarrow> ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
    by (by100 blast)
  obtain t r where htr: "p = (t, r)" "t \<in> {0..1}" by (cases p) (use hp in \<open>(by100 auto)\<close>)
  obtain x' y' where hr: "r = (x', y')" by (cases r)
  have ht: "0 \<le> t" "t \<le> 1" using htr(2) by (by100 auto)+
  have hq_eq: "q = ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n)"
    using hq htr(1) hr by (by100 simp)
  obtain c' where hc': "\<forall>i<n. (0::real) \<le> c' i" "(\<Sum>i<n. c' i) = 1"
      "x' = (\<Sum>i<n. c' i * vx i)" "y' = (\<Sum>i<n. c' i * vy i)"
    using hp htr(1) hr by (by100 blast)
  let ?c = "\<lambda>i. if i < n then (1-t) * c' i else if i = n then t else 0 :: real"
  have hc_nn: "\<forall>i<Suc n. 0 \<le> ?c i" using ht hc'(1) by (by100 force)
  have hc_sum: "(\<Sum>i<Suc n. ?c i) = 1"
  proof -
    have "(\<Sum>i<n. ?c i) = (\<Sum>i<n. (1-t) * c' i)" by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t)" using hc'(2) by (simp add: sum_distrib_left[symmetric])
    finally show ?thesis by (by100 simp)
  qed
  have hc_x: "(\<Sum>i<Suc n. ?c i * vx i) = (1-t)*x' + t*vx n"
  proof -
    have "(\<Sum>i<n. ?c i * vx i) = (\<Sum>i<n. (1-t) * c' i * vx i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * x'" using hc'(3) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  have hc_y: "(\<Sum>i<Suc n. ?c i * vy i) = (1-t)*y' + t*vy n"
  proof -
    have "(\<Sum>i<n. ?c i * vy i) = (\<Sum>i<n. (1-t) * c' i * vy i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * y'" using hc'(4) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  show "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
    unfolding hq_eq
    apply simp
    apply (rule_tac x="?c" in exI)
    using hc_nn hc_sum hc_x hc_y by (by100 force)
qed

text \<open>Cone subset: conv(Suc n) \<subseteq> cone(conv n, v_n).\<close>
lemma convex_hull_cone_sub:
  fixes vx vy :: "nat \<Rightarrow> real"
  assumes "n \<ge> 1"
  shows "{(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}
    \<subseteq> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
proof (rule subsetI)
  fix q assume "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
  then obtain x y c where hq: "q = (x, y)"
      and hc: "\<forall>i<Suc n. (0::real) \<le> c i" "(\<Sum>i<Suc n. c i) = 1"
      "x = (\<Sum>i<Suc n. c i * vx i)" "y = (\<Sum>i<Suc n. c i * vy i)"
    by (by100 blast)
  let ?t = "c n"
  have ht0: "0 \<le> ?t" using hc(1) by (by100 force)
  have ht1: "?t \<le> 1"
    by (rule order_trans[OF member_le_sum[of n "{..<Suc n}" c]]) (use hc in auto)
  show "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  proof (cases "?t = 1")
    case True
    have hsum0: "(\<Sum>i<n. c i) = 0" using hc(2) True by simp
    have hall0: "\<forall>i<n. c i = 0"
    proof (intro allI impI)
      fix i assume "i < n"
      have "c i \<le> (\<Sum>i<n. c i)" by (rule member_le_sum) (use hc(1) \<open>i<n\<close> in auto)
      moreover have "0 \<le> c i" using hc(1) \<open>i<n\<close> by (by100 force)
      ultimately show "c i = 0" using hsum0 by (by100 linarith)
    qed
    have hx_vn: "x = vx n" using hc(3) hall0 True by simp
    have hy_vn: "y = vy n" using hc(4) hall0 True by simp
    \<comment> \<open>n \<ge> 1 (from induction hypothesis), so Pn is non-empty: (vx 0, vy 0) \<in> Pn.\<close>
    have hn1: "n \<ge> 1" using assms .
    let ?d = "\<lambda>i::nat. if i = 0 then 1::real else 0"
    have "(vx 0, vy 0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?d" in exI)
    proof (intro conjI allI impI)
      fix i :: nat assume "i < n" thus "0 \<le> ?d i" by (by100 simp)
    next
      show "(\<Sum>i<n. ?d i) = 1" using hn1 by simp
    next
      show "vx 0 = (\<Sum>i<n. ?d i * vx i)"
      proof -
        have "(\<Sum>i<n. ?d i * vx i) = ?d 0 * vx 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vx i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vx i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    next
      show "vy 0 = (\<Sum>i<n. ?d i * vy i)"
      proof -
        have "(\<Sum>i<n. ?d i * vy i) = ?d 0 * vy 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vy i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vy i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    qed
    hence hpn_ne: "\<exists>p'. p' \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    then obtain x0 y0 where hxy0: "(x0, y0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    have "(1::real, (x0, y0)) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using hxy0 by (by100 auto)
    moreover have "q = (case (1::real, (x0, y0)) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_vn hy_vn by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  next
    case htnot1: False
    have hlt1: "?t < 1" using htnot1 ht1 by (by100 linarith)
    hence h1mt: "1 - ?t > 0" by (by100 linarith)
    let ?c' = "\<lambda>i. c i / (1 - ?t)"
    have hc'_nn: "\<forall>i<n. ?c' i \<ge> 0" using hc(1) h1mt by (by100 force)
    have hc'_sum: "(\<Sum>i<n. ?c' i) = 1"
    proof -
      have "(\<Sum>i<n. ?c' i) = (\<Sum>i<n. c i) / (1 - ?t)"
        by (simp add: sum_divide_distrib)
      also have "(\<Sum>i<n. c i) = 1 - ?t" using hc(2) by simp
      finally show ?thesis using h1mt by simp
    qed
    let ?x' = "\<Sum>i<n. ?c' i * vx i"
    let ?y' = "\<Sum>i<n. ?c' i * vy i"
    have hrescale_x: "(1-?t)*?x' = (\<Sum>i<n. c i * vx i)"
    proof -
      have "(1-?t)*?x' = (\<Sum>i<n. (1-?t) * (?c' i * vx i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vx i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hrescale_y: "(1-?t)*?y' = (\<Sum>i<n. c i * vy i)"
    proof -
      have "(1-?t)*?y' = (\<Sum>i<n. (1-?t) * (?c' i * vy i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vy i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hx_eq: "x = (1-?t)*?x' + ?t*vx n" using hc(3) hrescale_x by simp
    have hy_eq: "y = (1-?t)*?y' + ?t*vy n" using hc(4) hrescale_y by simp
    have "(?x', ?y') \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?c'" in exI)
      using hc'_nn hc'_sum by (by100 auto)
    have ht_in: "?t \<in> {0..1}" using ht0 ht1 by (by100 auto)
    hence "(?t, (?x', ?y')) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using \<open>(?x', ?y') \<in> _\<close> by (by100 blast)
    moreover have "q = (case (?t, (?x', ?y')) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_eq hy_eq by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
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
    by (rule equalityI[OF convex_hull_cone_sub[OF Suc(1)] convex_hull_cone_sup])
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
  \<comment> \<open>Step 1: T_n is a polygonal quotient of a 4n-gon. Extract the scheme.\<close>
  have h_poly: "top1_is_polygonal_quotient_on X TX"
    using assms(1) sorry \<comment> \<open>n-fold torus is a polygonal quotient.\<close>
  \<comment> \<open>Step 2: The 4n-gon's 1-skeleton after identifications is a wedge of 2n circles.\<close>
  have h_skel: "\<exists>A. closedin_on X TX A \<and>
      top1_is_wedge_of_circles_on A (subspace_topology X TX A) {..<2*n} x0"
    sorry \<comment> \<open>1-skeleton of 4n-gon with torus scheme = wedge of 2n circles.\<close>
  \<comment> \<open>Step 3: Apply Theorem 72.1. The attaching map h: B² \<rightarrow> X wraps S¹ around
     the 1-skeleton via the word [a₁,b₁]...[aₙ,bₙ].
     Theorem 72.1 gives: \<pi>_1(X) \<cong> \<pi>_1(1-skel)/N(relator).\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + presentation by relator [a₁,b₁]...[aₙ,bₙ].\<close>
qed

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1² \<cdots> a_m²\<rangle>.
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
  \<comment> \<open>Step 1: P_m is a polygonal quotient of a 2m-gon with projective scheme.\<close>
  have h_poly: "top1_is_polygonal_quotient_on X TX"
    using assms(1) sorry \<comment> \<open>m-fold projective plane is a polygonal quotient.\<close>
  \<comment> \<open>Step 2: The 2m-gon's 1-skeleton after identifications is a wedge of m circles.\<close>
  have h_skel: "\<exists>A. closedin_on X TX A \<and>
      top1_is_wedge_of_circles_on A (subspace_topology X TX A) {..<m} x0"
    sorry \<comment> \<open>1-skeleton of 2m-gon with projective scheme = wedge of m circles.\<close>
  \<comment> \<open>Step 3: Theorem 72.1 with relator a₁²a₂²...aₘ².\<close>
  show ?thesis sorry \<comment> \<open>Theorem 72.1 + projective presentation.\<close>
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
  \<comment> \<open>Step 2: Abelianize. The presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩ abelianizes to
     the free abelian group on 2n generators (commutator relator becomes trivial).\<close>
  have h_abelianize: "\<exists>(H::'h set) mulH eH invgH \<iota>_S \<phi>.
      top1_is_abelianization_of H mulH eH invgH
        (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0) \<phi>
      \<and> top1_is_free_abelian_group_full_on H mulH eH invgH (\<iota>_S::nat \<Rightarrow> 'h) {..<2*n}"
    sorry \<comment> \<open>Abelianization of group with commutator relator = free abelian.\<close>
  show ?thesis using h_abelianize by (by100 blast)
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
  \<comment> \<open>Step 2: Abelianize. The relator a₁²...aₘ² maps to 2(a₁+...+aₘ) in the abelianization.
     H₁ = Z^m/⟨2·sum⟩. Decompose: torsion = Z/2Z (class of sum), free = Z^{m-1}.\<close>
  show ?thesis sorry \<comment> \<open>Abelianization + Smith normal form decomposition.\<close>
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
  show ?thesis sorry \<comment> \<open>Disjoint simplex copies + pasting map gives quotient presentation.\<close>
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
  show ?thesis sorry \<comment> \<open>Iterative merging via spanning tree of dual graph.\<close>
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

section \<open>Chapter 13: Classification of Covering Spaces\<close>

text \<open>General lift uniqueness: if two continuous maps into a covering space
  agree at one point, both lift the same base map, and the domain is connected,
  then they agree everywhere.\<close>
lemma covering_lift_unique_connected:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hconn: "top1_connected_on Y TY"
      and hf1: "top1_continuous_map_on Y TY E TE f1"
      and hf2: "top1_continuous_map_on Y TY E TE f2"
      and hlift1: "\<forall>y\<in>Y. p (f1 y) = p (f2 y)"
      and hagree: "y0 \<in> Y" and hf1f2: "f1 y0 = f2 y0"
  shows "\<forall>y\<in>Y. f1 y = f2 y"
proof -
  \<comment> \<open>S = agreement set = {y \<in> Y | f1(y) = f2(y)}. Show S is open, closed, non-empty in Y.
     Y connected \<Rightarrow> S = Y.\<close>
  let ?S = "{y \<in> Y. f1 y = f2 y}"
  have hS_ne: "?S \<noteq> {}" using hagree hf1f2 by (by100 blast)
  \<comment> \<open>S is open: for y \<in> S, p(f1(y)) = p(f2(y)) has an evenly covered nbhd U.
     f1(y) = f2(y) lies in one sheet V₀. Near y, both f1 and f2 map into V₀
     (by continuity), and p is injective on V₀, so f1 = f2 near y.\<close>
  have hS_open: "?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> S, find open neighborhood contained in S.\<close>
    have "\<forall>y\<in>?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> ?S"
      hence hyY: "y \<in> Y" and hf12: "f1 y = f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Get evenly covered U of p(f1(y)).\<close>
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) is in some sheet V₀.\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      hence "f1 y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
      then obtain V0 where hV0: "V0 \<in> \<V>" and hf1V0: "f1 y \<in> V0" by (by100 blast)
      \<comment> \<open>f2(y) = f1(y) \<in> V₀.\<close>
      have hf2V0: "f2 y \<in> V0" using hf12 hf1V0 by (by100 simp)
      \<comment> \<open>V₀ is open in E.\<close>
      have hV0_openE: "openin_on E TE V0" using hV_open hV0 by (by100 blast)
      have hV0_sub: "V0 \<subseteq> E" using hV0_openE unfolding openin_on_def by (by100 blast)
      have hV0_TE: "V0 \<in> TE" using hV0_openE unfolding openin_on_def by (by100 blast)
      \<comment> \<open>f1⁻¹(V₀) and f2⁻¹(V₀) are open in Y.\<close>
      have hf1_preV0: "{y\<in>Y. f1 y \<in> V0} \<in> TY"
        using hf1 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_preV0: "{y\<in>Y. f2 y \<in> V0} \<in> TY"
        using hf2 hV0_TE unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V₀) \<inter> f2⁻¹(V₀) is open in Y.\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0}"
      have hW_TY: "?W \<in> TY"
      proof -
        have "{y\<in>Y. f1 y \<in> V0} \<inter> {y\<in>Y. f2 y \<in> V0} \<in> TY"
        proof -
          have hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          let ?A = "{y\<in>Y. f1 y \<in> V0}" and ?B = "{y\<in>Y. f2 y \<in> V0}"
          have hfin: "finite {?A, ?B}" by (by100 simp)
          have hne: "{?A, ?B} \<noteq> {}" by (by100 blast)
          have hsub: "{?A, ?B} \<subseteq> TY" using hf1_preV0 hf2_preV0 by (by100 blast)
          have "\<Inter>{?A, ?B} \<in> TY"
            using hinter hfin hne hsub by (by100 blast)
          moreover have "\<Inter>{?A, ?B} = ?A \<inter> ?B" by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        qed
        thus ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V0 hf2V0 by (by100 blast)
      \<comment> \<open>On W, f1 = f2 (p injective on V₀).\<close>
      have hW_sub_S: "?W \<subseteq> ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V0: "f1 z \<in> V0" and hf2z_V0: "f2 z \<in> V0"
          by (by100 blast)+
        have "p (f1 z) = p (f2 z)" using hlift1 hzY by (by100 blast)
        \<comment> \<open>p is injective on V₀ (homeomorphism, hence bij_betw, hence inj_on).\<close>
        have hp_inj: "inj_on p V0"
          using hV_homeo hV0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "f1 z = f2 z" using hp_inj hf1z_V0 hf2z_V0 \<open>p (f1 z) = p (f2 z)\<close>
          unfolding inj_on_def by (by100 blast)
        thus "z \<in> ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_sub_S hW_TY by (by100 blast)+
    qed
    \<comment> \<open>S is a union of open sets, hence open.\<close>
    have "?S = \<Union>{W \<in> TY. W \<subseteq> ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
      proof
        assume "y \<in> ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> ?S"
          using \<open>\<forall>y\<in>?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> ?S}"
        thus "y \<in> ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y \ S is open: for y \<in> Y \ S, f1(y) \<noteq> f2(y). Since p(f1(y)) = p(f2(y)),
     f1(y) and f2(y) lie in different sheets V₁, V₂ over the same U.
     Near y, f1 maps into V₁ and f2 into V₂ (continuity), so f1 \<noteq> f2 near y.\<close>
  have hYmS_open: "Y - ?S \<in> TY"
  proof -
    \<comment> \<open>For each y \<in> Y \ S, find open neighborhood disjoint from S.\<close>
    have "\<forall>y\<in>Y - ?S. \<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y - ?S"
      hence hyY: "y \<in> Y" and hf12_ne: "f1 y \<noteq> f2 y" by (by100 blast)+
      have hf1Y: "f1 y \<in> E" using hf1 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2Y: "f2 y \<in> E" using hf2 hyY unfolding top1_continuous_map_on_def by (by100 blast)
      have hpf1: "p (f1 y) \<in> B"
        using hcov hf1Y unfolding top1_covering_map_on_def top1_continuous_map_on_def by (by100 blast)
      obtain U where hU: "p (f1 y) \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
        using hcov hpf1 unfolding top1_covering_map_on_def by (by100 blast)
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
        using hec unfolding top1_evenly_covered_on_def by blast
      \<comment> \<open>f1(y) and f2(y) are in different sheets (p(f1(y)) = p(f2(y)) but f1(y) \<noteq> f2(y)).\<close>
      have "f1 y \<in> {x\<in>E. p x \<in> U}" using hf1Y hU by (by100 blast)
      then obtain V1 where hV1: "V1 \<in> \<V>" and hf1V1: "f1 y \<in> V1"
        using hV_cover by (by100 blast)
      have hpf2: "p (f2 y) \<in> U"
      proof -
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        thus ?thesis using hU by (by100 simp)
      qed
      have "f2 y \<in> {x\<in>E. p x \<in> U}" using hf2Y hpf2 by (by100 blast)
      then obtain V2 where hV2: "V2 \<in> \<V>" and hf2V2: "f2 y \<in> V2"
        using hV_cover by (by100 blast)
      have hV12_ne: "V1 \<noteq> V2"
      proof
        assume "V1 = V2"
        hence "f2 y \<in> V1" using hf2V2 by (by100 simp)
        have hp_inj: "inj_on p V1"
          using hV_homeo hV1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "p (f1 y) = p (f2 y)" using hlift1 hyY by (by100 blast)
        hence "f1 y = f2 y"
          using hp_inj hf1V1 \<open>f2 y \<in> V1\<close> unfolding inj_on_def by (by100 blast)
        thus False using hf12_ne by (by100 blast)
      qed
      have hV1_TE: "V1 \<in> TE" using hV_open hV1 unfolding openin_on_def by (by100 blast)
      have hV2_TE: "V2 \<in> TE" using hV_open hV2 unfolding openin_on_def by (by100 blast)
      \<comment> \<open>W = f1⁻¹(V1) \<inter> f2⁻¹(V2) is open and f1 \<noteq> f2 on W (different sheets, disjoint).\<close>
      let ?W = "{y\<in>Y. f1 y \<in> V1} \<inter> {y\<in>Y. f2 y \<in> V2}"
      have hf1_pre: "{y\<in>Y. f1 y \<in> V1} \<in> TY"
        using hf1 hV1_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hf2_pre: "{y\<in>Y. f2 y \<in> V2} \<in> TY"
        using hf2 hV2_TE unfolding top1_continuous_map_on_def by (by100 blast)
      have hinter': "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      let ?A' = "{y\<in>Y. f1 y \<in> V1}" and ?B' = "{y\<in>Y. f2 y \<in> V2}"
      have hW_TY: "?W \<in> TY"
      proof -
        have hfin': "finite {?A', ?B'}" by (by100 simp)
        have hne': "{?A', ?B'} \<noteq> {}" by (by100 blast)
        have hsub': "{?A', ?B'} \<subseteq> TY" using hf1_pre hf2_pre by (by100 blast)
        have "\<Inter>{?A', ?B'} \<in> TY"
          using hinter' hfin' hne' hsub' by (by100 blast)
        moreover have "\<Inter>{?A', ?B'} = ?A' \<inter> ?B'" by (by100 auto)
        ultimately show ?thesis by (by100 simp)
      qed
      have hyW: "y \<in> ?W" using hyY hf1V1 hf2V2 by (by100 blast)
      have hW_disj: "?W \<subseteq> Y - ?S"
      proof (rule subsetI)
        fix z assume hz: "z \<in> ?W"
        hence hzY: "z \<in> Y" and hf1z_V1: "f1 z \<in> V1" and hf2z_V2: "f2 z \<in> V2"
          by (by100 blast)+
        have hV12_disj: "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 hV12_ne by (by100 blast)
        have "f1 z \<noteq> f2 z"
        proof
          assume "f1 z = f2 z"
          hence "f1 z \<in> V2" using hf2z_V2 by (by100 simp)
          hence "f1 z \<in> V1 \<inter> V2" using hf1z_V1 by (by100 blast)
          thus False using hV12_disj by (by100 blast)
        qed
        thus "z \<in> Y - ?S" using hzY by (by100 blast)
      qed
      show "\<exists>W\<in>TY. y \<in> W \<and> W \<subseteq> Y - ?S"
        apply (rule bexI[where x="?W"])
        using hyW hW_disj hW_TY by (by100 blast)+
    qed
    have "Y - ?S = \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
    proof (rule set_eqI)
      fix y show "y \<in> Y - ?S \<longleftrightarrow> y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}"
      proof
        assume "y \<in> Y - ?S"
        then obtain W where "W \<in> TY" "y \<in> W" "W \<subseteq> Y - ?S"
          using \<open>\<forall>y\<in>Y - ?S. _\<close> by (by100 blast)
        thus "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" by (by100 blast)
      next
        assume "y \<in> \<Union>{W \<in> TY. W \<subseteq> Y - ?S}" thus "y \<in> Y - ?S" by (by100 blast)
      qed
    qed
    moreover have "\<Union>{W \<in> TY. W \<subseteq> Y - ?S} \<in> TY"
    proof -
      have hunion: "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
        using hTY unfolding is_topology_on_def by (by100 blast)
      have "{W \<in> TY. W \<subseteq> Y - ?S} \<subseteq> TY" by (by100 blast)
      thus ?thesis using hunion by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Y connected + S non-empty + S open + complement open \<Rightarrow> S = Y.\<close>
  have "?S = Y"
  proof -
    have "?S \<subseteq> Y" by (by100 blast)
    moreover have "?S \<in> TY" by (rule hS_open)
    moreover have "Y - ?S \<in> TY" by (rule hYmS_open)
    moreover have "?S \<noteq> {}" by (rule hS_ne)
    ultimately show ?thesis using hconn unfolding top1_connected_on_def by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Helper: path-connected implies connected.\<close>
lemma path_connected_imp_connected:
  assumes "top1_path_connected_on X TX"
  shows "top1_connected_on X TX"
  unfolding top1_connected_on_def
proof (intro conjI)
  have hTX: "is_topology_on X TX"
    using assms unfolding top1_path_connected_on_def by (by100 blast)
  show "is_topology_on X TX" by (rule hTX)
  show "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
  proof (rule notI)
    assume "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    then obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TX" and hU0ne: "U0 \<noteq> {}"
        and hV0ne: "V0 \<noteq> {}" and hdisj: "U0 \<inter> V0 = {}" and hcover: "U0 \<union> V0 = X"
      by blast
    obtain a where ha: "a \<in> U0" using hU0ne by blast
    obtain b where hb: "b \<in> V0" using hV0ne by blast
    have haX: "a \<in> X"
    proof -
      have "a \<in> U0 \<union> V0" using ha by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    have hbX: "b \<in> X"
    proof -
      have "b \<in> U0 \<union> V0" using hb by (by100 blast)
      thus ?thesis using hcover by (by100 simp)
    qed
    \<comment> \<open>Path from a to b (path-connected).\<close>
    obtain \<gamma> where h\<gamma>: "top1_is_path_on X TX a b \<gamma>"
      using assms haX hbX unfolding top1_path_connected_on_def by (by100 auto)
    \<comment> \<open>\<gamma> maps [0,1] into X = U0 \<union> V0. The preimages \<gamma>⁻¹(U0) and \<gamma>⁻¹(V0) cover [0,1].
       \<gamma>(0) = a \<in> U0 and \<gamma>(1) = b \<in> V0. Since [0,1] is connected,
       \<gamma>⁻¹(U0) \<inter> \<gamma>⁻¹(V0) \<noteq> {}. But U0 \<inter> V0 = {}, contradiction.\<close>
    have h\<gamma>0: "\<gamma> 0 = a" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>1: "\<gamma> 1 = b" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>_cont: "top1_continuous_map_on I_set I_top X TX \<gamma>"
      using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
    \<comment> \<open>Preimages of U0 and V0 under \<gamma> are open in [0,1].\<close>
    have hpreU: "{s \<in> I_set. \<gamma> s \<in> U0} \<in> I_top"
      using h\<gamma>_cont hU0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hpreV: "{s \<in> I_set. \<gamma> s \<in> V0} \<in> I_top"
      using h\<gamma>_cont hV0 unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>They cover [0,1] and are disjoint.\<close>
    have hcov_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} = I_set"
    proof (rule set_eqI)
      fix s show "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0} \<longleftrightarrow> s \<in> I_set"
      proof
        assume "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" thus "s \<in> I_set" by (by100 blast)
      next
        assume hs: "s \<in> I_set"
        hence "\<gamma> s \<in> X" using h\<gamma>_cont unfolding top1_continuous_map_on_def by (by100 blast)
        hence "\<gamma> s \<in> U0 \<or> \<gamma> s \<in> V0" using hcover by (by100 blast)
        thus "s \<in> {s \<in> I_set. \<gamma> s \<in> U0} \<union> {s \<in> I_set. \<gamma> s \<in> V0}" using hs by (by100 blast)
      qed
    qed
    have hdisj_I: "{s \<in> I_set. \<gamma> s \<in> U0} \<inter> {s \<in> I_set. \<gamma> s \<in> V0} = {}"
      using hdisj by (by100 blast)
    have hneU: "{s \<in> I_set. \<gamma> s \<in> U0} \<noteq> {}"
    proof -
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 0 \<in> U0" using h\<gamma>0 ha by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    have hneV: "{s \<in> I_set. \<gamma> s \<in> V0} \<noteq> {}"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "\<gamma> 1 \<in> V0" using h\<gamma>1 hb by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>[0,1] is connected (I_set with I_top).\<close>
    have hI_conn: "top1_connected_on I_set I_top"
      by (rule top1_unit_interval_connected)
    \<comment> \<open>Contradiction: connected set separated by two disjoint nonempty open sets.\<close>
    show False using hI_conn hpreU hpreV hneU hneV hdisj_I hcov_I
      unfolding top1_connected_on_def by (by100 blast)
  qed
qed

text \<open>General lifting criterion (Munkres Theorem 79.1): given a covering map p: E \<rightarrow> B,
  a continuous map f: Y \<rightarrow> B with Y path-connected and locally path-connected,
  if f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)), then f lifts to a continuous map \<tilde>f: Y \<rightarrow> E
  with p \<circ> \<tilde>f = f and \<tilde>f(y0) = e0.\<close>
lemma general_lifting_criterion:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTY: "is_topology_on Y TY" and hTB: "is_topology_on B TB" and hTE: "is_topology_on E TE"
      and hf: "top1_continuous_map_on Y TY B TB f"
      and hYpc: "top1_path_connected_on Y TY"
      and hYlpc: "top1_locally_path_connected_on Y TY"
      and hy0: "y0 \<in> Y" and he0: "e0 \<in> E" and hfy0: "f y0 = p e0"
      and hsubgrp: "top1_fundamental_group_image_hom Y TY y0 B TB (p e0) f
          \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
  shows "\<exists>ftilde. (\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y)
      \<and> ftilde y0 = e0 \<and> top1_continuous_map_on Y TY E TE ftilde"
proof -
  \<comment> \<open>Step 1: Define ftilde(y) for each y \<in> Y.
     Pick path \<alpha> from y0 to y (Y path-connected).
     f\<circ>\<alpha> is a path from f(y0) = p(e0) to f(y) in B.
     Lift f\<circ>\<alpha> to E starting at e0.
     ftilde(y) = lift endpoint.\<close>
  let ?b0 = "p e0"
  \<comment> \<open>For each y \<in> Y, obtain a path from y0 to y.\<close>
  have hpath_exists: "\<forall>y\<in>Y. \<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
    using hYpc hy0 unfolding top1_path_connected_on_def by (by100 auto)
  \<comment> \<open>For each path \<alpha>, f\<circ>\<alpha> can be lifted to E.\<close>
  have hlift_exists: "\<forall>y\<in>Y. \<forall>\<alpha>. top1_is_path_on Y TY y0 y \<alpha> \<longrightarrow>
      (\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)))"
  proof (intro ballI allI impI)
    fix y \<alpha> assume hy: "y \<in> Y" and h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
    have hf\<alpha>: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>) 0 = ?b0"
        using h\<alpha> hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>) 1 = f y"
        using h\<alpha> unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft' \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> \<alpha>) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>)" by (rule hf\<alpha>)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft where hft: "top1_is_path_on E TE e0 (ft 1) ft"
        and hftp: "\<forall>s\<in>I_set. p (ft s) = (f \<circ> \<alpha>) s" by (by100 blast)
    have "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)" using hftp by (by100 simp)
    thus "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))"
      using hft by (by100 blast)
  qed
  \<comment> \<open>Step 2: Well-definedness. Any two paths \<alpha>1, \<alpha>2 from y0 to y give the same lift endpoint.
     \<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.
     [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)) (by hsubgrp).
     So there exists a loop \<delta> at e0 in E with p\<circ>\<delta> \<simeq> f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).
     By Theorem_54_3: lifts from e0 of path-homotopic loops have same endpoints.
     The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 is a loop (since it lifts p\<circ>\<delta> which is homotopic,
     and \<delta> lifts to itself, ending at e0).
     This loop decomposes as: lift(f\<circ>\<alpha>1) followed by reverse(lift(f\<circ>\<alpha>2)).
     Both starting at e0, so the endpoints of lift(f\<circ>\<alpha>1) and lift(f\<circ>\<alpha>2) agree.\<close>
  have hwd: "\<forall>y\<in>Y. \<forall>\<alpha>1 \<alpha>2 ft1 ft2.
      top1_is_path_on Y TY y0 y \<alpha>1 \<longrightarrow>
      top1_is_path_on Y TY y0 y \<alpha>2 \<longrightarrow>
      top1_is_path_on E TE e0 (ft1 1) ft1 \<longrightarrow> (\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)) \<longrightarrow>
      top1_is_path_on E TE e0 (ft2 1) ft2 \<longrightarrow> (\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)) \<longrightarrow>
      ft1 1 = ft2 1"
  proof (intro ballI allI impI)
    fix y \<alpha>1 \<alpha>2 ft1 ft2
    assume hy: "y \<in> Y"
        and h\<alpha>1: "top1_is_path_on Y TY y0 y \<alpha>1"
        and h\<alpha>2: "top1_is_path_on Y TY y0 y \<alpha>2"
        and hft1: "top1_is_path_on E TE e0 (ft1 1) ft1"
        and hft1p: "\<forall>s\<in>I_set. p (ft1 s) = f (\<alpha>1 s)"
        and hft2: "top1_is_path_on E TE e0 (ft2 1) ft2"
        and hft2p: "\<forall>s\<in>I_set. p (ft2 s) = f (\<alpha>2 s)"
    \<comment> \<open>f\<circ>\<alpha>1 and f\<circ>\<alpha>2 are paths from p(e0) to f(y) in B.\<close>
    have hf\<alpha>1: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>1)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>1)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>1 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>1) 0 = ?b0" using h\<alpha>1 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>1) 1 = f y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hf\<alpha>2: "top1_is_path_on B TB ?b0 (f y) (f \<circ> \<alpha>2)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<alpha>2)"
        by (rule top1_continuous_map_on_comp)
           (use h\<alpha>2 hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(f \<circ> \<alpha>2) 0 = ?b0" using h\<alpha>2 hfy0 unfolding top1_is_path_on_def by (by100 simp)
      moreover have "(f \<circ> \<alpha>2) 1 = f y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>ft1 lifts f\<circ>\<alpha>1 from e0, ft2 lifts f\<circ>\<alpha>2 from e0.\<close>
    have hft1_lift: "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s"
      using hft1p by (by100 simp)
    have hft2_lift: "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s"
      using hft2p by (by100 simp)
    \<comment> \<open>\<alpha>1\<cdot>\<alpha>2\<inverse> is a loop at y0. f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is a loop at p(e0) in B.\<close>
    have h\<alpha>2_rev: "top1_is_path_on Y TY y y0 (top1_path_reverse \<alpha>2)"
      by (rule top1_path_reverse_is_path[OF h\<alpha>2])
    have hloop_Y: "top1_is_loop_on Y TY y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)] \<in> p_*(\<pi>_1(E,e0)): from hsubgrp (f_* \<subseteq> p_*).\<close>
    \<comment> \<open>\<Rightarrow> \<exists> loop \<delta> at e0 in E with [p\<circ>\<delta>] = [f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>)].\<close>
    \<comment> \<open>\<delta> lifts p\<circ>\<delta> from e0, ending at e0 (loop).\<close>
    \<comment> \<open>By Theorem_54_3: lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Now the lift of (f\<circ>\<alpha>1)\<cdot>(f\<circ>\<alpha>2)\<inverse> from e0 is: ft1 followed by lift of (f\<circ>\<alpha>2)\<inverse> from ft1(1).
       Since this composite ends at e0, the second part goes from ft1(1) to e0.
       Its reverse lifts f\<circ>\<alpha>2 from e0 to ft1(1).
       By Lemma_54_1_uniqueness: ft2 agrees with this reverse \<Rightarrow> ft2(1) = ft1(1).\<close>
    \<comment> \<open>Get \<delta>: loop at e0 in E with p\<circ>\<delta> ~ f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>).\<close>
    have hfloop: "top1_is_loop_on B TB ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
    proof -
      have "top1_is_path_on Y TY y0 y0 (top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
        by (rule top1_path_product_is_path[OF hTY h\<alpha>1 h\<alpha>2_rev])
      hence "top1_is_path_on B TB ?b0 ?b0 (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          by (rule top1_continuous_map_on_comp)
             (use \<open>top1_is_path_on Y TY y0 y0 _\<close> hf in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 0 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) 1 = ?b0"
          using \<open>top1_is_path_on Y TY y0 y0 _\<close> hfy0 unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    \<comment> \<open>[f\<circ>loop] \<in> p_*(\<pi>_1(E)). Extract \<delta> with p\<circ>\<delta> ~ f\<circ>loop.\<close>
    \<comment> \<open>The loop class of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) is in f_*(\<pi>_1(Y)) \<subseteq> p_*(\<pi>_1(E)).\<close>
    let ?\<beta> = "top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)"
    have hclass_in_Y: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom Y TY y0 B TB ?b0 f"
    proof -
      have "{g. top1_loop_equiv_on Y TY y0 ?\<beta> g} \<in> top1_fundamental_group_carrier Y TY y0"
        unfolding top1_fundamental_group_carrier_def
        using top1_loop_equiv_on_refl[OF hloop_Y] hloop_Y by (by100 blast)
      thus ?thesis unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    qed
    \<comment> \<open>So the induced class is in p_*(\<pi>_1(E)).\<close>
    have hclass_in_E: "top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
        {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}
      \<in> top1_fundamental_group_image_hom E TE e0 B TB ?b0 p"
      using hsubgrp hclass_in_Y by (by100 blast)
    \<comment> \<open>Extract \<delta>: loop at e0 with [p\<circ>\<delta>] = induced_f([loop]).\<close>
    obtain \<delta> where h\<delta>_loop: "top1_is_loop_on E TE e0 \<delta>"
        and h\<delta>_hom: "top1_path_homotopic_on B TB ?b0 ?b0
            (p \<circ> \<delta>) (f \<circ> ?\<beta>)"
    proof -
      \<comment> \<open>Unpack: hclass_in_E says the f-induced class is in the p-image of \<pi>_1(E).\<close>
      from hclass_in_E obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hpc: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
              = top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
                  {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      \<comment> \<open>c = {g. loop_equiv(E, e0, \<delta>, g)} for some loop \<delta> at e0.\<close>
      from hc obtain \<delta>' where h\<delta>': "top1_is_loop_on E TE e0 \<delta>'"
          and hc_eq: "c = {g. top1_loop_equiv_on E TE e0 \<delta>' g}"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>p_*(c) = {g. loop_equiv(B, p e0, p\<circ>\<delta>', g)}.\<close>
      have hp_c: "top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c
          = {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      \<comment> \<open>f_*([β]) = {g. loop_equiv(B, p e0, f\<circ>β, g)} (approximately).\<close>
      \<comment> \<open>From hpc: the two induced classes are equal as sets.
         \<delta>' \<in> c, so p\<circ>\<delta>' gives a representative of p_*(c).
         β gives a representative of f_*([β]).
         Equal classes \<Rightarrow> p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have h\<delta>'_in_c: "\<delta>' \<in> c" using hc_eq top1_loop_equiv_on_refl[OF h\<delta>'] by (by100 blast)
      \<comment> \<open>p\<circ>\<delta>' is loop-equiv to itself, so it's in p_*(c).\<close>
      have hp\<delta>'_in: "p \<circ> \<delta>' \<in> {g. \<exists>h\<in>c. top1_loop_equiv_on B TB ?b0 (p \<circ> h) g}"
      proof -
        have "top1_is_loop_on B TB ?b0 (p \<circ> \<delta>')"
        proof -
          have h\<delta>'_path: "top1_is_path_on E TE e0 e0 \<delta>'"
            using h\<delta>' unfolding top1_is_loop_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>')"
            by (rule top1_continuous_map_on_comp)
               (use h\<delta>'_path top1_covering_map_on_continuous[OF hcov] in
                  \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> \<delta>') 0 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> \<delta>') 1 = ?b0"
            using h\<delta>'_path unfolding top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            by (by100 blast)
        qed
        hence "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (p \<circ> \<delta>')"
          by (rule top1_loop_equiv_on_refl)
        thus ?thesis using h\<delta>'_in_c by (by100 blast)
      qed
      \<comment> \<open>f\<circ>β is loop-equiv to itself, so it's in f_*([β]).\<close>
      have hf\<beta>_in: "f \<circ> ?\<beta> \<in> {g. \<exists>h\<in>{g. top1_loop_equiv_on Y TY y0 ?\<beta> g}.
          top1_loop_equiv_on B TB ?b0 (f \<circ> h) g}"
      proof -
        have "?\<beta> \<in> {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
          using top1_loop_equiv_on_refl[OF hloop_Y] by (by100 blast)
        moreover have "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> ?\<beta>)"
          by (rule top1_loop_equiv_on_refl[OF hfloop])
        ultimately show ?thesis by (by100 blast)
      qed
      \<comment> \<open>Since p_*(c) = f_*([β]) and p\<circ>\<delta>' \<in> p_*(c), f\<circ>β \<in> f_*([β]),
         and both are equivalence classes, p\<circ>\<delta>' ~ f\<circ>β.\<close>
      have "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on E TE e0 B TB ?b0 p c"
        using hp\<delta>'_in hp_c by (by100 simp)
      hence "p \<circ> \<delta>' \<in> top1_fundamental_group_induced_on Y TY y0 B TB ?b0 f
          {g. top1_loop_equiv_on Y TY y0 ?\<beta> g}"
        using hpc by (by100 simp)
      hence "\<exists>h. top1_loop_equiv_on Y TY y0 ?\<beta> h \<and> top1_loop_equiv_on B TB ?b0 (f \<circ> h) (p \<circ> \<delta>')"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      then obtain \<beta>' where h\<beta>': "top1_loop_equiv_on Y TY y0 ?\<beta> \<beta>'"
          and hp\<delta>'_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> \<beta>') (p \<circ> \<delta>')" by (by100 blast)
      \<comment> \<open>f\<circ>β ~ f\<circ>β' (since β ~ β') and f\<circ>β' ~ p\<circ>δ'. So f\<circ>β ~ p\<circ>δ'.\<close>
      have hf\<beta>_f\<beta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
      proof -
        have h\<beta>'_loop: "top1_is_loop_on Y TY y0 \<beta>'"
          using h\<beta>' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (f y0) (f \<circ> ?\<beta>) (f \<circ> \<beta>')"
          by (rule top1_induced_preserves_loop_equiv[OF hTY hf hloop_Y h\<beta>'_loop h\<beta>'])
        thus ?thesis using hfy0 by (by100 simp)
      qed
      \<comment> \<open>Chain: f\<circ>β ~ f\<circ>β' (by hf\<beta>_f\<beta>'), f\<circ>β' ~ p\<circ>δ' (sym of hp\<delta>'_f\<beta>').\<close>
      \<comment> \<open>hp\<delta>'_f\<beta>' says f\<circ>\<beta>' ~ p\<circ>\<delta>', which is already the right direction.\<close>
      have hf\<beta>_p\<delta>': "top1_loop_equiv_on B TB ?b0 (f \<circ> ?\<beta>) (p \<circ> \<delta>')"
        by (rule top1_loop_equiv_on_trans[OF hTB hf\<beta>_f\<beta>' hp\<delta>'_f\<beta>'])
      have hp\<delta>'_f\<beta>: "top1_loop_equiv_on B TB ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        by (rule top1_loop_equiv_on_sym[OF hf\<beta>_p\<delta>'])
      have "top1_path_homotopic_on B TB ?b0 ?b0 (p \<circ> \<delta>') (f \<circ> ?\<beta>)"
        using hp\<delta>'_f\<beta> unfolding top1_loop_equiv_on_def by (by100 blast)
      thus ?thesis using h\<delta>' that by (by100 blast)
    qed
    \<comment> \<open>By Theorem_54_3: \<delta> lifts p\<circ>\<delta> from e0 (loop \<Rightarrow> ends at e0).
       The lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0 also ends at e0.\<close>
    \<comment> \<open>Get a lift of f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0.\<close>
    have hfloop_path: "top1_is_path_on B TB ?b0 ?b0
        (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
      using hfloop unfolding top1_is_loop_on_def by (by100 blast)
    have "\<exists>ft'. top1_is_path_on E TE e0 (ft' 1) ft'
        \<and> (\<forall>s\<in>I_set. p (ft' s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s)"
    proof (rule Lemma_54_1_path_lifting)
      show "top1_covering_map_on E TE B TB p" by (rule hcov)
      show "e0 \<in> E" by (rule he0)
      show "p e0 = p e0" by (by100 simp)
      show "top1_is_path_on B TB (p e0) ?b0
          (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using hfloop_path by (by100 simp)
      show "is_topology_on B TB" by (rule hTB)
      show "is_topology_on E TE" by (rule hTE)
    qed
    then obtain ft_loop where hft_loop: "top1_is_path_on E TE e0 (ft_loop 1) ft_loop"
        and hft_loop_lift: "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
      by (by100 blast)
    \<comment> \<open>By Theorem_54_3 with p\<circ>\<delta> ~ f\<circ>loop: ft_loop(1) = \<delta>(1) = e0.\<close>
    have hft_loop_end: "ft_loop 1 = e0"
    proof -
      have h\<delta>_path: "top1_is_path_on E TE e0 e0 \<delta>"
        using h\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h\<delta>_lift: "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
      have hp\<delta>_path: "top1_is_path_on B TB ?b0 ?b0 (p \<circ> \<delta>)"
      proof -
        have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<delta>)"
          by (rule top1_continuous_map_on_comp)
             (use h\<delta>_path top1_covering_map_on_continuous[OF hcov] in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
        moreover have "(p \<circ> \<delta>) 0 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        moreover have "(p \<circ> \<delta>) 1 = ?b0"
          using h\<delta>_path unfolding top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      have "e0 = ft_loop 1 \<and> top1_path_homotopic_on E TE e0 e0 \<delta> ft_loop"
      proof (rule Theorem_54_3[OF hcov hTE hTB he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (p \<circ> \<delta>)" using hp\<delta>_path by (by100 simp)
        show "top1_is_path_on B TB (p e0) (p e0) (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))"
          using hfloop_path by (by100 simp)
        show "top1_path_homotopic_on B TB (p e0) (p e0) (p \<circ> \<delta>)
            (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2))" using h\<delta>_hom by (by100 simp)
        show "top1_is_path_on E TE e0 e0 \<delta>" by (rule h\<delta>_path)
        show "\<forall>s\<in>I_set. p (\<delta> s) = (p \<circ> \<delta>) s" by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop 1) ft_loop" by (rule hft_loop)
        show "\<forall>s\<in>I_set. p (ft_loop s) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) s"
          by (rule hft_loop_lift)
      qed
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>ft_loop lifts f\<circ>(\<alpha>1\<cdot>\<alpha>2\<inverse>) from e0, ending at e0.
       Now use Lemma_54_1_uniqueness to relate ft_loop to ft1 and ft2.\<close>
    \<comment> \<open>The first half of ft_loop (rescaled to [0,1]) lifts f\<circ>\<alpha>1.
       By uniqueness with ft1: they agree, in particular ft_loop(1/2) = ft1(1).
       The second half reversed lifts f\<circ>\<alpha>2.
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       So ft1(1) = ft2(1).\<close>
    \<comment> \<open>First half of ft_loop (rescaled) lifts f\<circ>\<alpha>1 from e0.
       By uniqueness with ft1: ft_loop(1/2) = ft1(1).
       Second half reversed lifts f\<circ>\<alpha>2 from e0 (since ft_loop ends at e0).
       By uniqueness with ft2: ft_loop(1/2) = ft2(1).
       Therefore ft1(1) = ft2(1).\<close>
    \<comment> \<open>g1(s) = ft_loop(s/2) is a path lifting f\<circ>\<alpha>1 from e0.\<close>
    let ?g1 = "\<lambda>s. ft_loop (s / 2)"
    have hg1_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>The linear map s \<mapsto> s/2 is continuous from I_set to I_set.\<close>
      have hlin_cont: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. s / 2) = (\<lambda>s. ft_loop (s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (0 / 2) = e0"
        using hft_loop unfolding top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg1_lift: "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2))" by (by100 simp)
      also have "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (s / 2) = \<alpha>1 (2 * (s / 2))"
        unfolding top1_path_product_def using hs01 by (by100 simp)
      also have "2 * (s / 2) = s" by (by100 simp)
      finally show "p (?g1 s) = (f \<circ> \<alpha>1) s" by (by100 simp)
    qed
    \<comment> \<open>By uniqueness: ?g1 agrees with ft1 \<Rightarrow> ft_loop(1/2) = ft1(1).\<close>
    have "ft_loop (1/2) = ft1 1"
    proof -
      have "\<forall>s\<in>I_set. ?g1 s = ft1 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>1)" using hf\<alpha>1 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g1" by (rule hg1_path)
        show "\<forall>s\<in>I_set. p (?g1 s) = (f \<circ> \<alpha>1) s" by (rule hg1_lift)
        show "top1_is_path_on E TE e0 (ft1 1) ft1" by (rule hft1)
        show "\<forall>s\<in>I_set. p (ft1 s) = (f \<circ> \<alpha>1) s" using hft1_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g1 1 = ft1 1" using \<open>\<forall>s\<in>I_set. ?g1 s = ft1 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    \<comment> \<open>g2(s) = ft_loop(1 - s/2) lifts f\<circ>\<alpha>2 from e0 (since ft_loop(1) = e0).\<close>
    let ?g2 = "\<lambda>s. ft_loop (1 - s / 2)"
    have hg2_path: "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2"
    proof -
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ft_loop"
        using hft_loop unfolding top1_is_path_on_def by (by100 blast)
      have hlin_cont2: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. 1 - s / 2)"
      proof -
        have "\<And>s::real. s \<in> I_set \<Longrightarrow> 1 - s / 2 \<in> I_set"
          unfolding top1_unit_interval_def by (by100 simp)
        moreover have "continuous_on (UNIV::real set) (\<lambda>s::real. 1 - s / 2)"
          by (intro continuous_intros continuous_on_divide) auto
        ultimately have "top1_continuous_map_on I_set
            (subspace_topology (UNIV::real set) top1_open_sets I_set)
            I_set (subspace_topology (UNIV::real set) top1_open_sets I_set) (\<lambda>s. 1 - s / 2)"
          by (rule top1_continuous_map_on_real_subspace_open_sets)
        moreover have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_continuous_map_on I_set I_top E TE (\<lambda>s. ft_loop (1 - s / 2))"
      proof -
        have "top1_continuous_map_on I_set I_top E TE (ft_loop \<circ> (\<lambda>s. 1 - s / 2))"
          by (rule top1_continuous_map_on_comp[OF hlin_cont2 hft_cont])
        moreover have "ft_loop \<circ> (\<lambda>s. 1 - s / 2) = (\<lambda>s. ft_loop (1 - s / 2))"
          by (rule ext) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 0 / 2) = e0"
      proof -
        have "ft_loop 1 = e0" by (rule hft_loop_end)
        thus ?thesis by (by100 simp)
      qed
      moreover have "ft_loop (1 - 1 / 2) = ft_loop (1/2)" by (by100 simp)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hg2_lift: "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
      have hs2: "1 - s / 2 \<in> I_set" unfolding top1_unit_interval_def using hs01 by (by100 simp)
      have "p (ft_loop (1 - s / 2)) = (f \<circ> top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)"
        using hft_loop_lift hs2 by (by100 blast)
      also have "\<dots> = f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))" by (by100 simp)
      also have "\<dots> = f (\<alpha>2 s)"
      proof (cases "s = 1")
        case True
        \<comment> \<open>At s=1: path_product at 1/2 gives \<alpha>1(1) = y. f(\<alpha>1(1)) = f(y) = f(\<alpha>2(1)).\<close>
        have "1 - s / 2 = 1 / 2" using True by (by100 simp)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2) = \<alpha>1 (2 * (1/2))"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)) = f (\<alpha>1 1)"
          by (by100 simp)
        moreover have "\<alpha>1 1 = y" using h\<alpha>1 unfolding top1_is_path_on_def by (by100 blast)
        moreover have "\<alpha>2 1 = y" using h\<alpha>2 unfolding top1_is_path_on_def by (by100 blast)
        ultimately show ?thesis using True by (by100 simp)
      next
        case False
        hence "1 - s / 2 > 1 / 2" using hs01 by (by100 linarith)
        hence "\<not> (1 - s / 2 \<le> 1 / 2)" by (by100 linarith)
        hence "(top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2)
            = (top1_path_reverse \<alpha>2) (2 * (1 - s / 2) - 1)"
          unfolding top1_path_product_def by (by100 simp)
        hence "f ((top1_path_product \<alpha>1 (top1_path_reverse \<alpha>2)) (1 - s / 2))
            = f ((top1_path_reverse \<alpha>2) (1 - s))" by (by100 simp)
        moreover have "(top1_path_reverse \<alpha>2) (1 - s) = \<alpha>2 s"
          unfolding top1_path_reverse_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      finally show "p (?g2 s) = (f \<circ> \<alpha>2) s" by (by100 simp)
    qed
    have "ft_loop (1/2) = ft2 1"
    proof -
      have "\<forall>s\<in>I_set. ?g2 s = ft2 s"
      proof (rule Lemma_54_1_uniqueness[OF hcov he0])
        show "p e0 = p e0" by (by100 simp)
        show "top1_is_path_on B TB (p e0) (f y) (f \<circ> \<alpha>2)" using hf\<alpha>2 by (by100 simp)
        show "top1_is_path_on E TE e0 (ft_loop (1/2)) ?g2" by (rule hg2_path)
        show "\<forall>s\<in>I_set. p (?g2 s) = (f \<circ> \<alpha>2) s" by (rule hg2_lift)
        show "top1_is_path_on E TE e0 (ft2 1) ft2" by (rule hft2)
        show "\<forall>s\<in>I_set. p (ft2 s) = (f \<circ> \<alpha>2) s" using hft2_lift by (by100 simp)
      qed
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "?g2 1 = ft2 1" using \<open>\<forall>s\<in>I_set. ?g2 s = ft2 s\<close> by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
    show "ft1 1 = ft2 1" using \<open>ft_loop (1/2) = ft1 1\<close> \<open>ft_loop (1/2) = ft2 1\<close> by (by100 simp)
  qed
  \<comment> \<open>Step 3: Define ftilde.\<close>
  define ftilde where "ftilde y = (let \<alpha> = SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>;
      ft = SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
    in ft 1)" for y
  \<comment> \<open>Step 4: ftilde has the required properties.\<close>
  have hft_props: "(\<forall>y\<in>Y. ftilde y \<in> E) \<and> (\<forall>y\<in>Y. p (ftilde y) = f y) \<and> ftilde y0 = e0"
  proof -
    \<comment> \<open>For each y \<in> Y: the SOME-chosen path and lift satisfy the properties.\<close>
    have hsome_props: "\<forall>y\<in>Y. (\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
        \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
        \<and> ftilde y = ft 1)"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y"
      let ?\<alpha> = "SOME \<alpha>. top1_is_path_on Y TY y0 y \<alpha>"
      have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y \<alpha>" using hpath_exists hy by (by100 blast)
      hence h\<alpha>: "top1_is_path_on Y TY y0 y ?\<alpha>" by (rule someI_ex)
      let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
      have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha> s))"
        using hlift_exists hy h\<alpha> by (by100 blast)
      hence hft: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = f (?\<alpha> s))"
        by (rule someI_ex)
      have "ftilde y = ?ft 1" unfolding ftilde_def by (by100 simp)
      thus "\<exists>\<alpha> ft. top1_is_path_on Y TY y0 y \<alpha>
          \<and> top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s))
          \<and> ftilde y = ft 1"
        using h\<alpha> hft by (by100 blast)
    qed
    show ?thesis proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where "top1_is_path_on E TE e0 (ft 1) ft" and "ftilde y = ft 1"
        by (by100 blast)
      have "ft 1 \<in> E"
      proof -
        have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        thus ?thesis using \<open>top1_is_path_on E TE e0 (ft 1) ft\<close>
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      qed
      thus "ftilde y \<in> E" using \<open>ftilde y = ft 1\<close> by (by100 simp)
    qed
  next
    show "\<forall>y\<in>Y. p (ftilde y) = f y"
    proof (intro ballI)
      fix y assume "y \<in> Y"
      from hsome_props[rule_format, OF this]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y = ft 1" by (by100 blast)
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "p (ft 1) = f (\<alpha> 1)" using hftp h1I by (by100 blast)
      moreover have "\<alpha> 1 = y" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      ultimately show "p (ftilde y) = f y" using hftilde by (by100 simp)
    qed
  next
    show "ftilde y0 = e0"
    proof -
      \<comment> \<open>The SOME-chosen path from y0 to y0 gives a lift; any lift from e0 of a
         loop at p(e0) has some endpoint. But by well-definedness, the endpoint
         is the same for all paths. The constant path at y0 lifts to constant at e0.\<close>
      from hsome_props[rule_format, OF hy0]
      obtain \<alpha> ft where h\<alpha>: "top1_is_path_on Y TY y0 y0 \<alpha>"
          and hft: "top1_is_path_on E TE e0 (ft 1) ft"
          and hftp: "\<forall>s\<in>I_set. p (ft s) = f (\<alpha> s)"
          and hftilde: "ftilde y0 = ft 1" by (by100 blast)
      \<comment> \<open>The constant path at y0 also lifts to constant at e0.\<close>
      have hconst_path: "top1_is_path_on Y TY y0 y0 (top1_constant_path y0)"
        by (rule top1_constant_path_is_path[OF hTY hy0])
      have hconst_lift: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
        by (rule top1_constant_path_is_path[OF hTE he0])
      have hconst_liftp: "\<forall>s\<in>I_set. p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
      proof (intro ballI)
        fix s assume "s \<in> I_set"
        show "p ((top1_constant_path e0) s) = f ((top1_constant_path y0) s)"
          unfolding top1_constant_path_def using hfy0 by (by100 simp)
      qed
      \<comment> \<open>By well-definedness (hwd): ft 1 = e0.\<close>
      have "ft 1 = (top1_constant_path e0) 1"
      proof -
        have hcl2: "top1_is_path_on E TE e0 ((top1_constant_path e0) 1) (top1_constant_path e0)"
        proof -
          have "(top1_constant_path e0) 1 = e0" unfolding top1_constant_path_def by (by100 simp)
          thus ?thesis using hconst_lift by (by100 simp)
        qed
        from hwd[rule_format, OF hy0, of \<alpha> "top1_constant_path y0" ft "top1_constant_path e0"]
        show ?thesis using h\<alpha> hconst_path hft hftp hcl2 hconst_liftp by (by100 blast)
      qed
      hence "ft 1 = e0" unfolding top1_constant_path_def by (by100 simp)
      thus ?thesis using hftilde by (by100 simp)
    qed
    qed
  qed
  \<comment> \<open>Helper: ftilde(y') equals the endpoint of ANY lift of f\<circ>\<alpha> from e0, for any path \<alpha> from y0 to y'.\<close>
  have ftilde_eq_lift: "\<And>y' \<alpha> ft'. y' \<in> Y \<Longrightarrow> top1_is_path_on Y TY y0 y' \<alpha> \<Longrightarrow>
      top1_is_path_on E TE e0 (ft' 1) ft' \<Longrightarrow> (\<forall>s\<in>I_set. p (ft' s) = f (\<alpha> s)) \<Longrightarrow>
      ftilde y' = ft' 1"
  proof -
    fix y' \<alpha>' ft'
    assume hy': "y' \<in> Y" and h\<alpha>': "top1_is_path_on Y TY y0 y' \<alpha>'"
        and hft': "top1_is_path_on E TE e0 (ft' 1) ft'"
        and hft'p: "\<forall>s\<in>I_set. p (ft' s) = f (\<alpha>' s)"
    \<comment> \<open>Get the SOME-chosen path and lift for ftilde(y').\<close>
    let ?\<alpha>_s = "SOME \<alpha>. top1_is_path_on Y TY y0 y' \<alpha>"
    have "\<exists>\<alpha>. top1_is_path_on Y TY y0 y' \<alpha>" using hpath_exists hy' by (by100 blast)
    hence h\<alpha>_s: "top1_is_path_on Y TY y0 y' ?\<alpha>_s" by (rule someI_ex)
    let ?ft_s = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
    have "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f (?\<alpha>_s s))"
      using hlift_exists hy' h\<alpha>_s by (by100 blast)
    hence hft_s: "top1_is_path_on E TE e0 (?ft_s 1) ?ft_s \<and> (\<forall>s\<in>I_set. p (?ft_s s) = f (?\<alpha>_s s))"
      by (rule someI_ex)
    have hftilde_eq: "ftilde y' = ?ft_s 1" unfolding ftilde_def by (by100 simp)
    \<comment> \<open>By hwd: ft' 1 = ft_s 1.\<close>
    from hwd[rule_format, OF hy', of \<alpha>' ?\<alpha>_s ft' ?ft_s]
    have "ft' 1 = ?ft_s 1" using h\<alpha>' h\<alpha>_s hft' hft'p hft_s by (by100 blast)
    thus "ftilde y' = ft' 1" using hftilde_eq by (by100 simp)
  qed
  \<comment> \<open>Step 5: ftilde is continuous.
     For y \<in> Y, let U be evenly covered nbhd of f(y) in B.
     By local path-connectivity of Y, get path-connected open V \<ni> y with f(V) \<subseteq> U.
     Let W0 be the sheet over U containing ftilde(y).
     For y' \<in> V: extend path (y0\<rightarrow>y) with segment (y\<rightarrow>y' in V).
     The lift of the segment stays in W0 (sheets are homeomorphic to U).
     So ftilde|_V = (p|_{W0})\<inverse> \<circ> f|_V, which is continuous.\<close>
  have hft_cont: "top1_continuous_map_on Y TY E TE ftilde"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>Y. ftilde y \<in> E" using hft_props by (by100 blast)
  next
    show "\<forall>W\<in>TE. {y \<in> Y. ftilde y \<in> W} \<in> TY"
    proof (intro ballI)
      fix W assume hW: "W \<in> TE"
      \<comment> \<open>For each y in the preimage, find a neighborhood mapping into W.\<close>
      have "\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. \<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
      proof (intro ballI)
        fix y assume hy_pre: "y \<in> {y \<in> Y. ftilde y \<in> W}"
        hence hyY: "y \<in> Y" and hfty_W: "ftilde y \<in> W" by (by100 blast)+
        have hfty_E: "ftilde y \<in> E" using hft_props hyY by (by100 blast)
        have hfy: "p (ftilde y) = f y" using hft_props hyY by (by100 blast)
        have hfy_B: "f y \<in> B"
          using hf hyY unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Get evenly covered U of f(y) in B.\<close>
        obtain U where hU: "f y \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
          using hcov hfy_B unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_cover: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                         (subspace_topology B TB U) p"
          using hec unfolding top1_evenly_covered_on_def by blast
        \<comment> \<open>ftilde(y) is in some sheet W0.\<close>
        have "ftilde y \<in> {x\<in>E. p x \<in> U}"
        proof -
          have "ftilde y \<in> E" by (rule hfty_E)
          moreover have "p (ftilde y) \<in> U" using hfy hU by (by100 simp)
          ultimately show ?thesis by (by100 blast)
        qed
        hence "ftilde y \<in> \<Union>\<V>" using hV_cover by (by100 simp)
        then obtain W0 where hW0: "W0 \<in> \<V>" and hfty_W0: "ftilde y \<in> W0" by (by100 blast)
        \<comment> \<open>W0 \<inter> W is open in E, contains ftilde(y).\<close>
        have hW0_open: "W0 \<in> TE" using hV_open hW0 unfolding openin_on_def by (by100 blast)
        \<comment> \<open>p is a homeomorphism on W0 → U.\<close>
        have hp_homeo: "top1_homeomorphism_on W0 (subspace_topology E TE W0) U
            (subspace_topology B TB U) p" using hV_homeo hW0 by (by100 blast)
        have hp_inj: "inj_on p W0"
          using hp_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        \<comment> \<open>U is open in B.\<close>
        have hU_open: "openin_on B TB U"
          using hec unfolding top1_evenly_covered_on_def by (by100 blast)
        have hU_TB: "U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>f\<inverse>(U) is open in Y.\<close>
        have hfU: "{y\<in>Y. f y \<in> U} \<in> TY"
          using hf hU_TB unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>By local path-connectivity: get path-connected open V \<subseteq> f\<inverse>(U) with y \<in> V.\<close>
        obtain V0 where hV0_TY: "V0 \<in> TY" and hy_V0: "y \<in> V0"
            and hV0_sub: "V0 \<subseteq> {y\<in>Y. f y \<in> U}"
            and hV0_pc: "top1_path_connected_on V0 (subspace_topology Y TY V0)"
        proof -
          \<comment> \<open>f\<inverse>(U) is open in Y, contains y.\<close>
          have hfU_nbhd: "neighborhood_of y Y TY {y\<in>Y. f y \<in> U}"
            unfolding neighborhood_of_def using hfU hyY hU by (by100 blast)
          have hfU_sub: "{y\<in>Y. f y \<in> U} \<subseteq> Y" by (by100 blast)
          \<comment> \<open>By local path-connectivity of Y at y: get path-connected open V0 \<subseteq> f\<inverse>(U).\<close>
          have hlpc_y: "top1_locally_path_connected_at Y TY y"
            using hYlpc hyY unfolding top1_locally_path_connected_on_def by (by100 blast)
          obtain V0' where hV0'_nbhd: "neighborhood_of y Y TY V0'"
              and hV0'_sub: "V0' \<subseteq> {y\<in>Y. f y \<in> U}" and hV0'_Y: "V0' \<subseteq> Y"
              and hV0'_pc: "top1_path_connected_on V0' (subspace_topology Y TY V0')"
          proof -
            from hlpc_y[unfolded top1_locally_path_connected_at_def,
                rule_format, of "{y\<in>Y. f y \<in> U}"]
            show ?thesis using hfU_nbhd hfU_sub that by (by100 blast)
          qed
          \<comment> \<open>neighborhood_of means V0' \<in> TY \<and> y \<in> V0'.\<close>
          have hV0'_TY: "V0' \<in> TY" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          have hy_V0': "y \<in> V0'" using hV0'_nbhd unfolding neighborhood_of_def by (by100 blast)
          show ?thesis using that[OF hV0'_TY hy_V0' hV0'_sub hV0'_pc] .
        qed
        \<comment> \<open>For y' \<in> V0: ftilde(y') \<in> W0 because the lift stays in the sheet.\<close>
        \<comment> \<open>ftilde maps V0 into W0: for y' \<in> V0, the lift of f\<circ>\<sigma> (path y\<rightarrow>y' in V0)
           from ftilde(y) stays in W0 (since f\<circ>\<sigma> stays in U and p|_{W0}: W0 \<cong> U).\<close>
        \<comment> \<open>p|_{W0} is a bijection W0 → U.\<close>
        have hp_bij: "bij_betw p W0 U"
          using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>ftilde(y) = inv_into W0 p (f y).\<close>
        have hfty_inv: "ftilde y = inv_into W0 p (f y)"
          using inv_into_f_eq[OF hp_inj hfty_W0] hfy by (by100 simp)
        have hftilde_V0: "\<forall>y'\<in>V0. ftilde y' \<in> W0"
        proof (intro ballI)
          fix y' assume hy'V0: "y' \<in> V0"
          have hy'Y: "y' \<in> Y" using hy'V0 hV0_sub by (by100 blast)
          have hfy'U: "f y' \<in> U" using hy'V0 hV0_sub by (by100 blast)
          have hfy'_pW0: "f y' \<in> p ` W0" using hp_bij hfy'U unfolding bij_betw_def by (by100 blast)
          have hinv_y'_W0: "inv_into W0 p (f y') \<in> W0" by (rule inv_into_into[OF hfy'_pW0])
          \<comment> \<open>Path from y to y' in V0.\<close>
          obtain \<sigma> where h\<sigma>: "top1_is_path_on V0 (subspace_topology Y TY V0) y y' \<sigma>"
            using hV0_pc hy_V0 hy'V0 unfolding top1_path_connected_on_def by (by100 auto)
          \<comment> \<open>\<sigma> as ambient path.\<close>
          have hV0_sub_Y: "V0 \<subseteq> Y" using hV0_sub by (by100 blast)
          have h\<sigma>_cont_V0: "top1_continuous_map_on I_set I_top V0 (subspace_topology Y TY V0) \<sigma>"
            using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
          have h\<sigma>_in_V0: "\<forall>s\<in>I_set. \<sigma> s \<in> V0"
            using h\<sigma>_cont_V0 unfolding top1_continuous_map_on_def by (by100 blast)
          have h\<sigma>_Y: "top1_is_path_on Y TY y y' \<sigma>"
          proof -
            have hincl: "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
            proof -
              have "top1_continuous_map_on V0 (subspace_topology Y TY V0) Y TY (\<lambda>x. x)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTY, unfolded id_def] hV0_sub_Y])
              thus ?thesis .
            qed
            have "top1_continuous_map_on I_set I_top Y TY ((\<lambda>x. x) \<circ> \<sigma>)"
              by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_V0 hincl])
            moreover have "(\<lambda>x::'c. x) \<circ> \<sigma> = \<sigma>" by (rule ext) (by100 simp)
            ultimately have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>" by (by100 simp)
            have "\<sigma> 0 = y" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            have "\<sigma> 1 = y'" using h\<sigma> unfolding top1_is_path_on_def by (by100 blast)
            show ?thesis unfolding top1_is_path_on_def using h\<sigma>_cont_Y \<open>\<sigma> 0 = y\<close> \<open>\<sigma> 1 = y'\<close>
              by (by100 blast)
          qed
          \<comment> \<open>Path from y0 to y.\<close>
          obtain \<alpha>0 where h\<alpha>0: "top1_is_path_on Y TY y0 y \<alpha>0"
            using hpath_exists hyY by (by100 blast)
          \<comment> \<open>Lift of f\<circ>\<alpha>0 from e0.\<close>
          obtain ft0 where hft0: "top1_is_path_on E TE e0 (ft0 1) ft0"
              and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = f (\<alpha>0 s)"
            using hlift_exists hyY h\<alpha>0 by (by100 blast)
          \<comment> \<open>ft0 1 = ftilde y (by ftilde_eq_lift).\<close>
          have hft0_end: "ft0 1 = ftilde y"
            using ftilde_eq_lift[OF hyY h\<alpha>0 hft0 hft0p] by (by100 simp)
          \<comment> \<open>Concatenate: \<alpha>0\<cdot>\<sigma> is a path from y0 to y'.\<close>
          have h\<alpha>0\<sigma>: "top1_is_path_on Y TY y0 y' (top1_path_product \<alpha>0 \<sigma>)"
            by (rule top1_path_product_is_path[OF hTY h\<alpha>0 h\<sigma>_Y])
          \<comment> \<open>Construct the lift of f\<circ>(\<alpha>0\<cdot>\<sigma>) as ft0 \<cdot> (inv_into W0 p \<circ> f \<circ> \<sigma>).\<close>
          let ?inv_lift = "\<lambda>s. inv_into W0 p (f (\<sigma> s))"
          \<comment> \<open>?inv_lift is a path in W0 \<subseteq> E from ftilde(y) to inv_into W0 p (f y').\<close>
          have hinvl_path: "top1_is_path_on E TE (ftilde y) (inv_into W0 p (f y')) ?inv_lift"
          proof -
            \<comment> \<open>Continuity: inv_into W0 p \<circ> f \<circ> \<sigma> is continuous I_set \<rightarrow> E.\<close>
            \<comment> \<open>f\<circ>\<sigma>: I_set \<rightarrow> U (f continuous, \<sigma> maps V0 \<subseteq> f\<inverse>(U)).\<close>
            \<comment> \<open>inv_into W0 p: U \<rightarrow> W0 \<subseteq> E (inverse of homeomorphism).\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0)
                (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>f\<circ>\<sigma> maps I_set into U (via V0).\<close>
            have hf\<sigma>_cont: "top1_continuous_map_on I_set I_top U (subspace_topology B TB U) (f \<circ> \<sigma>)"
            proof -
              \<comment> \<open>\<sigma>: I \<rightarrow> Y continuous, f: Y \<rightarrow> B continuous. f\<circ>\<sigma>: I \<rightarrow> B continuous.\<close>
              have h\<sigma>_cont_Y: "top1_continuous_map_on I_set I_top Y TY \<sigma>"
                using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              have "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                by (rule top1_continuous_map_on_comp[OF h\<sigma>_cont_Y hf])
              \<comment> \<open>f\<circ>\<sigma> maps into U (V0 \<subseteq> f\<inverse>(U) and \<sigma> maps into V0).\<close>
              moreover have "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
              proof (intro ballI)
                fix s assume "s \<in> I_set"
                hence "\<sigma> s \<in> V0" using h\<sigma>_in_V0 by (by100 blast)
                hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
                thus "(f \<circ> \<sigma>) s \<in> U" by (by100 simp)
              qed
              \<comment> \<open>Restrict codomain to U with subspace topology.\<close>
              moreover have hU_sub_B: "U \<subseteq> B"
                using hU_open unfolding openin_on_def by (by100 blast)
              ultimately show ?thesis
              proof -
                assume hf\<sigma>B: "top1_continuous_map_on I_set I_top B TB (f \<circ> \<sigma>)"
                    and hrange: "\<forall>s\<in>I_set. (f \<circ> \<sigma>) s \<in> U"
                show ?thesis
                  by (rule continuous_map_restrict_codomain[OF hf\<sigma>B hrange hU_sub_B])
              qed
            qed
            \<comment> \<open>Composition: inv_into \<circ> f \<circ> \<sigma> maps I_set to W0.\<close>
            have "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) (inv_into W0 p \<circ> (f \<circ> \<sigma>))"
              by (rule top1_continuous_map_on_comp[OF hf\<sigma>_cont hinv_cont])
            moreover have "(inv_into W0 p \<circ> (f \<circ> \<sigma>)) = ?inv_lift"
              by (rule ext) (by100 simp)
            ultimately have hinvl_cont_W0: "top1_continuous_map_on I_set I_top W0 (subspace_topology E TE W0) ?inv_lift"
              by (by100 simp)
            \<comment> \<open>W0 \<subseteq> E, so compose with inclusion to get continuity into E.\<close>
            have hW0_sub: "W0 \<subseteq> E" using hV_open hW0 unfolding openin_on_def by (by100 blast)
            have hW0_incl: "top1_continuous_map_on W0 (subspace_topology E TE W0) E TE (\<lambda>x. x)"
              using top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTE, unfolded id_def] hW0_sub] by (by100 simp)
            have "top1_continuous_map_on I_set I_top E TE ((\<lambda>x. x) \<circ> ?inv_lift)"
              by (rule top1_continuous_map_on_comp[OF hinvl_cont_W0 hW0_incl])
            moreover have "(\<lambda>x::'a. x) \<circ> ?inv_lift = ?inv_lift" by (rule ext) (by100 simp)
            ultimately have hinvl_cont_E: "top1_continuous_map_on I_set I_top E TE ?inv_lift"
              by (by100 simp)
            \<comment> \<open>Endpoints.\<close>
            have hinvl_0: "?inv_lift 0 = ftilde y"
            proof -
              have "\<sigma> 0 = y" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              hence "?inv_lift 0 = inv_into W0 p (f y)" by (by100 simp)
              also have "\<dots> = ftilde y" using hfty_inv by (by100 simp)
              finally show ?thesis .
            qed
            have hinvl_1: "?inv_lift 1 = inv_into W0 p (f y')"
            proof -
              have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
              thus ?thesis by (by100 simp)
            qed
            show ?thesis unfolding top1_is_path_on_def
              using hinvl_cont_E hinvl_0 hinvl_1 by (by100 blast)
          qed
          have hinvl_lift: "\<forall>s\<in>I_set. p (?inv_lift s) = f (\<sigma> s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            have "\<sigma> s \<in> V0" using h\<sigma>_in_V0 hs by (by100 blast)
            hence "f (\<sigma> s) \<in> U" using hV0_sub by (by100 blast)
            hence "f (\<sigma> s) \<in> p ` W0" using hp_bij unfolding bij_betw_def by (by100 blast)
            show "p (?inv_lift s) = f (\<sigma> s)" by (rule f_inv_into_f[OF \<open>f (\<sigma> s) \<in> p ` W0\<close>])
          qed
          \<comment> \<open>The concatenation ft0 \<cdot> inv_lift is a path from e0 to inv_into W0 p (f y').\<close>
          define cl where "cl = top1_path_product ft0 ?inv_lift"
          have hcl_path: "top1_is_path_on E TE e0 (inv_into W0 p (f y')) cl"
          proof -
            have "ft0 1 = ftilde y" by (rule hft0_end)
            hence hft0': "top1_is_path_on E TE e0 (ftilde y) ft0"
              using hft0 by (by100 simp)
            show ?thesis unfolding cl_def by (rule top1_path_product_is_path[OF hTE hft0' hinvl_path])
          qed
          have hcl_lift: "\<forall>s\<in>I_set. p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
          proof (intro ballI)
            fix s assume hs: "s \<in> I_set"
            hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
            show "p (cl s) = f ((top1_path_product \<alpha>0 \<sigma>) s)"
            proof (cases "s \<le> 1/2")
              case True
              have "cl s = ft0 (2 * s)" unfolding cl_def top1_path_product_def using True by (by100 simp)
              moreover have "p (ft0 (2 * s)) = f (\<alpha>0 (2 * s))"
              proof -
                have "2 * s \<in> I_set" unfolding top1_unit_interval_def using hs01 True by (by100 simp)
                thus ?thesis using hft0p by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<alpha>0 (2 * s)"
                unfolding top1_path_product_def using True by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            next
              case False
              hence hgt: "s > 1/2" by (by100 simp)
              have "cl s = ?inv_lift (2 * s - 1)" unfolding cl_def top1_path_product_def using False by (by100 simp)
              moreover have "p (?inv_lift (2 * s - 1)) = f (\<sigma> (2 * s - 1))"
              proof -
                have "2 * s - 1 \<in> I_set" unfolding top1_unit_interval_def using hs01 hgt by (by100 simp)
                thus ?thesis using hinvl_lift by (by100 blast)
              qed
              moreover have "(top1_path_product \<alpha>0 \<sigma>) s = \<sigma> (2 * s - 1)"
                unfolding top1_path_product_def using False by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
          qed
          \<comment> \<open>By ftilde_eq_lift: ftilde(y') = endpoint of this lift = inv_into W0 p (f y').\<close>
          \<comment> \<open>cl 1 = inv_into W0 p (f y') (endpoint computation).\<close>
          have hcl_end: "cl 1 = inv_into W0 p (f y')"
          proof -
            have "cl 1 = ?inv_lift (2 * (1::real) - 1)" unfolding cl_def top1_path_product_def by (by100 simp)
            moreover have "(2::real) * 1 - 1 = (1::real)" by (by100 simp)
            ultimately have "cl 1 = ?inv_lift 1" by (by100 simp)
            moreover have "?inv_lift 1 = inv_into W0 p (f (\<sigma> 1))" by (by100 simp)
            moreover have "\<sigma> 1 = y'" using h\<sigma>_Y unfolding top1_is_path_on_def by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>ftilde(y') = cl 1 (by ftilde_eq_lift).\<close>
          have hcl_lift2: "\<forall>s\<in>I_set. p (cl s) = f (top1_path_product \<alpha>0 \<sigma> s)"
            using hcl_lift by (by100 simp)
          have hcl_path2: "top1_is_path_on E TE e0 (cl 1) cl"
          proof -
            have "cl 1 = inv_into W0 p (f y')" using hcl_end .
            thus ?thesis using hcl_path by (by100 simp)
          qed
          have "ftilde y' = cl 1"
            by (rule ftilde_eq_lift[OF hy'Y h\<alpha>0\<sigma> hcl_path2 hcl_lift2])
          hence "ftilde y' = inv_into W0 p (f y')" using hcl_end by (by100 simp)
          thus "ftilde y' \<in> W0" using hinv_y'_W0 by (by100 simp)
        qed
        \<comment> \<open>hftilde_V0 proved above.\<close>
        \<comment> \<open>V' = V0 \<inter> ftilde\<inverse>(W0 \<inter> W). Since ftilde(V0) \<subseteq> W0, this simplifies.\<close>
        \<comment> \<open>Actually, we need V' \<subseteq> {y \<in> Y. ftilde y \<in> W}. Use W0 \<inter> W.\<close>
        \<comment> \<open>W0 \<inter> W is open in E. p maps W0 homeomorphically to U.
           So p(W0 \<inter> W) is open in U, hence open in B.
           V' = V0 \<inter> f\<inverse>(p(W0 \<inter> W)) is open in Y.\<close>
        \<comment> \<open>ftilde on V0 equals (p|_{W0})\<inverse> \<circ> f. For ftilde(y') \<in> W, need f(y') \<in> p(W0 \<inter> W).\<close>
        have hftilde_eq: "\<forall>y'\<in>V0. ftilde y' = inv_into W0 p (f y')"
        proof (intro ballI)
          fix y' assume "y' \<in> V0"
          hence "ftilde y' \<in> W0" using hftilde_V0 by (by100 blast)
          have hy'Y: "y' \<in> Y" using \<open>y' \<in> V0\<close> hV0_sub by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          thus "ftilde y' = inv_into W0 p (f y')"
            using inv_into_f_eq[OF hp_inj \<open>ftilde y' \<in> W0\<close> \<open>p (ftilde y') = f y'\<close>]
            by (by100 simp)
        qed
        \<comment> \<open>p(W0 \<inter> W) is open in B (p homeo on W0, W0 \<inter> W open in W0).\<close>
        have hpWW: "p ` (W0 \<inter> W) \<subseteq> U"
        proof -
          have "W0 \<subseteq> {x\<in>E. p x \<in> U}" using hV_cover hW0 by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have hpWW_open: "{y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
        proof -
          \<comment> \<open>p(W0 \<inter> W) is open in B.\<close>
          \<comment> \<open>W0 \<inter> W is open in E. Its intersection with W0 (= W0 \<inter> W) is open in
             the subspace W0. p maps open subsets of W0 to open subsets of U (homeomorphism).
             U open in B, so the image is open in B.\<close>
          have "p ` (W0 \<inter> W) \<in> TB"
          proof -
            \<comment> \<open>W0 \<inter> W is open in the subspace topology of W0.\<close>
            have hWW_sub: "W0 \<inter> W \<in> subspace_topology E TE W0"
              unfolding subspace_topology_def using hW hW0_open by (by100 blast)
            \<comment> \<open>p maps W0 homeomorphically to U. Open subsets map to open subsets.\<close>
            have hp_bij: "bij_betw p W0 U"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_cont_W0: "top1_continuous_map_on W0 (subspace_topology E TE W0) U (subspace_topology B TB U) p"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>The inverse p\<inverse> is continuous on U → W0.\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) W0 (subspace_topology E TE W0) (inv_into W0 p)"
              using hp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>Preimage of W0\<inter>W under p\<inverse> = p(W0\<inter>W). By continuity of p\<inverse>, this is open in U.\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U"
              using hinv_cont hWW_sub unfolding top1_continuous_map_on_def by (by100 blast)
            \<comment> \<open>{u \<in> U | inv(u) \<in> W0\<inter>W} = p(W0\<inter>W) (since p is bijection on W0).\<close>
            have "{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} = p ` (W0 \<inter> W)"
            proof (rule set_eqI)
              fix u show "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<longleftrightarrow> u \<in> p ` (W0 \<inter> W)"
              proof
                assume hu: "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                hence "inv_into W0 p u \<in> W0 \<inter> W" and "u \<in> U" by (by100 blast)+
                have "u \<in> p ` W0" using hp_bij \<open>u \<in> U\<close> unfolding bij_betw_def by (by100 blast)
                have "p (inv_into W0 p u) = u" by (rule f_inv_into_f[OF \<open>u \<in> p ` W0\<close>])
                thus "u \<in> p ` (W0 \<inter> W)" using \<open>inv_into W0 p u \<in> W0 \<inter> W\<close> by (by100 force)
              next
                assume "u \<in> p ` (W0 \<inter> W)"
                then obtain e where he: "e \<in> W0 \<inter> W" and hue: "u = p e" by (by100 blast)
                have "e \<in> W0" using he by (by100 blast)
                have "u \<in> U" using hpWW \<open>u \<in> p ` (W0 \<inter> W)\<close> by (by100 blast)
                have "inv_into W0 p u = e"
                  using inv_into_f_eq[OF hp_inj \<open>e \<in> W0\<close>] hue by (by100 simp)
                thus "u \<in> {u \<in> U. inv_into W0 p u \<in> W0 \<inter> W}"
                  using \<open>u \<in> U\<close> he by (by100 simp)
              qed
            qed
            \<comment> \<open>So p(W0\<inter>W) is open in the subspace U of B.\<close>
            hence "p ` (W0 \<inter> W) \<in> subspace_topology B TB U"
              using \<open>{u \<in> U. inv_into W0 p u \<in> W0 \<inter> W} \<in> subspace_topology B TB U\<close>
              by (by100 simp)
            \<comment> \<open>Open in U subspace = V \<inter> U for some V \<in> TB. Since U \<in> TB and V \<in> TB, V\<inter>U \<in> TB.\<close>
            then obtain V where hV_TB: "V \<in> TB" and hpWW_eq: "p ` (W0 \<inter> W) = U \<inter> V"
              unfolding subspace_topology_def by (by100 auto)
            have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TB \<longrightarrow> \<Inter>F \<in> TB"
              using hTB unfolding is_topology_on_def by (by100 blast)
            hence "U \<inter> V \<in> TB"
            proof -
              have "finite {U, V}" by (by100 simp)
              moreover have "{U, V} \<noteq> {}" by (by100 blast)
              moreover have "{U, V} \<subseteq> TB" using hU_TB hV_TB by (by100 blast)
              ultimately have "\<Inter>{U, V} \<in> TB"
                using \<open>\<forall>F. _\<close> by (by100 blast)
              moreover have "\<Inter>{U, V} = U \<inter> V" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            thus "p ` (W0 \<inter> W) \<in> TB" using hpWW_eq by (by100 simp)
          qed
          thus ?thesis using hf unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        let ?V' = "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
        have hV'_TY: "?V' \<in> TY"
        proof -
          have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
            using hTY unfolding is_topology_on_def by (by100 blast)
          hence "V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)} \<in> TY"
          proof -
            have hfin: "finite {V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}}" by (by100 simp)
            have hne: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<noteq> {}" by (by100 blast)
            have hsub: "{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<subseteq> TY"
              using hV0_TY hpWW_open by (by100 blast)
            have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} \<in> TY"
              using \<open>\<forall>F. _\<close> hfin hne hsub by (by100 blast)
            moreover have "\<Inter>{V0, {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}} = V0 \<inter> {y\<in>Y. f y \<in> p ` (W0 \<inter> W)}"
              by (by100 auto)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis by (by100 simp)
        qed
        have hy_V': "y \<in> ?V'"
        proof -
          have "y \<in> V0" by (rule hy_V0)
          moreover have "y \<in> Y" by (rule hyY)
          moreover have "f y \<in> p ` (W0 \<inter> W)"
          proof -
            have "ftilde y \<in> W0 \<inter> W" using hfty_W0 hfty_W by (by100 blast)
            hence "p (ftilde y) \<in> p ` (W0 \<inter> W)" by (by100 blast)
            thus ?thesis using hfy by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        have hV'_sub: "?V' \<subseteq> {y \<in> Y. ftilde y \<in> W}"
        proof (rule subsetI)
          fix y' assume hy': "y' \<in> ?V'"
          hence hy'V0: "y' \<in> V0" and hy'Y: "y' \<in> Y" and hfy'_pWW: "f y' \<in> p ` (W0 \<inter> W)"
            by (by100 blast)+
          \<comment> \<open>f(y') \<in> p(W0 \<inter> W) means \<exists>e \<in> W0 \<inter> W. p(e) = f(y').
             ftilde(y') = inv_into W0 p (f y') = e \<in> W0 \<inter> W \<subseteq> W.\<close>
          from hfy'_pWW obtain e where he: "e \<in> W0" "e \<in> W" and hpe: "p e = f y'" by (by100 auto)
          have "ftilde y' \<in> W0" using hftilde_V0 hy'V0 by (by100 blast)
          have "p (ftilde y') = f y'" using hft_props hy'Y by (by100 blast)
          hence "ftilde y' = e"
          proof -
            have "p (ftilde y') = p e" using \<open>p (ftilde y') = f y'\<close> hpe by (by100 simp)
            moreover have "ftilde y' \<in> W0" by (rule \<open>ftilde y' \<in> W0\<close>)
            moreover have "e \<in> W0" using he by (by100 blast)
            ultimately show ?thesis using hp_inj unfolding inj_on_def by (by100 fast)
          qed
          hence "ftilde y' \<in> W" using he by (by100 blast)
          thus "y' \<in> {y \<in> Y. ftilde y \<in> W}" using hy'Y by (by100 blast)
        qed
        show "\<exists>V\<in>TY. y \<in> V \<and> V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
          apply (rule bexI[where x="?V'"])
          using hy_V' hV'_sub hV'_TY by (by100 blast)+
      qed
      \<comment> \<open>Preimage is union of open neighborhoods, hence open.\<close>
      have "{y \<in> Y. ftilde y \<in> W} = \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
      proof (rule set_eqI)
        fix y show "y \<in> {y \<in> Y. ftilde y \<in> W} \<longleftrightarrow> y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}"
        proof
          assume "y \<in> {y \<in> Y. ftilde y \<in> W}"
          then obtain V where "V \<in> TY" "y \<in> V" "V \<subseteq> {y \<in> Y. ftilde y \<in> W}"
            using \<open>\<forall>y \<in> {y \<in> Y. ftilde y \<in> W}. _\<close> by (by100 blast)
          thus "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" by (by100 blast)
        next
          assume "y \<in> \<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}}" thus "y \<in> {y \<in> Y. ftilde y \<in> W}"
            by (by100 blast)
        qed
      qed
      moreover have "\<Union>{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<in> TY"
      proof -
        have "\<forall>U. U \<subseteq> TY \<longrightarrow> \<Union>U \<in> TY"
          using hTY unfolding is_topology_on_def by (by100 blast)
        moreover have "{V \<in> TY. V \<subseteq> {y \<in> Y. ftilde y \<in> W}} \<subseteq> TY" by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show "{y \<in> Y. ftilde y \<in> W} \<in> TY" by (by100 simp)
    qed
  qed
  show ?thesis using hft_props hft_cont by (by100 blast)
qed

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
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
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
  \<comment> \<open>p_*(π₁(E)) = p'_*(π₁(E')) because p=p'∘h on E, h_* is bijective (homeomorphism),
     and functoriality gives p_* = p'_* ∘ h_*. So im(p_*) = im(p'_* ∘ h_*) = im(p'_*).\<close>
  \<comment> \<open>By functoriality + p=p'\<circ>h on E + h_* bijective:
     p_* = (p'\<circ>h)_* = p'_* \<circ> h_*, so im(p_*) = p'_*(im(h_*)) = p'_*(π₁(E')).\<close>
  show "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  proof -
    have hTE: "is_topology_on E TE"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on E TE E' TE' h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_bij: "bij_betw h E E'"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh_inj: "inj_on h E"
      using hh_bij unfolding bij_betw_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    have hp'h_cont: "top1_continuous_map_on E TE B TB (p' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hp'_cont])
    \<comment> \<open>p and p'∘h agree on E: ∀e∈E. p(e) = (p'∘h)(e).\<close>
    have hp_agree: "\<forall>e\<in>E. p e = (p' \<circ> h) e"
      using hp by (by100 auto)
    have hp'h_e0: "(p' \<circ> h) e0 = b0"
      using he assms(7) by (by100 simp)
    \<comment> \<open>Basepoint membership.\<close>
    note he0_E = assms(12) and he0'_E' = assms(13) and hb0_B = assms(14)
    \<comment> \<open>h_* maps carrier(E) to carrier(E') (group hom property).\<close>
    have hh_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h)"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE hTE' he0_E he0'_E' hh_cont he])
    \<comment> \<open>h⁻¹ setup\<close>
    have hinv_e0': "inv_into E h e0' = e0"
      using inv_into_f_f[OF hh_inj he0_E] he by (by100 simp)
    have hhinv_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier E' TE' e0') (top1_fundamental_group_mul E' TE' e0')
        (top1_fundamental_group_carrier E TE e0) (top1_fundamental_group_mul E TE e0)
        (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTE he0'_E' he0_E hh_inv_cont hinv_e0'])
    \<comment> \<open>⊆: for c ∈ carrier(E, e0), induced_p(c) = induced_p'(h_*(c)) ∈ image_hom(E', p').\<close>
    \<comment> \<open>⊇: for c' ∈ carrier(E', e0'), induced_p'(c') = induced_p(h⁻¹_*(c')) ∈ image_hom(E, p).\<close>
    show ?thesis unfolding top1_fundamental_group_image_hom_def
    proof (rule set_eqI, rule iffI)
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
                 top1_fundamental_group_carrier E TE e0"
      then obtain c where hc: "c \<in> top1_fundamental_group_carrier E TE e0"
          and hd: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p c"
        by (by100 blast)
      \<comment> \<open>By induced_agree: induced_p(c) = induced_{p'∘h}(c).\<close>
      have hstep1: "top1_fundamental_group_induced_on E TE e0 B TB b0 p c
          = top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c"
        by (rule fundamental_group_induced_agree[OF hTE hTB he0_E hp_cont hp'h_cont hp_agree assms(5) hp'h_e0 hc])
      \<comment> \<open>By induced_comp: induced_{p'∘h}(c) = induced_p'(induced_h(c)).\<close>
      have hstep2: "top1_fundamental_group_induced_on E TE e0 B TB b0 (p' \<circ> h) c
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
              (top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c)"
        by (rule fundamental_group_induced_comp[OF hTE hTE' hTB hh_cont hp'_cont he0_E he assms(7) hc])
      \<comment> \<open>h_*(c) ∈ carrier(E', e0') (since h_* is a group hom).\<close>
      have hh_star: "top1_fundamental_group_induced_on E TE e0 E' TE' e0' h c
          \<in> top1_fundamental_group_carrier E' TE' e0'"
        using hh_hom hc unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
               top1_fundamental_group_carrier E' TE' e0'"
        using hd hstep1 hstep2 hh_star by (by100 blast)
    next
      fix d
      assume "d \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' `
                 top1_fundamental_group_carrier E' TE' e0'"
      then obtain c' where hc': "c' \<in> top1_fundamental_group_carrier E' TE' e0'"
          and hd: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'"
        by (by100 blast)
      \<comment> \<open>p' agrees with p∘h⁻¹ on E'.\<close>
      have hp'_agree: "\<forall>e'\<in>E'. p' e' = (p \<circ> inv_into E h) e'"
      proof (intro ballI)
        fix e' assume he': "e' \<in> E'"
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence hinv_E: "inv_into E h e' \<in> E"
          by (rule inv_into_into)
        have "e' \<in> h ` E" using he' hh_bij unfolding bij_betw_def by (by100 blast)
        hence "h (inv_into E h e') = e'"
          by (rule f_inv_into_f)
        hence "p' e' = p' (h (inv_into E h e'))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e')" using hp hinv_E by (by100 blast)
        finally show "p' e' = (p \<circ> inv_into E h) e'" by (by100 simp)
      qed
      have hphinv_cont: "top1_continuous_map_on E' TE' B TB (p \<circ> inv_into E h)"
        by (rule top1_continuous_map_on_comp[OF hh_inv_cont hp_cont])
      have hphinv_e0': "(p \<circ> inv_into E h) e0' = b0"
        using hinv_e0' assms(5) by (by100 simp)
      have hstep1': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c'
          = top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'"
        by (rule fundamental_group_induced_agree[OF hTE' hTB he0'_E' hp'_cont hphinv_cont hp'_agree assms(7) hphinv_e0' hc'])
      have hstep2': "top1_fundamental_group_induced_on E' TE' e0' B TB b0 (p \<circ> inv_into E h) c'
          = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              (top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c')"
        by (rule fundamental_group_induced_comp[OF hTE' hTE hTB hh_inv_cont hp_cont he0'_E' hinv_e0' assms(5) hc'])
      have hhinv_star: "top1_fundamental_group_induced_on E' TE' e0' E TE e0 (inv_into E h) c'
          \<in> top1_fundamental_group_carrier E TE e0"
        using hhinv_hom hc' unfolding top1_group_hom_on_def by (by100 blast)
      show "d \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p `
               top1_fundamental_group_carrier E TE e0"
        using hd hstep1' hstep2' hhinv_star by (by100 blast)
    qed
  qed
next
  \<comment> \<open>Backward: if subgroup images equal, use path-lifting to construct h.\<close>
  assume hH_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  \<comment> \<open>Construct h: E \<rightarrow> E' via path-lifting. For each e \<in> E, pick path \<alpha> from e0 to e,
     lift p\<circ>\<alpha> to E' starting at e0'. The endpoint is h(e).\<close>
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hp_cont: "top1_continuous_map_on E TE B TB p"
    by (rule top1_covering_map_on_continuous[OF assms(4)])
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  \<comment> \<open>For each e \<in> E, paths from e0 exist (path-connected).\<close>
  \<comment> \<open>For each path, p\<circ>\<alpha> can be lifted to E' (Lemma_54_1).\<close>
  \<comment> \<open>The lift endpoint is independent of the chosen path (well-definedness via Theorem_54_3
     + subgroup equality hH_eq).\<close>
  \<comment> \<open>Define h via some path choice.\<close>
  \<comment> \<open>Apply general lifting criterion to construct h and h'.\<close>
  have hpe0: "p e0 = b0" by (rule assms(5))
  have hp'e0': "p' e0' = b0" by (rule assms(7))
  \<comment> \<open>For h: lift p (base map E\<rightarrow>B) to E' via p' (covering E'\<rightarrow>B).\<close>
  have h_exists: "\<exists>h. (\<forall>e\<in>E. h e \<in> E') \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'
      \<and> top1_continuous_map_on E TE E' TE' h"
  proof -
    \<comment> \<open>Subgroup condition: p_*(\<pi>_1(E)) \<subseteq> p'_*(\<pi>_1(E')), with basepoints at p'(e0') = b0.\<close>
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (p' e0') p
        \<subseteq> top1_fundamental_group_image_hom E' TE' e0' B TB (p' e0') p'"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(6) hTE hTB hTE' hp_cont assms(8,10,12,13)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  \<comment> \<open>For h': lift p' (base map E'\<rightarrow>B) to E via p (covering E\<rightarrow>B).\<close>
  have h'_exists: "\<exists>h'. (\<forall>e'\<in>E'. h' e' \<in> E) \<and> (\<forall>e'\<in>E'. p (h' e') = p' e') \<and> h' e0' = e0
      \<and> top1_continuous_map_on E' TE' E TE h'"
  proof -
    have hsubgrp: "top1_fundamental_group_image_hom E' TE' e0' B TB (p e0) p'
        \<subseteq> top1_fundamental_group_image_hom E TE e0 B TB (p e0) p"
      using hH_eq hp'e0' hpe0 by (by100 simp)
    show ?thesis
      using general_lifting_criterion[OF assms(4) hTE' hTB hTE hp'_cont assms(9,11,13,12)
            _ hsubgrp] hpe0 hp'e0' by (by100 simp)
  qed
  obtain h where hh_E': "\<forall>e\<in>E. h e \<in> E'" and hh_lift: "\<forall>e\<in>E. p' (h e) = p e"
      and hh_e0: "h e0 = e0'" and hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using h_exists by (by100 blast)
  obtain h' where hh'_E: "\<forall>e'\<in>E'. h' e' \<in> E" and hh'_lift: "\<forall>e'\<in>E'. p (h' e') = p' e'"
      and hh'_e0: "h' e0' = e0" and hh'_cont: "top1_continuous_map_on E' TE' E TE h'"
    using h'_exists by (by100 blast)
  \<comment> \<open>h' \<circ> h = id on E: both lift p (i.e. p \<circ> (h'\<circ>h) = p \<circ> id = p on E),
     and agree at e0 (h'(h(e0)) = h'(e0') = e0). By covering_lift_unique_connected,
     h'\<circ>h = id on the connected space E.\<close>
  have hh'h_id: "\<forall>e\<in>E. h' (h e) = e"
  proof -
    have hh'h_cont: "top1_continuous_map_on E TE E TE (h' \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh_cont hh'_cont])
    have hh'h_lift: "\<forall>e\<in>E. p ((h' \<circ> h) e) = p (id e)"
    proof (intro ballI)
      fix e assume he: "e \<in> E"
      have "h e \<in> E'" using hh_E' he by (by100 blast)
      hence "p (h' (h e)) = p' (h e)" using hh'_lift by (by100 blast)
      also have "\<dots> = p e" using hh_lift he by (by100 blast)
      finally show "p ((h' \<circ> h) e) = p (id e)" by (by100 simp)
    qed
    have hh'h_e0: "(h' \<circ> h) e0 = id e0"
      using hh_e0 hh'_e0 by (by100 simp)
    have hid_cont: "top1_continuous_map_on E TE E TE id"
      using top1_continuous_map_on_id[OF hTE] .
    have hE_conn: "top1_connected_on E TE"
      by (rule path_connected_imp_connected[OF assms(8)])
    from covering_lift_unique_connected[OF assms(4) hTE hTB hTE hE_conn
        hh'h_cont hid_cont hh'h_lift assms(12) hh'h_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h \<circ> h' = id on E': symmetric argument.\<close>
  have hhh'_id: "\<forall>e'\<in>E'. h (h' e') = e'"
  proof -
    have hhh'_cont: "top1_continuous_map_on E' TE' E' TE' (h \<circ> h')"
      by (rule top1_continuous_map_on_comp[OF hh'_cont hh_cont])
    have hhh'_lift: "\<forall>e'\<in>E'. p' ((h \<circ> h') e') = p' (id e')"
    proof (intro ballI)
      fix e' assume he': "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      hence "p' (h (h' e')) = p (h' e')" using hh_lift by (by100 blast)
      also have "\<dots> = p' e'" using hh'_lift he' by (by100 blast)
      finally show "p' ((h \<circ> h') e') = p' (id e')" by (by100 simp)
    qed
    have hhh'_e0: "(h \<circ> h') e0' = id e0'"
      using hh'_e0 hh_e0 by (by100 simp)
    have hid_cont': "top1_continuous_map_on E' TE' E' TE' id"
      using top1_continuous_map_on_id[OF hTE'] .
    have hE'_conn: "top1_connected_on E' TE'"
      by (rule path_connected_imp_connected[OF assms(9)])
    from covering_lift_unique_connected[OF assms(6) hTE' hTB hTE' hE'_conn
        hhh'_cont hid_cont' hhh'_lift assms(13) hhh'_e0]
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>h is a homeomorphism: continuous bijection with continuous inverse h'.\<close>
  have hh_bij: "bij_betw h E E'"
  proof (unfold bij_betw_def, intro conjI)
    show "inj_on h E"
    proof (rule inj_onI)
      fix x y assume "x \<in> E" "y \<in> E" "h x = h y"
      have "x = h' (h x)" using hh'h_id[rule_format, OF \<open>x \<in> E\<close>] by (by100 simp)
      also have "\<dots> = h' (h y)" using \<open>h x = h y\<close> by (by100 simp)
      also have "\<dots> = y" using hh'h_id[rule_format, OF \<open>y \<in> E\<close>] by (by100 simp)
      finally show "x = y" .
    qed
    show "h ` E = E'"
    proof (rule set_eqI)
      fix e' show "e' \<in> h ` E \<longleftrightarrow> e' \<in> E'"
      proof
        assume "e' \<in> h ` E"
        then obtain e where "e \<in> E" "e' = h e" by (by100 blast)
        thus "e' \<in> E'" using hh_E' by (by100 blast)
      next
        assume "e' \<in> E'"
        hence "h (h' e') = e'" using hhh'_id by (by100 blast)
        moreover have hh'e'_E: "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
        ultimately have "h (h' e') = e'" by (by100 simp)
        hence "e' = h (h' e')" by (by100 simp)
        thus "e' \<in> h ` E" using hh'e'_E by (by100 force)
      qed
    qed
  qed
  have hh_inv_cont: "top1_continuous_map_on E' TE' E TE (inv_into E h)"
  proof -
    have "\<forall>e'\<in>E'. inv_into E h e' = h' e'"
    proof (intro ballI)
      fix e' assume "e' \<in> E'"
      have "h' e' \<in> E" using hh'_E \<open>e' \<in> E'\<close> by (by100 blast)
      moreover have "h (h' e') = e'" using hhh'_id \<open>e' \<in> E'\<close> by (by100 blast)
      ultimately show "inv_into E h e' = h' e'"
        using inv_into_f_eq[of h E "h' e'" e'] hh_bij
        unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>inv_into agrees with h' on E', and h' is continuous.\<close>
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix e' assume he': "e' \<in> E'"
      have "inv_into E h e' = h' e'" using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> he' by (by100 blast)
      moreover have "h' e' \<in> E" using hh'_E he' by (by100 blast)
      ultimately show "inv_into E h e' \<in> E" by (by100 simp)
    next
      fix V assume "V \<in> TE"
      \<comment> \<open>{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}\<close>
      have hset_eq: "{e'\<in>E'. inv_into E h e' \<in> V} = {e'\<in>E'. h' e' \<in> V}"
      proof (rule Collect_cong)
        fix e' show "(e' \<in> E' \<and> inv_into E h e' \<in> V) = (e' \<in> E' \<and> h' e' \<in> V)"
          using \<open>\<forall>e'\<in>E'. inv_into E h e' = h' e'\<close> by (by100 auto)
      qed
      have "{e'\<in>E'. h' e' \<in> V} \<in> TE'"
        using hh'_cont \<open>V \<in> TE\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      thus "{e'\<in>E'. inv_into E h e' \<in> V} \<in> TE'"
        using hset_eq by (by100 simp)
    qed
  qed
  have hhomeo: "top1_homeomorphism_on E TE E' TE' h"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on E TE" by (rule hTE)
    show "is_topology_on E' TE'" by (rule hTE')
    show "bij_betw h E E'" by (rule hh_bij)
    show "top1_continuous_map_on E TE E' TE' h" by (rule hh_cont)
    show "top1_continuous_map_on E' TE' E TE (inv_into E h)" by (rule hh_inv_cont)
  qed
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'"
    using hhomeo hh_lift hh_e0 by (by100 blast)
qed

text \<open>Basepoint change for image_hom: if \<alpha> is a path from e0 to e1 in a covering space E,
  then p_*(\<pi>_1(E, e1)) is the conjugate of p_*(\<pi>_1(E, e0)) by [p\<circ>\<alpha>]\<inverse>.\<close>
lemma basepoint_change_image_hom:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
      and he0: "e0 \<in> E" and he1: "e1 \<in> E"
      and h\<alpha>: "top1_is_path_on E TE e0 e1 \<alpha>"
      and hpe0: "p e0 = b0" and hpe1: "p e1 = b0"
      and hEpc: "top1_path_connected_on E TE"
  shows "top1_fundamental_group_image_hom E TE e1 B TB b0 p
      = (\<lambda>H. top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g})
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    {g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Proof via loop conjugation in E: for each direction, conjugate by \<alpha> resp. \<alpha>\<inverse>.\<close>
  \<comment> \<open>\<subseteq>: For d \<in> image_hom(E, e1): d = [p\<circ>g] for loop g at e1.
     Form \<alpha>\<cdot>g\<cdot>\<alpha>\<inverse> (loop at e0). [p\<circ>(\<alpha>\<cdot>g\<cdot>\<alpha>\<inverse>)] = [p\<circ>\<alpha>]\<cdot>[p\<circ>g]\<cdot>[rev(p\<circ>\<alpha>)] = c\<cdot>d\<cdot>inv(c).
     So c\<cdot>d\<cdot>inv(c) \<in> image_hom(E, e0). Thus d = inv(c)\<cdot>(c\<cdot>d\<cdot>inv(c))\<cdot>c \<in> conj(image_hom(E, e0)).\<close>
  \<comment> \<open>\<supseteq>: For h \<in> image_hom(E, e0): h = [p\<circ>f] for loop f at e0.
     Form \<alpha>\<inverse>\<cdot>f\<cdot>\<alpha> (loop at e1). [p\<circ>(\<alpha>\<inverse>\<cdot>f\<cdot>\<alpha>)] = inv(c)\<cdot>[p\<circ>f]\<cdot>c = inv(c)\<cdot>h\<cdot>c.
     So inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1). This means inv(c)\<cdot>(h\<cdot>c) = inv(c)\<cdot>h\<cdot>c \<in> image_hom(E, e1).\<close>
  \<comment> \<open>Key identities:
     p \<circ> path_product(path_product(rev(\<alpha>), f), \<alpha>)
     = path_product(path_product(p\<circ>rev(\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_product twice)
     = path_product(path_product(rev(p\<circ>\<alpha>), p\<circ>f), p\<circ>\<alpha>)   (comp_path_reverse)
     And rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1 (for f loop at e0).
     Similarly \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0 (for g loop at e1).\<close>
proof -
  let ?mulB = "top1_fundamental_group_mul B TB b0"
  let ?invB = "top1_fundamental_group_invg B TB b0"
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p \<circ> \<alpha>) g}"
  have hp_cont: "top1_continuous_map_on E TE B TB p" by (rule top1_covering_map_on_continuous[OF hcov])
  have hb0_B: "b0 \<in> B" using hp_cont he0 hpe0 unfolding top1_continuous_map_on_def by (by100 blast)
  have h\<alpha>_rev: "top1_is_path_on E TE e1 e0 (top1_path_reverse \<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>])
  have hp\<alpha>_loop: "top1_is_loop_on B TB b0 (p \<circ> \<alpha>)"
  proof -
    have "top1_continuous_map_on I_set I_top B TB (p \<circ> \<alpha>)"
      by (rule top1_continuous_map_on_comp)
         (use h\<alpha> hp_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
    moreover have "(p \<circ> \<alpha>) 0 = b0" using h\<alpha> hpe0 unfolding top1_is_path_on_def by (by100 simp)
    moreover have "(p \<circ> \<alpha>) 1 = b0" using h\<alpha> hpe1 unfolding top1_is_path_on_def by (by100 simp)
    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  qed
  have hp\<alpha>_rev_loop: "top1_is_loop_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>))"
    by (rule top1_path_reverse_is_loop[OF hp\<alpha>_loop])
  show ?thesis
  proof (rule set_eqI)
    fix d
    show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p \<longleftrightarrow>
        d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    proof
      \<comment> \<open>\<Rightarrow>: d = [p\<circ>g] for loop g at e1. Conjugate: \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is loop at e0.\<close>
      assume "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
      then obtain g where hg_loop: "top1_is_loop_on E TE e1 g"
          and hd_eq: "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>\<alpha>\<cdot>g\<cdot>rev(\<alpha>) is a loop at e0.\<close>
      have hg_path: "top1_is_path_on E TE e1 e1 g"
        using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj_loop: "top1_is_loop_on E TE e0
          (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
      proof -
        have "top1_is_path_on E TE e0 e1 (top1_path_product \<alpha> g)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha> hg_path])
        hence "top1_is_path_on E TE e0 e0 (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>_rev])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>[p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>))] = c \<cdot> d \<cdot> inv(c) \<in> image_hom(E, e0).\<close>
      \<comment> \<open>p\<circ>(\<alpha>\<cdot>g\<cdot>rev(\<alpha>)) = (p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>) by comp_path_product/reverse.\<close>
      have hp_conj: "p \<circ> (top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>))
          = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>So [p\<circ>conj] = mul(mul(c, d), inv(c)) and this is in image_hom(E, e0).\<close>
      \<comment> \<open>Then d = inv(c) \<cdot> [p\<circ>conj] \<cdot> c, so d \<in> conj(image_hom(E, e0)).\<close>
      show "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      proof -
        \<comment> \<open>d = [p\<circ>g], the class of p\<circ>g at b0.\<close>
        have hg_loop_E: "top1_is_loop_on E TE e1 g" by (rule hg_loop)
        have hpg_loop: "top1_is_loop_on B TB b0 (p \<circ> g)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> g)"
            by (rule top1_continuous_map_on_comp)
               (use hg_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> g) 0 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> g) 1 = b0" using hg_loop hpe1 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e1 B TB b0 p
              {k. top1_loop_equiv_on E TE e1 g k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
            then obtain g' where hg'_eq: "top1_loop_equiv_on E TE e1 g g'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> g') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hg'_loop: "top1_is_loop_on E TE e1 g'"
              using hg'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> g) (p \<circ> g')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hg_loop hg'_loop hg'_eq] hpe1
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> g) k" by (by100 blast)
            have "g \<in> {k. top1_loop_equiv_on E TE e1 g k}"
              using top1_loop_equiv_on_refl[OF hg_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
                {k. top1_loop_equiv_on E TE e1 g k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>The conjugate \<alpha>\<cdot>g\<cdot>rev(\<alpha>) is in image_hom(E, e0) via h_conj_loop.\<close>
        let ?conj_loop = "top1_path_product (top1_path_product \<alpha> g) (top1_path_reverse \<alpha>)"
        have hconj_in: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          using h_conj_loop top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
        \<comment> \<open>This class = {k | loop_equiv((p\<circ>\<alpha>)\<cdot>(p\<circ>g)\<cdot>rev(p\<circ>\<alpha>), k)}.\<close>
        have hconj_class: "top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}
          = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          then obtain f' where hf': "top1_loop_equiv_on E TE e0 ?conj_loop f'"
              and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have hf'_loop: "top1_is_loop_on E TE e0 f'"
            using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) (p \<circ> f')"
            using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj_loop hf'_loop hf'] hpe0
            by (by100 simp)
          hence "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> f')"
            using hp_conj by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
            by (by100 blast)
        next
          fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
          hence hk: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k"
            by (by100 blast)
          have "p \<circ> ?conj_loop = top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))"
            by (rule hp_conj)
          hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj_loop) k" using hk by (by100 simp)
          moreover have "?conj_loop \<in> {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            using top1_loop_equiv_on_refl[OF h_conj_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        \<comment> \<open>Now compute inv(c) \<cdot> (h_conj \<cdot> c) and show it equals d = [p\<circ>g].\<close>
        let ?h_conj_class = "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) k}"
        have hpg_rev_p\<alpha>_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB
                top1_path_product_is_loop[OF hTB hp\<alpha>_loop hpg_loop] hp\<alpha>_rev_loop])
        \<comment> \<open>h_conj \<cdot> c = [conj_path] \<cdot> [p\<circ>\<alpha>] = [conj_path \<cdot> (p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB ?h_conj_class ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        \<comment> \<open>inv(c) \<cdot> (h_conj \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [above].\<close>
        have hh_c_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))"
          by (rule top1_path_product_is_loop[OF hTB hpg_rev_p\<alpha>_loop hp\<alpha>_loop])
        have hinv_hc: "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
        proof -
          have "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
            by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
          hence "?mulB (?invB ?c) (?mulB ?h_conj_class ?c)
              = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                  {k. top1_loop_equiv_on B TB b0
                    (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)) k}"
            using hh_c by (by100 simp)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hh_c_loop])
          finally show ?thesis .
        qed
        \<comment> \<open>Path algebra: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A)) \<cdot> A) ~ B, where A = p\<circ>\<alpha>, B = p\<circ>g.\<close>
        have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
          using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hpg_path: "top1_is_path_on B TB b0 b0 (p \<circ> g)"
          using hpg_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
          using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>Associativity gives f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h (right-to-left).\<close>
        have hAB_path: "top1_is_path_on B TB b0 b0 (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule top1_path_product_is_path[OF hTB hp\<alpha>_path hpg_path])
        \<comment> \<open>Step 1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) by sym(assoc).\<close>
        note s1_raw = Theorem_51_2_associativity[OF hTB hAB_path hp\<alpha>_rev_path hp\<alpha>_path]
        note s1 = Lemma_51_1_path_homotopic_sym[OF s1_raw]
        \<comment> \<open>s1: ((A\<cdot>B)\<cdot>rev(A))\<cdot>A ~ (A\<cdot>B)\<cdot>(rev(A)\<cdot>A)\<close>
        \<comment> \<open>Step 2: rev(A)\<cdot>A ~ const(b0) by inverse_right.\<close>
        have s2: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (top1_constant_path b0)"
          by (rule Theorem_51_2_invgerse_right[OF hTB hp\<alpha>_path])
        \<comment> \<open>Step 3: (A\<cdot>B)\<cdot>(rev(A)\<cdot>A) ~ (A\<cdot>B)\<cdot>const.\<close>
        have s3: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))"
          by (rule path_homotopic_product_right[OF hTB s2 hAB_path])
        have s4: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_constant_path b0))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Theorem_51_2_right_identity[OF hTB hAB_path])
        have s14: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))
            (top1_path_product (p \<circ> \<alpha>) (p \<circ> g))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s1
                Lemma_51_1_path_homotopic_trans[OF hTB s3 s4]])
        \<comment> \<open>Step 5: rev(A) \<cdot> ((A\<cdot>B\<cdot>rev(A))\<cdot>A) ~ rev(A) \<cdot> (A\<cdot>B).\<close>
        have s5: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)))"
          by (rule path_homotopic_product_right[OF hTB s14 hp\<alpha>_rev_path])
        \<comment> \<open>Step 6: rev(A) \<cdot> (A\<cdot>B) ~ (rev(A)\<cdot>A)\<cdot>B by assoc (direction f\<cdot>(g\<cdot>h) ~ (f\<cdot>g)\<cdot>h).\<close>
        note s6 = Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hp\<alpha>_path hpg_path]
        \<comment> \<open>Step 7: (rev(A)\<cdot>A)\<cdot>B ~ const\<cdot>B by inverse.\<close>
        have s7: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> \<alpha>)) (p \<circ> g))
            (top1_path_product (top1_constant_path b0) (p \<circ> g))"
          by (rule path_homotopic_product_left[OF hTB s2 hpg_path])
        \<comment> \<open>Step 8: const\<cdot>B ~ B by left identity.\<close>
        have s8: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_constant_path b0) (p \<circ> g)) (p \<circ> g)"
          by (rule Theorem_51_2_left_identity[OF hTB hpg_path])
        have s_full: "top1_path_homotopic_on B TB b0 b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
            (p \<circ> g)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTB s5
                Lemma_51_1_path_homotopic_trans[OF hTB s6
                  Lemma_51_1_path_homotopic_trans[OF hTB s7 s8]]])
        \<comment> \<open>So the two loop classes are equal.\<close>
        have hbig_loop: "top1_is_loop_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
          by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hh_c_loop])
        have hclass_eq: "{k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
              (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
          = {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
        proof (rule set_eqI)
          fix k
          have hLR: "top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))
              (p \<circ> g)"
            using s_full hbig_loop hpg_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 (p \<circ> g)
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>)))"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> g) k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_reverse (p \<circ> \<alpha>))
                  (top1_path_product (top1_path_product (top1_path_product (p \<circ> \<alpha>) (p \<circ> g)) (top1_path_reverse (p \<circ> \<alpha>))) (p \<circ> \<alpha>))) k}"
              by (by100 blast)
          qed
        qed
        \<comment> \<open>Conclusion: inv(c) \<cdot> (h_conj \<cdot> c) = d.\<close>
        have "?mulB (?invB ?c) (?mulB ?h_conj_class ?c) = d"
          using hinv_hc hclass_eq hd_class by (by100 simp)
        moreover have "?h_conj_class = top1_fundamental_group_induced_on E TE e0 B TB b0 p
            {k. top1_loop_equiv_on E TE e0 ?conj_loop k}"
          using hconj_class by (by100 simp)
        ultimately have "?mulB (?invB ?c)
            (?mulB (top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 ?conj_loop k}) ?c) = d"
          by (by100 simp)
        thus ?thesis using hconj_in by (by100 blast)
      qed
    next
      \<comment> \<open>\<Leftarrow>: h \<in> image_hom(E, e0). Conjugate: rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is loop at e1.\<close>
      assume "d \<in> (\<lambda>H. ?mulB (?invB ?c) ` ((\<lambda>h. ?mulB h ?c) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      then obtain h where hh: "h \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
          and hd_conj: "d = ?mulB (?invB ?c) (?mulB h ?c)" by (by100 blast)
      \<comment> \<open>h = [p\<circ>f] for loop f at e0.\<close>
      obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
          and hh_eq: "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}"
        using hh unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        by (by100 blast)
      \<comment> \<open>rev(\<alpha>)\<cdot>f\<cdot>\<alpha> is a loop at e1.\<close>
      have hf_path: "top1_is_path_on E TE e0 e0 f"
        using hf_loop unfolding top1_is_loop_on_def by (by100 blast)
      have h_conj2: "top1_is_loop_on E TE e1
          (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
      proof -
        have "top1_is_path_on E TE e1 e0 (top1_path_product (top1_path_reverse \<alpha>) f)"
          by (rule top1_path_product_is_path[OF hTE h\<alpha>_rev hf_path])
        hence "top1_is_path_on E TE e1 e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)"
          by (rule top1_path_product_is_path[OF hTE _ h\<alpha>])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      \<comment> \<open>p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>) = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) = path producing inv(c)\<cdot>h\<cdot>c.\<close>
      have hp_conj2: "p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)
          = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
        by (simp only: comp_path_product comp_path_reverse)
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] = inv(c) \<cdot> h \<cdot> c = d. So d \<in> image_hom(E, e1).\<close>
      \<comment> \<open>[p\<circ>(rev(\<alpha>)\<cdot>f\<cdot>\<alpha>)] \<in> image_hom(E, e1).\<close>
      have hconj2_in: "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
        using h_conj2 top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
      \<comment> \<open>This class = {k | loop_equiv(B, rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>), k)} by hp_conj2.\<close>
      have "top1_fundamental_group_induced_on E TE e1 B TB b0 p
          {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}
        = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) k}"
        then obtain f' where hf': "top1_loop_equiv_on E TE e1
            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>) f'"
            and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop: "top1_is_loop_on E TE e1 f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        \<comment> \<open>p\<circ>conj_loop ~ p\<circ>f' (by induced_preserves_loop_equiv).\<close>
        have "top1_loop_equiv_on B TB b0 (p \<circ> (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>)) (p \<circ> f')"
          using top1_induced_preserves_loop_equiv[OF hTE hp_cont h_conj2 hf'_loop hf'] hpe1
          by (by100 simp)
        \<comment> \<open>p\<circ>conj_loop = rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>) (pointwise by hp_conj2).\<close>
        hence "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) (p \<circ> f')"
          using hp_conj2 by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
          by (by100 blast)
      next
        fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        hence hk: "top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k"
          by (by100 blast)
        \<comment> \<open>The conjugated loop itself is in its own class.\<close>
        let ?conj2 = "top1_path_product (top1_path_product (top1_path_reverse \<alpha>) f) \<alpha>"
        have "?conj2 \<in> {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          using top1_loop_equiv_on_refl[OF h_conj2] by (by100 blast)
        \<comment> \<open>p\<circ>conj2 = the target path (pointwise).\<close>
        have "p \<circ> ?conj2 = top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          by (rule hp_conj2)
        hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k" using hk by simp
        show "k \<in> top1_fundamental_group_induced_on E TE e1 B TB b0 p
            {k. top1_loop_equiv_on E TE e1 ?conj2 k}"
          unfolding top1_fundamental_group_induced_on_def
          using \<open>?conj2 \<in> _\<close> \<open>top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k\<close> by (by100 blast)
      qed
      \<comment> \<open>This class = inv(c) \<cdot> h \<cdot> c = d.\<close>
      moreover have "\<dots> = ?mulB (?invB ?c) (?mulB h ?c)"
      proof -
        \<comment> \<open>Setup: p\<circ>f is a loop at b0.\<close>
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop hpe0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>h = induced([f]) = {k | loop_equiv(p\<circ>f, k)} (from the definition).\<close>
        have hh_class: "h = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "h = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hh_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf'_eq: "top1_loop_equiv_on E TE e0 f f'"
                and hk': "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE hp_cont hf_loop hf'_loop hf'_eq] hpe0
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk']
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            hence hk: "top1_loop_equiv_on B TB b0 (p \<circ> f) k" by (by100 blast)
            have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            thus "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>inv(c) = [rev(p\<circ>\<alpha>)].\<close>
        have hinvc: "?invB ?c = {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}"
          by (rule fundamental_group_invg_class[OF hTB hp\<alpha>_loop])
        \<comment> \<open>h \<cdot> c = [p\<circ>f] \<cdot> [p\<circ>\<alpha>] = [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hh_c: "?mulB h ?c = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hh_class top1_fundamental_group_mul_class[OF hTB hpf_loop hp\<alpha>_loop] by (by100 simp)
        \<comment> \<open>inv(c) \<cdot> (h \<cdot> c) = [rev(p\<circ>\<alpha>)] \<cdot> [(p\<circ>f)\<cdot>(p\<circ>\<alpha>)] = [rev(p\<circ>\<alpha>)\<cdot>(p\<circ>f)\<cdot>(p\<circ>\<alpha>)].\<close>
        have hpf_p\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          using top1_path_product_is_loop[OF hTB hpf_loop hp\<alpha>_loop] .
        have "?mulB (?invB ?c) (?mulB h ?c)
            = ?mulB {k. top1_loop_equiv_on B TB b0 (top1_path_reverse (p \<circ> \<alpha>)) k}
                {k. top1_loop_equiv_on B TB b0 (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)) k}"
          using hinvc hh_c by (by100 simp)
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))) k}"
          by (rule top1_fundamental_group_mul_class[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
        \<comment> \<open>By associativity: rev(p\<circ>\<alpha>) \<cdot> ((p\<circ>f) \<cdot> (p\<circ>\<alpha>)) \<simeq> (rev(p\<circ>\<alpha>) \<cdot> (p\<circ>f)) \<cdot> (p\<circ>\<alpha>).\<close>
        also have "\<dots> = {k. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}"
        proof (rule set_eqI)
          fix k
          have hp\<alpha>_rev_path: "top1_is_path_on B TB b0 b0 (top1_path_reverse (p \<circ> \<alpha>))"
            using hp\<alpha>_rev_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hpf_path: "top1_is_path_on B TB b0 b0 (p \<circ> f)"
            using hpf_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hp\<alpha>_path: "top1_is_path_on B TB b0 b0 (p \<circ> \<alpha>)"
            using hp\<alpha>_loop unfolding top1_is_loop_on_def by (by100 blast)
          have hassoc: "top1_path_homotopic_on B TB b0 b0
              (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>)))
              (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>))"
            by (rule Theorem_51_2_associativity[OF hTB hp\<alpha>_rev_path hpf_path hp\<alpha>_path])
          let ?L = "top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (top1_path_product (p \<circ> f) (p \<circ> \<alpha>))"
          let ?R = "top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)"
          have hL_loop: "top1_is_loop_on B TB b0 ?L"
            by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_p\<alpha>_loop])
          have hR_loop: "top1_is_loop_on B TB b0 ?R"
          proof -
            have "top1_is_loop_on B TB b0 (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f))"
              by (rule top1_path_product_is_loop[OF hTB hp\<alpha>_rev_loop hpf_loop])
            thus ?thesis by (rule top1_path_product_is_loop[OF hTB _ hp\<alpha>_loop])
          qed
          have hLR: "top1_loop_equiv_on B TB b0 ?L ?R"
            using hassoc hL_loop hR_loop unfolding top1_loop_equiv_on_def by (by100 blast)
          have hRL: "top1_loop_equiv_on B TB b0 ?R ?L"
            by (rule top1_loop_equiv_on_sym[OF hLR])
          show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}
            \<longleftrightarrow> k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
          proof
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}"
            from top1_loop_equiv_on_trans[OF hTB hRL this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}" by (by100 blast)
          next
            assume "k \<in> {k. top1_loop_equiv_on B TB b0 ?R k}"
            from top1_loop_equiv_on_trans[OF hTB hLR this[simplified]]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 ?L k}" by (by100 blast)
          qed
        qed
        finally have calc_eq: "?mulB (?invB ?c) (?mulB h ?c)
            = {k. top1_loop_equiv_on B TB b0
                (top1_path_product (top1_path_product (top1_path_reverse (p \<circ> \<alpha>)) (p \<circ> f)) (p \<circ> \<alpha>)) k}" .
        show ?thesis using calc_eq by (by100 simp)
      qed
      moreover note hd_conj
      ultimately show "d \<in> top1_fundamental_group_image_hom E TE e1 B TB b0 p"
        using hconj2_in by (by100 simp)
    qed
  qed
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
      and "e0 \<in> E" and "e0' \<in> E'" and "b0 \<in> B"
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
  \<comment> \<open>Setup: let e1' = h(e0). Since p'∘h = p on E: p'(e1') = p(e0) = b0.\<close>
  let ?e1' = "h e0"
  have hTE: "is_topology_on E TE"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTE': "is_topology_on E' TE'"
    using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on E TE E' TE' h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_bij: "bij_betw h E E'"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  note he0_E = assms(12)
  have he1'_E': "?e1' \<in> E'"
    using he0_E hh_bij unfolding bij_betw_def by (by100 blast)
  have hp'e1': "p' ?e1' = b0"
    using hp he0_E assms(5) by (by100 auto)
  have hb0_B: "b0 \<in> B"
    using hp'e1' top1_covering_map_on_surj[OF assms(6)] he1'_E' by (by100 blast)
  \<comment> \<open>Step 1: Get path γ from e0' to e1' in E' (path-connectedness).\<close>
  have he0'_E': "e0' \<in> E'" by (rule assms(13))
  obtain \<gamma> where h\<gamma>: "top1_is_path_on E' TE' e0' ?e1' \<gamma>"
    using assms(9) he0'_E' he1'_E' unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Step 2: c = [p'∘γ] is a loop class in π₁(B, b0).\<close>
  have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
    by (rule top1_covering_map_on_continuous[OF assms(6)])
  have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<gamma>"
    using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
  have hp'\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<gamma>)"
    by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont hp'_cont])
  have hp'\<gamma>_0: "(p' \<circ> \<gamma>) 0 = b0"
    using h\<gamma> assms(7) unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_1: "(p' \<circ> \<gamma>) 1 = b0"
    using h\<gamma> hp'e1' unfolding top1_is_path_on_def by (by100 simp)
  have hp'\<gamma>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<gamma>)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hp'\<gamma>_cont hp'\<gamma>_0 hp'\<gamma>_1 by (by100 blast)
  let ?c = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<gamma>) g}"
  have hc_carrier: "?c \<in> top1_fundamental_group_carrier B TB b0"
    unfolding top1_fundamental_group_carrier_def using hp'\<gamma>_loop by (by100 blast)
  \<comment> \<open>Step 3: By Theorem 79.2 forward (with e1' as basepoint in E'):
     image_hom(E, e0, p) = image_hom(E', e1', p').\<close>
  have himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
  proof -
    have "(\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1') \<longleftrightarrow>
          top1_fundamental_group_image_hom E TE e0 B TB b0 p
            = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
            he0_E he1'_E' hb0_B])
    moreover have "\<exists>h'. top1_homeomorphism_on E TE E' TE' h' \<and> (\<forall>e\<in>E. p' (h' e) = p e)
               \<and> h' e0 = ?e1'"
      using hh hp by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 4: By basepoint change (Lemma 79.3):
     image_hom(E', e1', p') = c⁻¹ · image_hom(E', e0', p') · c.
     Rearranging: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹
                = c · image_hom(E, e0, p) · c⁻¹.\<close>
  \<comment> \<open>Lemma 79.3: image_hom(E', e0', p') = c · image_hom(E', e1', p') · c⁻¹.
     Proof: for f loop at e0', basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1',
     and p'∘(γ⁻¹*f*γ) = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ) (by comp_basepoint_change).
     In π₁(B): [p'∘(γ⁻¹*f*γ)] = c⁻¹·[p'∘f]·c, so [p'∘f] = c·[p'∘(γ⁻¹*f*γ)]·c⁻¹.\<close>
  have hconjugate: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 ?c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  proof (rule set_eqI, rule iffI)
    fix d
    \<comment> \<open>⊆: d ∈ image_hom(E', e0', p') ⟹ d ∈ c · image_hom(E, e0, p) · c⁻¹.\<close>
    assume "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
    then obtain c0 where hc0: "c0 \<in> top1_fundamental_group_carrier E' TE' e0'"
        and hd_eq: "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    \<comment> \<open>c0 = class(f) for some loop f at e0'.\<close>
    from hc0 obtain f where hf_loop: "top1_is_loop_on E' TE' e0' f"
        and hc0_eq: "c0 = {g. top1_loop_equiv_on E' TE' e0' f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>β = basepoint_change(γ, f) = γ⁻¹*f*γ is a loop at e1'.\<close>
    let ?\<beta> = "top1_basepoint_change_on E' TE' e0' ?e1' \<gamma> f"
    have h\<beta>_loop: "top1_is_loop_on E' TE' ?e1' ?\<beta>"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma> hf_loop])
    \<comment> \<open>p'∘β = basepoint_change(p'∘γ, p'∘f) pointwise (comp_basepoint_change).\<close>
    have hp'\<beta>: "p' \<circ> ?\<beta> = top1_basepoint_change_on B TB b0 b0 (p' \<circ> \<gamma>) (p' \<circ> f)"
      using comp_basepoint_change[of p' E' TE' e0' ?e1' \<gamma> f B TB] assms(7) hp'e1' by (by100 simp)
    \<comment> \<open>[p'∘β] ∈ image_hom(E', e1', p') = image_hom(E, e0, p) (by himg_eq).\<close>
    have h\<beta>_class: "{g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_carrier E' TE' ?e1'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>_loop by (by100 blast)
    have hp'\<beta>_in: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>_class by (by100 blast)
    hence hp'\<beta>_imE: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
        \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      using himg_eq by (by100 simp)
    \<comment> \<open>Key: d = [p'∘f] = c · [p'∘β] · c⁻¹ in the fundamental group.
       This follows from: p'∘β = (p'∘γ)⁻¹*(p'∘f)*(p'∘γ), so
       [p'∘f] = [p'∘γ] · [p'∘β] · [(p'∘γ)⁻¹] = c · [p'∘β] · invg(c).\<close>
    \<comment> \<open>p'∘f is a loop at b0.\<close>
    have hp'f_loop: "top1_is_loop_on B TB b0 (p' \<circ> f)"
    proof -
      have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' f"
        using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> f)"
        by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
      moreover have "(p' \<circ> f) 0 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      moreover have "(p' \<circ> f) 1 = b0" using hf_loop assms(7)
        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>Key computation: class(basepoint_change(p'∘γ, p'∘f)) = invg(c) · class(p'∘f) · c.
       Uses: basepoint_change = reverse(α)*g*α, then mul_class twice + invg_class.\<close>
    let ?\<alpha> = "p' \<circ> \<gamma>" and ?g' = "p' \<circ> f"
    have h\<alpha>_loop: "top1_is_loop_on B TB b0 ?\<alpha>" by (rule hp'\<gamma>_loop)
    have hg'_loop: "top1_is_loop_on B TB b0 ?g'" by (rule hp'f_loop)
    have hr\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>)"
      using h\<alpha>_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
    have hg'\<alpha>_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g' ?\<alpha>)"
      by (rule top1_path_product_is_loop[OF hTB hg'_loop h\<alpha>_loop])
    \<comment> \<open>class(reverse(α) * (g * α)) = mul(invg(class(α)), mul(class(g), class(α)))\<close>
    have hbc_class: "{h. top1_loop_equiv_on B TB b0
          (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
        = top1_fundamental_group_mul B TB b0
            (top1_fundamental_group_invg B TB b0 ?c)
            (top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g' h} ?c)"
    proof -
      have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}
            {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}
          = {h. top1_loop_equiv_on B TB b0
              (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hr\<alpha>_loop hg'\<alpha>_loop])
      moreover have "top1_fundamental_group_mul B TB b0
            {h. top1_loop_equiv_on B TB b0 ?g' h} ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g' ?\<alpha>) h}"
        by (rule top1_fundamental_group_mul_class[OF hTB hg'_loop h\<alpha>_loop])
      moreover have "top1_fundamental_group_invg B TB b0 ?c
          = {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>) h}"
        by (rule fundamental_group_invg_class[OF hTB h\<alpha>_loop])
      moreover have "{h. top1_loop_equiv_on B TB b0
            (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}
          = {h. top1_loop_equiv_on B TB b0
            (top1_path_product (top1_path_reverse ?\<alpha>) (top1_path_product ?g' ?\<alpha>)) h}"
        unfolding top1_basepoint_change_on_def by (by100 simp)
      ultimately show ?thesis by (by100 metis)
    qed
    \<comment> \<open>Now: induced_p'(class(β)) = class(p'∘β) = class(basepoint_change(p'∘γ, p'∘f)).\<close>
    have hind_eq: "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}
      = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
    proof (rule set_eqI, rule iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
      then obtain f' where hf'_eq: "top1_loop_equiv_on E' TE' ?e1' ?\<beta> f'"
          and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hf'_loop: "top1_is_loop_on E' TE' ?e1' f'"
        using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> ?\<beta>) (p' \<circ> f')"
        by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>_loop hf'_loop hf'_eq])
      hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) (p' \<circ> f')"
        using hp'e1' by (by100 simp)
      from top1_loop_equiv_on_trans[OF hTB this hk]
      show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (by100 blast)
    next
      fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}"
      moreover have "?\<beta> \<in> {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        using top1_loop_equiv_on_refl[OF h\<beta>_loop] by (by100 blast)
      ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    qed
    \<comment> \<open>d = induced_p'(class(f)) = class(p'∘f).\<close>
    have hd_class: "d = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
    proof -
      have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0" by (rule hd_eq)
      also have "\<dots> = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' f g}" by (simp only: hc0_eq)
      also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' f f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have hf'_loop2: "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> f) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont hf_loop hf'_loop2 hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> f) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> f) h}"
        moreover have "f \<in> {g. top1_loop_equiv_on E' TE' e0' f g}"
          using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' f g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>Assembly: d = class(p'∘f). class(p'∘β) = invg(c) · d · c (from hbc_class + hp'β).
       Group algebra: d = c · class(p'∘β) · invg(c).\<close>
    \<comment> \<open>Chain: z = class(p'∘β) = class(bc(α,g')) = invg(c)·d·c. Then d = c·z·invg(c) by group algebra.\<close>
    let ?z = "top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' ?e1' ?\<beta> g}"
    have hz_eq1: "?z = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>) h}" by (rule hind_eq)
    have hz_eq2: "?z = {h. top1_loop_equiv_on B TB b0
        (top1_basepoint_change_on B TB b0 b0 ?\<alpha> ?g') h}"
      using hz_eq1 hp'\<beta> by (by100 simp)
    have hz_eq3: "?z = top1_fundamental_group_mul B TB b0
        (top1_fundamental_group_invg B TB b0 ?c)
        (top1_fundamental_group_mul B TB b0 d ?c)"
      using hz_eq2 hbc_class hd_class by (by100 simp)
    \<comment> \<open>Group algebra: z = invg(c) · d · c ⟹ d = c · z · invg(c).\<close>
    have hgrp: "top1_is_group_on
        (top1_fundamental_group_carrier B TB b0)
        (top1_fundamental_group_mul B TB b0)
        (top1_fundamental_group_id B TB b0)
        (top1_fundamental_group_invg B TB b0)"
      by (rule top1_fundamental_group_is_group[OF hTB hb0_B])
    let ?mulB = "top1_fundamental_group_mul B TB b0"
    let ?invB = "top1_fundamental_group_invg B TB b0"
    let ?eB = "top1_fundamental_group_id B TB b0"
    let ?G = "top1_fundamental_group_carrier B TB b0"
    have hc_in: "?c \<in> ?G" by (rule hc_carrier)
    have hd_in: "d \<in> ?G"
    proof -
      have "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
        using \<open>d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'\<close> .
      then obtain c0' where "c0' \<in> top1_fundamental_group_carrier E' TE' e0'"
          "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p' c0'"
        unfolding top1_fundamental_group_image_hom_def by (by100 blast)
      thus ?thesis
        using top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he0'_E' hb0_B hp'_cont assms(7)]
        unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have hz_in: "?z \<in> ?G"
    proof -
      have hhom': "top1_group_hom_on
          (top1_fundamental_group_carrier E' TE' ?e1')
          (top1_fundamental_group_mul E' TE' ?e1') ?G ?mulB
          (top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p')"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTE' hTB he1'_E' hb0_B hp'_cont hp'e1'])
      have "?z \<in> ?G"
        using hhom' h\<beta>_class unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis .
    qed
    have hinvc_in: "?invB ?c \<in> ?G" by (rule group_inv_closed[OF hgrp hc_in])
    \<comment> \<open>c · z · c⁻¹ = c · (invg(c) · d · c) · c⁻¹ = d\<close>
    \<comment> \<open>Expand z, apply associativity + cancellation step by step.\<close>
    have hdc_in: "?mulB d ?c \<in> ?G" by (rule group_mul_closed[OF hgrp hd_in hc_in])
    have hinvdc_in: "?mulB (?invB ?c) (?mulB d ?c) \<in> ?G"
      by (rule group_mul_closed[OF hgrp hinvc_in hdc_in])
    \<comment> \<open>Step A: c · (c⁻¹ · (d · c)) · c⁻¹ → (c · c⁻¹) · (d · c) · c⁻¹ (assoc on outer)\<close>
    have hstepA: "?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))
        = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using group_assoc[OF hgrp hc_in hinvdc_in hinvc_in] by (by100 metis)
    \<comment> \<open>Step B: c · (c⁻¹ · (d · c)) → (c · c⁻¹) · (d · c) (inner assoc)\<close>
    have hstepB: "?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))
        = ?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)"
      using group_assoc[OF hgrp hc_in hinvc_in hdc_in] by (by100 metis)
    \<comment> \<open>Step C: c · c⁻¹ = e\<close>
    have hstepC: "?mulB ?c (?invB ?c) = ?eB" by (rule group_inv_right[OF hgrp hc_in])
    \<comment> \<open>Step D: e · (d · c) = d · c\<close>
    have hstepD: "?mulB ?eB (?mulB d ?c) = ?mulB d ?c"
      by (rule group_id_left[OF hgrp hdc_in])
    \<comment> \<open>Step E: (d · c) · c⁻¹ = d · (c · c⁻¹) (assoc)\<close>
    have hstepE: "?mulB (?mulB d ?c) (?invB ?c) = ?mulB d (?mulB ?c (?invB ?c))"
      by (rule group_assoc[OF hgrp hd_in hc_in hinvc_in])
    \<comment> \<open>Step F: d · e = d\<close>
    have hstepF: "?mulB d ?eB = d" by (rule group_id_right[OF hgrp hd_in])
    \<comment> \<open>Chain: c·z·c⁻¹ = c·(c⁻¹·d·c)·c⁻¹ [hz_eq3] = ... = d\<close>
    have "?mulB ?c (?mulB ?z (?invB ?c))
        = ?mulB ?c (?mulB (?mulB (?invB ?c) (?mulB d ?c)) (?invB ?c))"
      using hz_eq3 by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?c (?mulB (?invB ?c) (?mulB d ?c))) (?invB ?c)"
      using hstepA by (by100 simp)
    also have "\<dots> = ?mulB (?mulB (?mulB ?c (?invB ?c)) (?mulB d ?c)) (?invB ?c)"
      using hstepB by (by100 simp)
    also have "\<dots> = ?mulB (?mulB ?eB (?mulB d ?c)) (?invB ?c)"
      using hstepC by (by100 simp)
    also have "\<dots> = ?mulB (?mulB d ?c) (?invB ?c)"
      using hstepD by (by100 simp)
    also have "\<dots> = ?mulB d (?mulB ?c (?invB ?c))"
      using hstepE by (by100 simp)
    also have "\<dots> = ?mulB d ?eB"
      using hstepC by (by100 simp)
    also have "\<dots> = d" using hstepF by (by100 simp)
    finally have hd_conj: "d = ?mulB ?c (?mulB ?z (?invB ?c))" by (by100 metis)
    show "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
      using hd_conj hp'\<beta>_imE by (by100 blast)
  next
    fix d
    \<comment> \<open>⊇: d ∈ c · image_hom(E, e0, p) · c⁻¹ ⟹ d ∈ image_hom(E', e0', p').\<close>
    assume "d \<in> (\<lambda>H. (top1_fundamental_group_mul B TB b0 ?c)
        ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                  (top1_fundamental_group_invg B TB b0 ?c)) ` H))
        (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    then obtain x where hx_in: "x \<in> top1_fundamental_group_image_hom E TE e0 B TB b0 p"
        and hd_eq: "d = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
      by (by100 blast)
    \<comment> \<open>x ∈ image_hom(E, e0, p) = image_hom(E', e1', p') (by himg_eq).\<close>
    have hx_imE'1: "x \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
      using hx_in himg_eq by (by100 simp)
    \<comment> \<open>x = induced_p'(class(β)) for some loop β at e1'.
       γ*β*γ⁻¹ is a loop at e0', and d = c · x · c⁻¹ = [p'∘(γ*β*γ⁻¹)] ∈ image_hom(E', e0', p').\<close>
    \<comment> \<open>x ∈ image_hom(E', e1', p') means x = induced_p'(class(β')) for some loop β' at e1'.\<close>
    from hx_imE'1 obtain c1' where hc1': "c1' \<in> top1_fundamental_group_carrier E' TE' ?e1'"
        and hx_eq: "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'"
      unfolding top1_fundamental_group_image_hom_def by (by100 blast)
    from hc1' obtain \<beta>' where h\<beta>'_loop: "top1_is_loop_on E' TE' ?e1' \<beta>'"
        and hc1'_eq: "c1' = {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>γ * β' * γ⁻¹ is a loop at e0' (reverse basepoint change).\<close>
    let ?\<gamma>R = "top1_path_reverse \<gamma>"
    let ?\<beta>0 = "top1_basepoint_change_on E' TE' ?e1' e0' ?\<gamma>R \<beta>'"
    have h\<gamma>R: "top1_is_path_on E' TE' ?e1' e0' ?\<gamma>R"
      by (rule top1_path_reverse_is_path[OF h\<gamma>])
    have h\<beta>0_loop: "top1_is_loop_on E' TE' e0' ?\<beta>0"
      by (rule top1_basepoint_change_is_loop[OF hTE' h\<gamma>R h\<beta>'_loop])
    \<comment> \<open>class(p'∘β0) ∈ image_hom(E', e0', p').\<close>
    have h\<beta>0_class: "{g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_carrier E' TE' e0'"
      unfolding top1_fundamental_group_carrier_def using h\<beta>0_loop by (by100 blast)
    have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      unfolding top1_fundamental_group_image_hom_def using h\<beta>0_class by (by100 blast)
    \<comment> \<open>d = class(p'∘β0) by symmetric group algebra argument.
       p'∘β0 = bc(p'∘γ⁻¹, p'∘β') = (p'∘γ) * (p'∘β') * (p'∘γ)⁻¹ = c · x · c⁻¹ = d.\<close>
    moreover have "d = top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
        {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
    proof -
      \<comment> \<open>Step 1: induced_p'(class(β0)) = class(p'∘β0) — same as hind_eq but at e0'.\<close>
      have hind2: "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
      proof (rule set_eqI, rule iffI)
        fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
        then obtain f' where hf': "top1_loop_equiv_on E' TE' e0' ?\<beta>0 f'"
            and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f') k"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        have "top1_is_loop_on E' TE' e0' f'"
          using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_loop_equiv_on B TB (p' e0') (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>0_loop \<open>top1_is_loop_on E' TE' e0' f'\<close> hf'])
        hence "top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) (p' \<circ> f')"
          using assms(7) by (by100 simp)
        from top1_loop_equiv_on_trans[OF hTB this hk]
        show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}" by (by100 blast)
      next
        fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}"
        moreover have "?\<beta>0 \<in> {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          using top1_loop_equiv_on_refl[OF h\<beta>0_loop] by (by100 blast)
        ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}"
          unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      qed
      \<comment> \<open>Step 2: p'∘β0 = bc(p'∘γR, p'∘β') = bc(reverse(p'∘γ), p'∘β').\<close>
      have hp'\<beta>0: "p' \<circ> ?\<beta>0 = top1_basepoint_change_on B TB (p' ?e1') (p' e0') (p' \<circ> ?\<gamma>R) (p' \<circ> \<beta>')"
        using comp_basepoint_change[of p' E' TE' ?e1' e0' ?\<gamma>R \<beta>' B TB] by (by100 simp)
      have hp'\<gamma>R: "p' \<circ> ?\<gamma>R = top1_path_reverse (p' \<circ> \<gamma>)"
        by (rule comp_path_reverse)
      \<comment> \<open>bc(reverse(α), f) = reverse(reverse(α)) * f * reverse(α) = α * f * reverse(α).\<close>
      have hbc_expand: "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
          = top1_path_product (p' \<circ> \<gamma>) (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
      proof -
        have "top1_basepoint_change_on B TB b0 b0 (top1_path_reverse (p' \<circ> \<gamma>)) (p' \<circ> \<beta>')
            = top1_path_product (top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)))
                (top1_path_product (p' \<circ> \<beta>') (top1_path_reverse (p' \<circ> \<gamma>)))"
          unfolding top1_basepoint_change_on_def by (by100 simp)
        also have "top1_path_reverse (top1_path_reverse (p' \<circ> \<gamma>)) = p' \<circ> \<gamma>"
          by (rule path_reverse_involution)
        finally show ?thesis .
      qed
      \<comment> \<open>Step 3: class(α * f * reverse(α)) = mul(class(α), mul(class(f), invg(class(α)))).\<close>
      let ?\<alpha>B = "p' \<circ> \<gamma>" and ?g'B = "p' \<circ> \<beta>'"
      have h\<alpha>B_loop: "top1_is_loop_on B TB b0 ?\<alpha>B" by (rule hp'\<gamma>_loop)
      have hg'B_loop: "top1_is_loop_on B TB b0 ?g'B"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology E' TE' \<beta>'"
          using h\<beta>'_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (p' \<circ> \<beta>')"
          by (rule top1_continuous_map_on_comp[OF _ hp'_cont])
        moreover have "(p' \<circ> \<beta>') 0 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        moreover have "(p' \<circ> \<beta>') 1 = b0" using h\<beta>'_loop hp'e1'
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
        ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      qed
      have hr\<alpha>B_loop: "top1_is_loop_on B TB b0 (top1_path_reverse ?\<alpha>B)"
        using h\<alpha>B_loop unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
      have hg'\<alpha>R_loop: "top1_is_loop_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))"
        by (rule top1_path_product_is_loop[OF hTB hg'B_loop hr\<alpha>B_loop])
      have hclass_eq: "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
          = top1_fundamental_group_mul B TB b0 ?c
              (top1_fundamental_group_mul B TB b0
                {h. top1_loop_equiv_on B TB b0 ?g'B h}
                (top1_fundamental_group_invg B TB b0 ?c))"
      proof -
        have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?\<alpha>B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          by (rule top1_fundamental_group_mul_class[OF hTB h\<alpha>B_loop hg'\<alpha>R_loop])
        moreover have "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              {h. top1_loop_equiv_on B TB b0 (top1_path_reverse ?\<alpha>B) h}"
          using fundamental_group_invg_class[OF hTB h\<alpha>B_loop] by (by100 simp)
        hence "top1_fundamental_group_mul B TB b0
              {h. top1_loop_equiv_on B TB b0 ?g'B h}
              (top1_fundamental_group_invg B TB b0 ?c)
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B)) h}"
          using top1_fundamental_group_mul_class[OF hTB hg'B_loop hr\<alpha>B_loop] by (by100 simp)
        moreover have "{h. top1_loop_equiv_on B TB b0 (p' \<circ> ?\<beta>0) h}
            = {h. top1_loop_equiv_on B TB b0 (top1_path_product ?\<alpha>B (top1_path_product ?g'B (top1_path_reverse ?\<alpha>B))) h}"
          using hp'\<beta>0 hp'\<gamma>R hbc_expand hp'e1' assms(7) by (by100 simp)
        ultimately show ?thesis by (by100 metis)
      qed
      \<comment> \<open>Step 4: x = class(p'∘β'), so class(p'∘β0) = mul(c, mul(x, invg(c))).\<close>
      have hx_class: "x = {h. top1_loop_equiv_on B TB b0 ?g'B h}"
      proof -
        have "x = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p' c1'" by (rule hx_eq)
        also have "\<dots> = top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
            {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}" by (simp only: hc1'_eq)
        also have "\<dots> = {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
          then obtain f'' where hf'': "top1_loop_equiv_on E' TE' ?e1' \<beta>' f''"
              and hk: "top1_loop_equiv_on B TB b0 (p' \<circ> f'') k"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          have "top1_is_loop_on E' TE' ?e1' f''"
            using hf'' unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on B TB (p' ?e1') (p' \<circ> \<beta>') (p' \<circ> f'')"
            by (rule top1_induced_preserves_loop_equiv[OF hTE' hp'_cont h\<beta>'_loop \<open>top1_is_loop_on E' TE' ?e1' f''\<close> hf''])
          hence "top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') (p' \<circ> f'')"
            using hp'e1' by (by100 simp)
          from top1_loop_equiv_on_trans[OF hTB this hk]
          show "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}" by (by100 blast)
        next
          fix k assume "k \<in> {h. top1_loop_equiv_on B TB b0 (p' \<circ> \<beta>') h}"
          moreover have "\<beta>' \<in> {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            using top1_loop_equiv_on_refl[OF h\<beta>'_loop] by (by100 blast)
          ultimately show "k \<in> top1_fundamental_group_induced_on E' TE' ?e1' B TB b0 p'
              {g. top1_loop_equiv_on E' TE' ?e1' \<beta>' g}"
            unfolding top1_fundamental_group_induced_on_def by (by100 blast)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>Step 5: Assembly.\<close>
      have "top1_fundamental_group_induced_on E' TE' e0' B TB b0 p'
          {g. top1_loop_equiv_on E' TE' e0' ?\<beta>0 g}
        = top1_fundamental_group_mul B TB b0 ?c
            (top1_fundamental_group_mul B TB b0 x (top1_fundamental_group_invg B TB b0 ?c))"
        using hind2 hclass_eq hx_class by (by100 simp)
      thus ?thesis using hd_eq by (by100 simp)
    qed
    ultimately show "d \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
      by (by100 simp)
  qed
  show "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    using hc_carrier hconjugate by (by100 blast)
next
  \<comment> \<open>Backward: conjugacy means subgroups differ by a basepoint change in E'.
     Theorem 79.2 applies after adjusting basepoints.\<close>
  assume "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Conjugate subgroups \<Rightarrow> \<exists>e1' with p'(e1')=b0 s.t. subgroups equal after basepoint change.
     Then Theorem 79.2 gives the pointed equivalence, and we forget the basepoint.\<close>
  then obtain c where hc: "c \<in> top1_fundamental_group_carrier B TB b0"
      and hconj: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
        = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                      (top1_fundamental_group_invg B TB b0 c)) ` H))
            (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
    by blast
  \<comment> \<open>c = [\<gamma>] for some loop \<gamma> at b0. Lift \<gamma>\<inverse> to E' from e0'. The endpoint is e1'.
     Then p'_*(\<pi>_1(E', e1')) = c\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> c = p_*(\<pi>_1(E, e0)).\<close>
  \<comment> \<open>From the basepoint change: after conjugation by c\<inverse>,
     p'_*(E', e1') = p_*(E, e0). Apply Theorem 79.2 with basepoint e1'.\<close>
  have "\<exists>e1'. e1' \<in> E' \<and> p' e1' = b0 \<and>
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
  proof -
    have hTE': "is_topology_on E' TE'"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hp'_cont: "top1_continuous_map_on E' TE' B TB p'"
      by (rule top1_covering_map_on_continuous[OF assms(6)])
    \<comment> \<open>c has a representative loop \<gamma> at b0.\<close>
    obtain \<gamma> where h\<gamma>_loop: "top1_is_loop_on B TB b0 \<gamma>"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>Lift \<gamma> to E' from e0'. Endpoint = e1'.\<close>
    have h\<gamma>_path: "top1_is_path_on B TB b0 b0 \<gamma>" using h\<gamma>_loop unfolding top1_is_loop_on_def by (by100 blast)
    obtain \<delta> where h\<delta>: "top1_is_path_on E' TE' e0' (\<delta> 1) \<delta>"
        and h\<delta>p: "\<forall>s\<in>I_set. p' (\<delta> s) = \<gamma> s"
    proof -
      have "\<exists>ft. top1_is_path_on E' TE' e0' (ft 1) ft \<and> (\<forall>s\<in>I_set. p' (ft s) = \<gamma> s)"
      proof (rule Lemma_54_1_path_lifting)
        show "top1_covering_map_on E' TE' B TB p'" by (rule assms(6))
        show "e0' \<in> E'" by (rule assms(13))
        show "p' e0' = b0" by (rule assms(7))
        show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
        show "is_topology_on B TB" by (rule hTB)
        show "is_topology_on E' TE'" by (rule hTE')
      qed
      then obtain ft' where hft': "top1_is_path_on E' TE' e0' (ft' 1) ft'"
          and hft'p: "\<forall>s\<in>I_set. p' (ft' s) = \<gamma> s" by (by100 blast)
      show ?thesis using that[OF hft' hft'p] .
    qed
    let ?e1' = "\<delta> 1"
    have he1': "?e1' \<in> E'"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      thus ?thesis using h\<delta> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    qed
    have hp'e1': "p' ?e1' = b0"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      hence "p' (\<delta> 1) = \<gamma> 1" using h\<delta>p by (by100 blast)
      moreover have "\<gamma> 1 = b0" using h\<gamma>_path unfolding top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Basepoint change: p'_*(\<pi>_1(E', e1')) = [p'\<circ>\<delta>]\<inverse> \<cdot> p'_*(\<pi>_1(E', e0')) \<cdot> [p'\<circ>\<delta>].
       Since p'\<circ>\<delta> = \<gamma> and [\<gamma>] = c: p'_*(E', e1') = c\<inverse> \<cdot> p'_*(E', e0') \<cdot> c.
       Using hconj: p'_*(E', e0') = c \<cdot> p_*(E) \<cdot> c\<inverse>.
       So: p'_*(E', e1') = c\<inverse> \<cdot> (c \<cdot> p_*(E) \<cdot> c\<inverse>) \<cdot> c = p_*(E).\<close>
    \<comment> \<open>Apply basepoint change: image_hom(E', e1') = c'\<inverse> \<cdot> image_hom(E', e0') \<cdot> c'
       where c' = [p'\<circ>\<delta>] = [\<gamma>] = c.\<close>
    \<comment> \<open>Basepoint change + conjugacy cancellation:
       image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c (basepoint change by \<delta>)
       image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c) (hconj)
       Combined: image_hom(E', e1') = inv(c) \<cdot> c \<cdot> image_hom(E, e0) \<cdot> inv(c) \<cdot> c = image_hom(E, e0)
       Proof uses: basepoint_change_image_hom + group algebra cancellation.\<close>
    \<comment> \<open>Step: [p'\<circ>\<delta>] = c. Since p'\<circ>\<delta> = \<gamma> on I_set, their loop classes agree.\<close>
    have hp'\<delta>_eq_\<gamma>: "\<And>s. s \<in> I_set \<Longrightarrow> (p' \<circ> \<delta>) s = \<gamma> s" using h\<delta>p by (by100 simp)
    have hp'\<delta>_loop: "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)"
    proof -
      have "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
        by (rule top1_continuous_map_on_comp)
           (use h\<delta> hp'_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      moreover have "(p' \<circ> \<delta>) 0 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      moreover have "(p' \<circ> \<delta>) 1 = b0"
        using hp'\<delta>_eq_\<gamma> h\<gamma>_path unfolding top1_is_path_on_def top1_unit_interval_def by (by100 auto)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    have hclass_p'\<delta>_eq_c: "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
        = {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
    proof (rule set_eqI)
      fix k
      \<comment> \<open>p'\<circ>\<delta> and \<gamma> agree on I_set, so they are path-homotopic via the identity homotopy.\<close>
      have hp'\<delta>_\<gamma>_equiv: "top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) \<gamma>"
        unfolding top1_loop_equiv_on_def
      proof (intro conjI)
        show "top1_is_loop_on B TB b0 (p' \<circ> \<delta>)" by (rule hp'\<delta>_loop)
        show "top1_is_loop_on B TB b0 \<gamma>" by (rule h\<gamma>_loop)
        \<comment> \<open>Path homotopy via constant homotopy F(s,t) = (p'\<circ>\<delta>)(s).\<close>
        show "top1_path_homotopic_on B TB b0 b0 (p' \<circ> \<delta>) \<gamma>"
          unfolding top1_path_homotopic_on_def
        proof (intro conjI)
          show "top1_is_path_on B TB b0 b0 (p' \<circ> \<delta>)"
            using hp'\<delta>_loop unfolding top1_is_loop_on_def by (by100 blast)
          show "top1_is_path_on B TB b0 b0 \<gamma>" by (rule h\<gamma>_path)
          show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F
              \<and> (\<forall>s\<in>I_set. F (s, 0) = (p' \<circ> \<delta>) s) \<and> (\<forall>s\<in>I_set. F (s, 1) = \<gamma> s)
              \<and> (\<forall>t\<in>I_set. F (0, t) = b0) \<and> (\<forall>t\<in>I_set. F (1, t) = b0)"
          proof (rule exI[of _ "\<lambda>p. (p' \<circ> \<delta>) (fst p)"], intro conjI)
            have h_p'\<delta>_cont: "top1_continuous_map_on I_set I_top B TB (p' \<circ> \<delta>)"
              using hp'\<delta>_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            show "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB (\<lambda>p. (p' \<circ> \<delta>) (fst p))"
              by (rule path_homotopy_const_continuous[OF h_p'\<delta>_cont])
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (0::real))) = (p' \<circ> \<delta>) s" by (by100 simp)
            show "\<forall>s\<in>I_set. (p' \<circ> \<delta>) (fst (s, (1::real))) = \<gamma> s"
              using hp'\<delta>_eq_\<gamma> by (by100 simp)
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((0::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              have "(p' \<circ> \<delta>) 0 = b0"
                using h\<delta> assms(7) unfolding top1_is_path_on_def by (by100 simp)
              thus "(p' \<circ> \<delta>) (fst ((0::real), t)) = b0" by (by100 simp)
            qed
            show "\<forall>t\<in>I_set. (p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
            proof
              fix t assume "t \<in> I_set"
              show "(p' \<circ> \<delta>) (fst ((1::real), t)) = b0"
                using hp'e1' by (by100 simp)
            qed
          qed
        qed
      qed
      have h\<gamma>_p'\<delta>_equiv: "top1_loop_equiv_on B TB b0 \<gamma> (p' \<circ> \<delta>)"
        by (rule top1_loop_equiv_on_sym[OF hp'\<delta>_\<gamma>_equiv])
      show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}
          \<longleftrightarrow> k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
      proof
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
        from top1_loop_equiv_on_trans[OF hTB h\<gamma>_p'\<delta>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}" by (by100 blast)
      next
        assume "k \<in> {g. top1_loop_equiv_on B TB b0 \<gamma> g}"
        from top1_loop_equiv_on_trans[OF hTB hp'\<delta>_\<gamma>_equiv this[simplified]]
        show "k \<in> {g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}" by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply basepoint_change_image_hom: image_hom(E', e1') = inv([p'\<circ>\<delta>]) \<cdot> image_hom(E', e0') \<cdot> [p'\<circ>\<delta>].\<close>
    let ?c' = "{g. top1_loop_equiv_on B TB b0 (p' \<circ> \<delta>) g}"
    have hbpc: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 ?c')
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h ?c') ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      by (rule basepoint_change_image_hom[OF assms(6) hTE' hTB assms(13) he1' h\<delta> assms(7) hp'e1' assms(9)])
    \<comment> \<open>Replace ?c' with c using hclass_p'\<delta>_eq_c and hc_eq.\<close>
    have hc'_eq_c: "?c' = c" using hclass_p'\<delta>_eq_c hc_eq by (by100 simp)
    \<comment> \<open>So image_hom(E', e1') = inv(c) \<cdot> image_hom(E', e0') \<cdot> c.\<close>
    have hbpc2: "top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'
        = (\<lambda>H. top1_fundamental_group_mul B TB b0
              (top1_fundamental_group_invg B TB b0 c)
            ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h c) ` H))
            (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')"
      using hbpc hc'_eq_c by (by100 simp)
    \<comment> \<open>Substitute hconj: image_hom(E', e0') = c \<cdot> image_hom(E, e0) \<cdot> inv(c).\<close>
    \<comment> \<open>After substitution: image_hom(E', e1') = inv(c) \<cdot> (c \<cdot> image_hom(E, e0) \<cdot> inv(c)) \<cdot> c.\<close>
    \<comment> \<open>This double conjugation cancels: = image_hom(E, e0).\<close>
    have himg_match: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
        = top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
    proof -
      let ?mulB = "top1_fundamental_group_mul B TB b0"
      let ?invB = "top1_fundamental_group_invg B TB b0"
      let ?eB = "top1_fundamental_group_id B TB b0"
      let ?G = "top1_fundamental_group_carrier B TB b0"
      let ?img = "top1_fundamental_group_image_hom E TE e0 B TB b0 p"
      \<comment> \<open>Group axioms from the fundamental group of (B, b0).\<close>
      have hb0B: "b0 \<in> B" using assms(14) .
      have hgrp: "top1_is_group_on ?G ?mulB ?eB ?invB"
        by (rule top1_fundamental_group_is_group[OF hTB hb0B])
      have hc_G: "c \<in> ?G" by (rule hc)
      note hgrp_raw = hgrp[unfolded top1_is_group_on_def]
      note hmul_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct1]
      note hinv_cl_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hassoc_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hid_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note hinv_raw = hgrp_raw[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      have hmul_cl: "\<And>x y. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> ?mulB x y \<in> ?G"
        using hmul_cl_raw by (by100 blast)
      have hinv_cl: "\<And>x. x \<in> ?G \<Longrightarrow> ?invB x \<in> ?G"
        using hinv_cl_raw by (by100 blast)
      have hinvc_G: "?invB c \<in> ?G" by (rule hinv_cl[OF hc_G])
      have hassoc: "\<And>x y z. x \<in> ?G \<Longrightarrow> y \<in> ?G \<Longrightarrow> z \<in> ?G \<Longrightarrow>
          ?mulB (?mulB x y) z = ?mulB x (?mulB y z)"
        using hassoc_raw by (by100 blast)
      have hlinv: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB (?invB x) x = ?eB"
        using hinv_raw by (by100 blast)
      have hrid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB x ?eB = x"
        using hid_raw by (by100 blast)
      have hlid: "\<And>x. x \<in> ?G \<Longrightarrow> ?mulB ?eB x = x"
        using hid_raw by (by100 blast)
      \<comment> \<open>Image hom elements are in the carrier.\<close>
      have himg_sub: "?img \<subseteq> ?G"
      proof
        fix d assume "d \<in> ?img"
        then obtain f where hf_loop: "top1_is_loop_on E TE e0 f"
            and hd_eq: "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
          unfolding top1_fundamental_group_image_hom_def top1_fundamental_group_carrier_def
          by (by100 blast)
        have hTE_loc: "is_topology_on E TE"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hp_cont: "top1_continuous_map_on E TE B TB p"
          by (rule top1_covering_map_on_continuous[OF assms(4)])
        have hpf_loop: "top1_is_loop_on B TB b0 (p \<circ> f)"
        proof -
          have "top1_continuous_map_on I_set I_top B TB (p \<circ> f)"
            by (rule top1_continuous_map_on_comp)
               (use hf_loop hp_cont in \<open>unfold top1_is_loop_on_def top1_is_path_on_def, by100 blast\<close>)+
          moreover have "(p \<circ> f) 0 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          moreover have "(p \<circ> f) 1 = b0" using hf_loop assms(5) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>induced([f]) = [p\<circ>f] (same as hh_class proof pattern).\<close>
        have hd_class: "d = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
        proof -
          have "d = top1_fundamental_group_induced_on E TE e0 B TB b0 p
              {k. top1_loop_equiv_on E TE e0 f k}" by (rule hd_eq)
          also have "\<dots> = {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
            then obtain f' where hf': "top1_loop_equiv_on E TE e0 f f'"
                and hk: "top1_loop_equiv_on B TB b0 (p \<circ> f') k"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
            have hf'_loop: "top1_is_loop_on E TE e0 f'"
              using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB b0 (p \<circ> f) (p \<circ> f')"
              using top1_induced_preserves_loop_equiv[OF hTE_loc hp_cont hf_loop hf'_loop hf'] assms(5)
              by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}" by (by100 blast)
          next
            fix k assume "k \<in> {k. top1_loop_equiv_on B TB b0 (p \<circ> f) k}"
            moreover have "f \<in> {k. top1_loop_equiv_on E TE e0 f k}"
              using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
            ultimately show "k \<in> top1_fundamental_group_induced_on E TE e0 B TB b0 p
                {k. top1_loop_equiv_on E TE e0 f k}"
              unfolding top1_fundamental_group_induced_on_def by (by100 blast)
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>[p\<circ>f] \<in> carrier(B, b0) since p\<circ>f is a loop at b0.\<close>
        show "d \<in> ?G"
          unfolding hd_class top1_fundamental_group_carrier_def
          using hpf_loop top1_loop_equiv_on_refl[OF hpf_loop] by (by100 blast)
      qed
      \<comment> \<open>Key: inv(c) \<cdot> ((c \<cdot> (h \<cdot> inv(c))) \<cdot> c) = h for h \<in> G.\<close>
      have hcancel: "\<And>h. h \<in> ?G \<Longrightarrow>
          ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
      proof -
        fix h assume hh: "h \<in> ?G"
        have hhinvc: "?mulB h (?invB c) \<in> ?G" by (rule hmul_cl[OF hh hinvc_G])
        have hchinvc: "?mulB c (?mulB h (?invB c)) \<in> ?G" by (rule hmul_cl[OF hc_G hhinvc])
        \<comment> \<open>Step 1: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> ((h \<cdot> inv(c)) \<cdot> c) by assoc.\<close>
        have s1: "?mulB (?mulB c (?mulB h (?invB c))) c
            = ?mulB c (?mulB (?mulB h (?invB c)) c)"
          by (rule hassoc[OF hc_G hhinvc hc_G])
        \<comment> \<open>Step 2: (h \<cdot> inv(c)) \<cdot> c = h \<cdot> (inv(c) \<cdot> c) by assoc.\<close>
        have s2: "?mulB (?mulB h (?invB c)) c = ?mulB h (?mulB (?invB c) c)"
          by (rule hassoc[OF hh hinvc_G hc_G])
        \<comment> \<open>Step 3: inv(c) \<cdot> c = e by left inverse.\<close>
        have s3: "?mulB (?invB c) c = ?eB" by (rule hlinv[OF hc_G])
        \<comment> \<open>Step 4: h \<cdot> e = h.\<close>
        have s4: "?mulB h ?eB = h" by (rule hrid[OF hh])
        \<comment> \<open>Combine inner: (c \<cdot> (h \<cdot> inv(c))) \<cdot> c = c \<cdot> h.\<close>
        have inner: "?mulB (?mulB c (?mulB h (?invB c))) c = ?mulB c h"
          using s1 s2 s3 s4 by (by100 simp)
        \<comment> \<open>Step 5: inv(c) \<cdot> (c \<cdot> h) = (inv(c) \<cdot> c) \<cdot> h = e \<cdot> h = h.\<close>
        have hch: "?mulB c h \<in> ?G" by (rule hmul_cl[OF hc_G hh])
        have s5: "?mulB (?invB c) (?mulB c h) = ?mulB (?mulB (?invB c) c) h"
          by (rule hassoc[OF hinvc_G hc_G hh, symmetric])
        have s6: "?mulB (?mulB (?invB c) c) h = ?mulB ?eB h" using s3 by (by100 simp)
        have s7: "?mulB ?eB h = h" by (rule hlid[OF hh])
        show "?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c) = h"
          using inner s5 s6 s7 by (by100 simp)
      qed
      \<comment> \<open>Now show set equality using hbpc2 + hconj + cancellation.\<close>
      show ?thesis
      proof (rule set_eqI)
        fix d
        show "d \<in> ?img \<longleftrightarrow> d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
        proof
          \<comment> \<open>(\<Rightarrow>) h \<in> img(E,e0). Conjugate by c to get in img(E',e0'), then by inv(c) to get in img(E',e1'). Cancellation gives h back.\<close>
          assume hd: "d \<in> ?img"
          hence hd_G: "d \<in> ?G" using himg_sub by (by100 blast)
          \<comment> \<open>c \<cdot> (d \<cdot> inv(c)) \<in> img(E', e0') via hconj.\<close>
          let ?k = "?mulB c (?mulB d (?invB c))"
          have hk_in: "?k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
            using hd hconj by (by100 blast)
          \<comment> \<open>inv(c) \<cdot> (k \<cdot> c) \<in> img(E', e1') via hbpc2.\<close>
          let ?d' = "?mulB (?invB c) (?mulB ?k c)"
          have hd'_in: "?d' \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hk_in hbpc2 by (by100 blast)
          \<comment> \<open>?d' = d by cancellation.\<close>
          have "?d' = d" by (rule hcancel[OF hd_G])
          thus "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
            using hd'_in by (by100 simp)
        next
          \<comment> \<open>(\<Leftarrow>) Decompose via hbpc2 and hconj, then use cancellation.\<close>
          assume "d \<in> top1_fundamental_group_image_hom E' TE' ?e1' B TB b0 p'"
          hence "d \<in> ?mulB (?invB c) ` ((\<lambda>h. ?mulB h c) ` (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'))"
            using hbpc2 by (by100 simp)
          then obtain k where hk: "k \<in> top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
              and hd_eq: "d = ?mulB (?invB c) (?mulB k c)" by (by100 blast)
          have "k \<in> ?mulB c ` ((\<lambda>h. ?mulB h (?invB c)) ` ?img)"
            using hk hconj by (by100 simp)
          then obtain h where hh: "h \<in> ?img"
              and hk_eq: "k = ?mulB c (?mulB h (?invB c))" by (by100 blast)
          have hh_G: "h \<in> ?G" using hh himg_sub by (by100 blast)
          have "d = ?mulB (?invB c) (?mulB (?mulB c (?mulB h (?invB c))) c)"
            using hd_eq hk_eq by (by100 simp)
          also have "\<dots> = h" by (rule hcancel[OF hh_G])
          finally show "d \<in> ?img" using hh by (by100 simp)
        qed
      qed
    qed
    show ?thesis using he1' hp'e1' himg_match by (by100 blast)
  qed
  then obtain e1' where he1': "e1' \<in> E'" and hp'e1': "p' e1' = b0"
      and himg_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
          = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (by100 blast)
  \<comment> \<open>Apply Theorem 79.2 backward with basepoint e1': get h with h(e0) = e1'.\<close>
  have "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
           \<and> h e0 = e1') \<longleftrightarrow>
       top1_fundamental_group_image_hom E TE e0 B TB b0 p
         = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'"
    by (rule Theorem_79_2[OF assms(1,2,3,4) assms(5) assms(6) hp'e1' assms(8,9,10,11)
          assms(12) he1' assms(14)])
  hence "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e1'"
    using himg_eq by (by100 blast)
  thus "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
    by (by100 blast)
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
          by (by100 fast)
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
        hcovE assms(10) hcovE' assms(11) assms(6,7,8,9) assms(12,13) hb0_B]] hRHS by (by100 blast)
qed

text \<open>Restriction of a homeomorphism to an open subset (preimage) gives a homeomorphism.\<close>
lemma homeomorphism_restrict_open:
  assumes hf: "top1_homeomorphism_on X TX Y TY f"
      and hV: "openin_on Y TY V"
      and hVY: "V \<subseteq> Y"
      and hTX: "is_topology_on X TX"
      and hTY: "is_topology_on Y TY"
  shows "top1_homeomorphism_on {x \<in> X. f x \<in> V} (subspace_topology X TX {x \<in> X. f x \<in> V})
             V (subspace_topology Y TY V) f"
proof -
  let ?X' = "{x \<in> X. f x \<in> V}"
  let ?TX' = "subspace_topology X TX ?X'"
  let ?TY' = "subspace_topology Y TY V"
  have hXsub: "?X' \<subseteq> X" by (by100 blast)
  have hbij: "bij_betw f X Y" using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hf_cont: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  have hfinv_cont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on ?X' ?TX'" by (rule subspace_topology_is_topology_on[OF hTX hXsub])
    show "is_topology_on V ?TY'" by (rule subspace_topology_is_topology_on[OF hTY hVY])
    \<comment> \<open>bij_betw: f maps ?X' bijectively to V.\<close>
    show "bij_betw f ?X' V"
    proof -
      have "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      hence "inj_on f ?X'" by (rule inj_on_subset) (by100 blast)
      moreover have "f ` ?X' = V"
      proof (rule set_eqI)
        fix y show "y \<in> f ` ?X' \<longleftrightarrow> y \<in> V"
        proof
          assume "y \<in> f ` ?X'" thus "y \<in> V" by (by100 blast)
        next
          assume "y \<in> V"
          hence "y \<in> Y" using hVY by (by100 blast)
          hence "\<exists>x\<in>X. f x = y" using hbij unfolding bij_betw_def by (by100 blast)
          then obtain x where hx: "x \<in> X" and hfx: "f x = y" by (by100 blast)
          hence "x \<in> ?X'" using \<open>y \<in> V\<close> by (by100 blast)
          thus "y \<in> f ` ?X'" using hfx by (by100 blast)
        qed
      qed
      ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
    qed
    \<comment> \<open>Continuity: f restricted to ?X' \<rightarrow> V.\<close>
    show "top1_continuous_map_on ?X' ?TX' V ?TY' f"
    proof -
      have hf_restr: "top1_continuous_map_on ?X' ?TX' Y TY f"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hf_cont hXsub])
      have himg: "f ` ?X' \<subseteq> V" by (by100 blast)
      show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF hf_restr himg hVY])
    qed
    \<comment> \<open>Inverse continuity.\<close>
    show "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into ?X' f)"
    proof -
      \<comment> \<open>inv_into X' f = inv_into X f on V (since X' \<subseteq> X, f injective, image = V).\<close>
      have hinj: "inj_on f X" using hbij unfolding bij_betw_def by (by100 blast)
      have hfinv_agree: "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y"
      proof
        fix y assume "y \<in> V"
        hence "y \<in> Y" using hVY by (by100 blast)
        hence "y \<in> f ` X" using hbij unfolding bij_betw_def by (by100 blast)
        hence "inv_into X f y \<in> X" by (rule inv_into_into)
        moreover have "f (inv_into X f y) = y"
          using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
        hence "f (inv_into X f y) \<in> V" using \<open>y \<in> V\<close> by (by100 simp)
        hence "inv_into X f y \<in> ?X'" using calculation by (by100 blast)
        thus "inv_into ?X' f y = inv_into X f y"
          by (intro inv_into_f_eq[OF inj_on_subset[OF hinj hXsub]])
             (use \<open>f (inv_into X f y) = y\<close> in \<open>by100 blast\<close>)
      qed
      \<comment> \<open>Restrict inv_into X f: Y \<rightarrow> X to V \<rightarrow> X'.\<close>
      have hfinv_restr: "top1_continuous_map_on V ?TY' X TX (inv_into X f)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hfinv_cont hVY])
      \<comment> \<open>Codomain shrink from X to X'.\<close>
      have hfinv_img: "(inv_into X f) ` V \<subseteq> ?X'"
      proof
        fix x assume "x \<in> (inv_into X f) ` V"
        then obtain y where hy: "y \<in> V" and hx: "x = inv_into X f y" by (by100 blast)
        have "inv_into X f y \<in> ?X'"
        proof -
          have "y \<in> f ` X" using hy hVY hbij unfolding bij_betw_def by (by100 blast)
          hence hiy_X: "inv_into X f y \<in> X" by (rule inv_into_into)
          have "f (inv_into X f y) = y" using \<open>y \<in> f ` X\<close> by (rule f_inv_into_f)
          hence "f (inv_into X f y) \<in> V" using hy by (by100 simp)
          thus ?thesis using hiy_X by (by100 blast)
        qed
        thus "x \<in> ?X'" using hx by (by100 simp)
      qed
      have hfinv_shrink: "top1_continuous_map_on V ?TY' ?X' ?TX' (inv_into X f)"
        by (rule top1_continuous_map_on_codomain_shrink[OF hfinv_restr hfinv_img hXsub])
      \<comment> \<open>inv_into X' f = inv_into X f on V, so continuity transfers.\<close>
      \<comment> \<open>Transfer: inv_into X' f and inv_into X f agree on V, so same continuity.\<close>
      have "\<forall>y\<in>V. inv_into ?X' f y = inv_into X f y" by (rule hfinv_agree)
      show ?thesis
        by (rule top1_continuous_map_on_agree'[OF hfinv_shrink])
           (use hfinv_agree in \<open>by100 simp\<close>)
    qed
  qed
qed

text \<open>Helper: open subset of an evenly covered set is evenly covered.
  If U is evenly covered by p and V \<subseteq> U is open in B, then V is evenly covered by p.\<close>
lemma evenly_covered_open_subset:
  assumes hcov: "top1_evenly_covered_on E TE B TB p U"
      and hV: "openin_on B TB V" and hVU: "V \<subseteq> U"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
  shows "top1_evenly_covered_on E TE B TB p V"
proof -
  \<comment> \<open>Extract sheets of U.\<close>
  obtain \<V>U where h\<V>_open: "\<forall>W\<in>\<V>U. openin_on E TE W"
      and h\<V>_disj: "\<forall>W\<in>\<V>U. \<forall>W'\<in>\<V>U. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
      and h\<V>_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>U"
      and h\<V>_homeo: "\<forall>W\<in>\<V>U. top1_homeomorphism_on W (subspace_topology E TE W) U
                                    (subspace_topology B TB U) p"
    using hcov unfolding top1_evenly_covered_on_def
    by (elim conjE exE) (by100 blast)
  \<comment> \<open>Define restricted sheets: W' = {x \<in> W | p x \<in> V} for each W \<in> \<V>U.\<close>
  let ?\<V>V = "(\<lambda>W. {x \<in> W. p x \<in> V}) ` \<V>U"
  show ?thesis unfolding top1_evenly_covered_on_def
  proof (intro conjI exI[of _ ?\<V>V])
    show "openin_on B TB V" by (rule hV)
  next
    \<comment> \<open>Each restricted sheet is open in E.\<close>
    show "\<forall>W'\<in>?\<V>V. openin_on E TE W'"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      \<comment> \<open>p|_W: W \<rightarrow> U is a homeomorphism. V is open in subspace(B,U). Preimage of V is open in W.\<close>
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      \<comment> \<open>V is open in subspace_topology B TB U (since V \<in> TB and V \<subseteq> U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      \<comment> \<open>p continuous W \<rightarrow> U means preimage of V (open in U) is open in W.\<close>
      have hp_cont_WU: "top1_continuous_map_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using hW_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W"
        using hp_cont_WU hV_in_TU unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Open in subspace(E, W) and W open in E implies open in E.\<close>
      hence "{x \<in> W. p x \<in> V} \<in> TE"
      proof -
        have "{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W" by (rule \<open>{x \<in> W. p x \<in> V} \<in> subspace_topology E TE W\<close>)
        then obtain T_open where hTo: "T_open \<in> TE" and heq: "{x \<in> W. p x \<in> V} = W \<inter> T_open"
          unfolding subspace_topology_def by (by100 blast)
        have "W \<in> TE" using hW_open unfolding openin_on_def by (by100 blast)
        hence "W \<inter> T_open \<in> TE" by (rule topology_inter2[OF hTE _ hTo])
        thus ?thesis using heq by (by100 simp)
      qed
      moreover have "{x \<in> W. p x \<in> V} \<subseteq> E"
      proof -
        have "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      ultimately show "openin_on E TE W'" unfolding hW' openin_on_def by (by100 blast)
    qed
  next
    \<comment> \<open>Restricted sheets are pairwise disjoint.\<close>
    show "\<forall>W'\<in>?\<V>V. \<forall>W''\<in>?\<V>V. W' \<noteq> W'' \<longrightarrow> W' \<inter> W'' = {}"
    proof (intro ballI impI)
      fix W' W'' assume "W' \<in> ?\<V>V" "W'' \<in> ?\<V>V" "W' \<noteq> W''"
      then obtain W1 W2 where hW1: "W1 \<in> \<V>U" and hW1': "W' = {x \<in> W1. p x \<in> V}"
          and hW2: "W2 \<in> \<V>U" and hW2': "W'' = {x \<in> W2. p x \<in> V}" by (by100 blast)
      show "W' \<inter> W'' = {}"
      proof (cases "W1 = W2")
        case True thus ?thesis using \<open>W' \<noteq> W''\<close> hW1' hW2' by (by100 simp)
      next
        case False
        hence "W1 \<inter> W2 = {}" using h\<V>_disj hW1 hW2 by (by100 blast)
        thus ?thesis using hW1' hW2' by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Union of restricted sheets = p\<inverse>(V) \<inter> E.\<close>
    show "{x\<in>E. p x \<in> V} = \<Union>?\<V>V"
    proof (rule set_eqI)
      fix x show "x \<in> {x\<in>E. p x \<in> V} \<longleftrightarrow> x \<in> \<Union>?\<V>V"
      proof
        assume "x \<in> {x\<in>E. p x \<in> V}"
        hence hxE: "x \<in> E" and hpxV: "p x \<in> V" by (by100 blast)+
        hence "p x \<in> U" using hVU by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using hxE by (by100 blast)
        hence "x \<in> \<Union>\<V>U" using h\<V>_union by (by100 simp)
        then obtain W where hW: "W \<in> \<V>U" and hxW: "x \<in> W" by (by100 blast)
        have "x \<in> {x \<in> W. p x \<in> V}" using hxW hpxV by (by100 blast)
        moreover have "{x \<in> W. p x \<in> V} \<in> ?\<V>V" using hW by (by100 blast)
        ultimately show "x \<in> \<Union>?\<V>V" by (by100 blast)
      next
        assume "x \<in> \<Union>?\<V>V"
        then obtain W where hW: "W \<in> \<V>U" and hx: "x \<in> {x \<in> W. p x \<in> V}" by (by100 blast)
        hence hxW: "x \<in> W" and hpxV: "p x \<in> V" by (by100 blast)+
        have "x \<in> \<Union>\<V>U" using hW hxW by (by100 blast)
        hence "x \<in> {x\<in>E. p x \<in> U}" using h\<V>_union by (by100 simp)
        thus "x \<in> {x\<in>E. p x \<in> V}" using hpxV by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Each restricted sheet is homeomorphic to V via p.\<close>
    show "\<forall>W'\<in>?\<V>V. top1_homeomorphism_on W' (subspace_topology E TE W') V
                          (subspace_topology B TB V) p"
    proof
      fix W' assume "W' \<in> ?\<V>V"
      then obtain W where hW: "W \<in> \<V>U" and hW': "W' = {x \<in> W. p x \<in> V}" by (by100 blast)
      have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U (subspace_topology B TB U) p"
        using h\<V>_homeo hW by (by100 blast)
      have hW_open: "openin_on E TE W" using h\<V>_open hW by (by100 blast)
      have hWsub: "W \<subseteq> E" using hW_open unfolding openin_on_def by (by100 blast)
      have hW'sub: "W' \<subseteq> W" unfolding hW' by (by100 blast)
      have hW'E: "W' \<subseteq> E" using hW'sub hWsub by (by100 blast)
      have hUopen: "openin_on B TB U" using hcov unfolding top1_evenly_covered_on_def by (by100 blast)
      have hUsub: "U \<subseteq> B" using hUopen unfolding openin_on_def by (by100 blast)
      have hVsub: "V \<subseteq> B" using hV unfolding openin_on_def by (by100 blast)
      \<comment> \<open>V is open in subspace(B, U).\<close>
      have hV_in_TU: "V \<in> subspace_topology B TB U"
        unfolding subspace_topology_def using hV hVU unfolding openin_on_def by (by100 blast)
      have hV_open_sub: "openin_on U (subspace_topology B TB U) V"
        unfolding openin_on_def using hV_in_TU hVU by (by100 blast)
      have hTW: "is_topology_on W (subspace_topology E TE W)"
        by (rule subspace_topology_is_topology_on[OF hTE hWsub])
      have hTU: "is_topology_on U (subspace_topology B TB U)"
        by (rule subspace_topology_is_topology_on[OF hTB hUsub])
      \<comment> \<open>Apply homeomorphism_restrict_open to p: W \<cong> U with open V \<subseteq> U.\<close>
      note hrestr = homeomorphism_restrict_open[OF hW_homeo hV_open_sub hVU hTW hTU]
      \<comment> \<open>subspace_topology_trans: subspace(W, subspace(E,W), W') = subspace(E, W').\<close>
      have hTW'_eq: "subspace_topology W (subspace_topology E TE W) {x \<in> W. p x \<in> V}
          = subspace_topology E TE {x \<in> W. p x \<in> V}"
        by (rule subspace_topology_trans) (by100 force)
      have hTV'_eq: "subspace_topology U (subspace_topology B TB U) V
          = subspace_topology B TB V"
        by (rule subspace_topology_trans[OF hVU])
      show "top1_homeomorphism_on W' (subspace_topology E TE W') V (subspace_topology B TB V) p"
        using hrestr hTW'_eq hTV'_eq unfolding hW' by (by100 simp)
    qed
  qed
qed

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
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
      \<and> q e0 = y0 \<and> top1_continuous_map_on E TE Y TY q"
  proof -
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      by (rule top1_covering_map_on_continuous[OF assms(4)])
    have hE_pc: "top1_path_connected_on E TE"
      using assms(5) unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>E is locally path-connected (covering space of locally path-connected B,
       or directly from the covering structure + local homeomorphisms).\<close>
    have hE_lpc: "top1_locally_path_connected_on E TE" by (rule assms(7))
    have hpe0: "p e0 = r y0" using hry0 by (by100 simp)
    \<comment> \<open>E simply connected \<Rightarrow> p_*(\<pi>_1(E)) = {e} \<subseteq> r_*(\<pi>_1(Y)).\<close>
    have himg_triv: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        = {top1_fundamental_group_id B TB (r y0)}"
      by (rule simply_connected_trivial_image[OF assms(5) assms(4) he0 hpe0 hTB])
    have hsubgrp: "top1_fundamental_group_image_hom E TE e0 B TB (r y0) p
        \<subseteq> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
    proof -
      \<comment> \<open>{e} is in any image_hom (the identity class is always in the image).\<close>
      have "top1_fundamental_group_id B TB (r y0)
          \<in> top1_fundamental_group_image_hom Y TY y0 B TB (r y0) r"
      proof -
        \<comment> \<open>id_Y \<in> carrier(Y). induced(id_Y) = {g | loop_equiv(r\<circ>const_y0, g)} = id_B.\<close>
        have hid_Y: "top1_fundamental_group_id Y TY y0 \<in> top1_fundamental_group_carrier Y TY y0"
          using top1_fundamental_group_is_group[OF hTY hy0] unfolding top1_is_group_on_def by (by100 blast)
        have "top1_fundamental_group_induced_on Y TY y0 B TB (r y0) r
            (top1_fundamental_group_id Y TY y0)
          = top1_fundamental_group_id B TB (r y0)"
        proof -
          \<comment> \<open>induced(id) = {g | \<exists>f\<in>id. loop_equiv(r\<circ>f, g)} = {g | loop_equiv(r\<circ>const, g)} = id_B.\<close>
          have hconst_in: "top1_constant_path y0 \<in> top1_fundamental_group_id Y TY y0"
            unfolding top1_fundamental_group_id_def
            using top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTY hy0]] by (by100 blast)
          have hrconst: "r \<circ> top1_constant_path y0 = top1_constant_path (r y0)"
            unfolding top1_constant_path_def by (rule ext) (by100 simp)
          show ?thesis
            unfolding top1_fundamental_group_induced_on_def top1_fundamental_group_id_def
          proof (rule set_eqI, rule iffI)
            fix k
            assume "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
            then obtain fa where hfa: "top1_loop_equiv_on Y TY y0 (top1_constant_path y0) fa"
                and hk: "top1_loop_equiv_on B TB (r y0) (r \<circ> fa) k" by (by100 blast)
            have hfa_loop: "top1_is_loop_on Y TY y0 fa"
              using hfa unfolding top1_loop_equiv_on_def by (by100 blast)
            have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
            proof -
              have "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) (r \<circ> fa)"
                using top1_induced_preserves_loop_equiv[OF hTY
                  top1_covering_map_on_continuous[OF assms(6)]
                  top1_constant_path_is_loop[OF hTY hy0] hfa_loop hfa] by (by100 simp)
              thus ?thesis .
            qed
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) (r \<circ> fa)"
              using hrconst by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTB this hk]
            show "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}" by (by100 blast)
          next
            fix k assume "k \<in> {g. top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) g}"
            hence "top1_loop_equiv_on B TB (r y0) (top1_constant_path (r y0)) k" by (by100 blast)
            hence "top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k"
              using hrconst by (by100 simp)
            show "k \<in> {g'. \<exists>fa\<in>{g. top1_loop_equiv_on Y TY y0 (top1_constant_path y0) g}.
                top1_loop_equiv_on B TB (r y0) (r \<circ> fa) g'}"
              apply (rule CollectI)
              apply (rule bexI[of _ "top1_constant_path y0"])
              apply (rule \<open>top1_loop_equiv_on B TB (r y0) (r \<circ> top1_constant_path y0) k\<close>)
              using hconst_in unfolding top1_fundamental_group_id_def by (by100 blast)
          qed
        qed
        thus ?thesis unfolding top1_fundamental_group_image_hom_def using hid_Y by (by100 force)
      qed
      thus ?thesis using himg_triv by (by100 simp)
    qed
    from general_lifting_criterion[OF assms(6) hTE hTB hTY hp_cont hE_pc hE_lpc he0 hy0
        hpe0 hsubgrp]
    obtain q where "\<forall>e\<in>E. q e \<in> Y" "\<forall>e\<in>E. r (q e) = p e"
        "q e0 = y0" "top1_continuous_map_on E TE Y TY q" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain q where hq_Y: "\<forall>e\<in>E. q e \<in> Y" and hq_rp: "\<forall>e\<in>E. r (q e) = p e"
      and hq_e0: "q e0 = y0" and hq_cont: "top1_continuous_map_on E TE Y TY q" by (by100 blast)
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.
     For each y \<in> Y, take b = r(y). Take U evenly covered by both p and r.
     Slices of p\<inverse>(U) are {U_\<alpha>}, slices of r\<inverse>(U) are {V_\<beta>}.
     q maps each U_\<alpha> into some V_\<beta> (connectedness).
     q restricted to U_\<alpha> = r_\<beta>\<inverse> \<circ> p_\<alpha>, a homeomorphism.
     So q evenly covers each V_\<beta>.\<close>
  have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
  have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
  have hq_surj: "q ` E = Y"
  proof (rule equalityI)
    show "q ` E \<subseteq> Y" using hq_Y by (by100 blast)
    show "Y \<subseteq> q ` E"
    proof -
      \<comment> \<open>q(E) is non-empty (contains y0).\<close>
      have hy0_qE: "y0 \<in> q ` E" using hq_e0 he0 by (by100 blast)
      \<comment> \<open>q(E) is open in Y: for each y = q(e), use covering structure to find
         a neighborhood of y contained in q(E). The r-slice containing y maps
         homeomorphically to an open U \<subseteq> B. The p-slice containing e maps
         homeomorphically to U. So q = r^{-1} \<circ> p maps a neighborhood of e
         onto a neighborhood of y, giving y \<in> interior of q(E).\<close>
      have hqE_open: "openin_on Y TY (q ` E)"
        sorry \<comment> \<open>Local homeomorphism argument: q is open map.\<close>
      \<comment> \<open>Y - q(E) is open in Y: for y \<in> Y - q(E), the r-slice containing y is
         either entirely in q(E) or disjoint (by connectedness of the slice).
         Since y \<notin> q(E), the slice is disjoint.\<close>
      have hqE_closed: "closedin_on Y TY (q ` E)"
        sorry \<comment> \<open>Complement is open: each r-slice meeting q(E) is fully in q(E).\<close>
      \<comment> \<open>Y is connected (path-connected covering space assumption or derived).\<close>
      have hY_conn: "top1_connected_on Y TY"
        sorry \<comment> \<open>Covering space of path-connected base is connected (if non-empty).\<close>
      \<comment> \<open>Connected + non-empty clopen subset = whole space.\<close>
      have "q ` E = {} \<or> q ` E = Y"
        using iffD1[OF connected_iff_clopen_openin_on[OF assms(3)] hY_conn]
              hqE_open hqE_closed by (by100 blast)
      moreover have "q ` E \<noteq> {}" using hy0_qE by (by100 blast)
      ultimately show "Y \<subseteq> q ` E" by (by100 blast)
    qed
  qed
  have hq_cov: "\<forall>y\<in>Y. \<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
  proof
    fix y assume hy: "y \<in> Y"
    let ?b = "r y"
    have hb_B: "?b \<in> B"
      using hy top1_covering_map_on_surj[OF assms(6)] by (by100 blast)
    \<comment> \<open>Take U evenly covered by both p and r.\<close>
    obtain Up where hUp_b: "?b \<in> Up" and hUp_cov_p: "top1_evenly_covered_on E TE B TB p Up"
      using hb_B assms(4) unfolding top1_covering_map_on_def by (by100 blast)
    obtain Ur where hUr_b: "?b \<in> Ur" and hUr_cov_r: "top1_evenly_covered_on Y TY B TB r Ur"
      using hb_B assms(6) unfolding top1_covering_map_on_def by (by100 blast)
    let ?U = "Up \<inter> Ur"
    \<comment> \<open>U = Up \<inter> Ur is open, contains b, and is evenly covered by both p and r.\<close>
    have hU_b: "?b \<in> ?U" using hUp_b hUr_b by (by100 blast)
    \<comment> \<open>The restriction of a covering to an open subset is still a covering.\<close>
    \<comment> \<open>Get the slice of r\<inverse>(U) containing y. This will be the evenly covered neighborhood.\<close>
    obtain \<V>r where h\<V>r_open: "\<forall>V\<in>\<V>r. openin_on Y TY V"
        and h\<V>r_disj: "\<forall>V\<in>\<V>r. \<forall>V'\<in>\<V>r. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r_union: "{x\<in>Y. r x \<in> Ur} = \<Union>\<V>r"
        and h\<V>r_homeo: "\<forall>V\<in>\<V>r. top1_homeomorphism_on V (subspace_topology Y TY V) Ur
                                      (subspace_topology B TB Ur) r"
      using hUr_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>y is in r\<inverse>(Ur), so y \<in> \<Union>\<V>r. Pick the slice V0 containing y.\<close>
    have hy_in_rU: "y \<in> {x\<in>Y. r x \<in> Ur}" using hy hUr_b by (by100 blast)
    hence "y \<in> \<Union>\<V>r" using h\<V>r_union by (by100 simp)
    then obtain V0 where hV0: "V0 \<in> \<V>r" and hy_V0: "y \<in> V0" by (by100 blast)
    \<comment> \<open>V0 is our evenly covered neighborhood.\<close>
    \<comment> \<open>To show: top1_evenly_covered_on E TE Y TY q V0.\<close>
    \<comment> \<open>Each slice U_\<alpha> of p\<inverse>(U) that maps into V0 maps homeomorphically via q.\<close>
    \<comment> \<open>Restrict p-covering to Up\<inter>Ur.\<close>
    have hTE: "is_topology_on E TE" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTB: "is_topology_on B TB" using assms(2) unfolding is_topology_on_strict_def by (by100 blast)
    have hTY: "is_topology_on Y TY" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hUp_open: "openin_on B TB Up"
      using hUp_cov_p unfolding top1_evenly_covered_on_def by (by100 blast)
    have hUr_open: "openin_on B TB Ur"
      using hUr_cov_r unfolding top1_evenly_covered_on_def by (by100 blast)
    have hU_open: "openin_on B TB ?U"
    proof -
      have "Up \<in> TB" using hUp_open unfolding openin_on_def by (by100 blast)
      moreover have "Ur \<in> TB" using hUr_open unfolding openin_on_def by (by100 blast)
      ultimately have "Up \<inter> Ur \<in> TB" by (rule topology_inter2[OF hTB])
      moreover have "Up \<inter> Ur \<subseteq> B" using hUp_open unfolding openin_on_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hU_cov_p: "top1_evenly_covered_on E TE B TB p ?U"
      by (rule evenly_covered_open_subset[OF hUp_cov_p hU_open _ hTE hTB]) (by100 blast)
    have hU_cov_r: "top1_evenly_covered_on Y TY B TB r ?U"
      by (rule evenly_covered_open_subset[OF hUr_cov_r hU_open _ hTY hTB]) (by100 blast)
    \<comment> \<open>Get p-slices and r-slices over U = Up\<inter>Ur.\<close>
    obtain \<V>p where h\<V>p_open: "\<forall>V\<in>\<V>p. openin_on E TE V"
        and h\<V>p_disj: "\<forall>V\<in>\<V>p. \<forall>V'\<in>\<V>p. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>p_union: "{x\<in>E. p x \<in> ?U} = \<Union>\<V>p"
        and h\<V>p_homeo: "\<forall>V\<in>\<V>p. top1_homeomorphism_on V (subspace_topology E TE V) ?U
                                      (subspace_topology B TB ?U) p"
      using hU_cov_p unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    obtain \<V>r' where h\<V>r'_open: "\<forall>V\<in>\<V>r'. openin_on Y TY V"
        and h\<V>r'_disj: "\<forall>V\<in>\<V>r'. \<forall>V'\<in>\<V>r'. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        and h\<V>r'_union: "{x\<in>Y. r x \<in> ?U} = \<Union>\<V>r'"
        and h\<V>r'_homeo: "\<forall>V\<in>\<V>r'. top1_homeomorphism_on V (subspace_topology Y TY V) ?U
                                      (subspace_topology B TB ?U) r"
      using hU_cov_r unfolding top1_evenly_covered_on_def
      by (elim conjE exE) (by100 blast)
    \<comment> \<open>V0' = the r'-slice containing y (over U = Up\<inter>Ur).\<close>
    have hy_in_rU': "y \<in> {x\<in>Y. r x \<in> ?U}" using hy hU_b by (by100 blast)
    hence "y \<in> \<Union>\<V>r'" using h\<V>r'_union by (by100 simp)
    then obtain V0' where hV0': "V0' \<in> \<V>r'" and hy_V0': "y \<in> V0'" by (by100 blast)
    \<comment> \<open>V0' is evenly covered by q: each p-slice U_\<alpha> over U maps homeo to V0' via q.\<close>
    \<comment> \<open>For each U_\<alpha> \<in> \<V>p: p|_{U_\<alpha>}: U_\<alpha> \<cong> U and r|_{V0'}: V0' \<cong> U.
       So q|_{U_\<alpha>} = (r|_{V0'})\<inverse> \<circ> p|_{U_\<alpha>}: U_\<alpha> \<cong> V0'.
       But only for those U_\<alpha> where q(U_\<alpha>) \<subseteq> V0'.\<close>
    \<comment> \<open>For each p-slice W, q maps {e\<in>W | q e \<in> V0'} homeomorphically to V0'.
       Proof: on this subset, q = inv_into V0' r \<circ> p (since r(q e) = p e and q e \<in> V0').
       Both p|_W and r|_{V0'} are homeomorphisms to U, so q is their composition.
       The family of non-empty {e\<in>W | q e \<in> V0'} covers q\<inverse>(V0'), is disjoint and open.\<close>
    have hV0'_open: "openin_on Y TY V0'" using h\<V>r'_open hV0' by (by100 blast)
    show "\<exists>V. y \<in> V \<and> top1_evenly_covered_on E TE Y TY q V"
    proof (rule exI[of _ V0'], intro conjI)
      show "y \<in> V0'" by (rule hy_V0')
      show "top1_evenly_covered_on E TE Y TY q V0'"
        sorry \<comment> \<open>V0' evenly covered: family = {{e\<in>W|q e\<in>V0'} | W\<in>\<V>p, nonempty}.
           Open: q continuous + V0' open. Disjoint: inherited from \<V>p.
           Union = q\<inverse>(V0'). Homeo: q = inv(r|_{V0'}) \<circ> p on each piece.\<close>
    qed
  qed
  show ?thesis
  proof (rule exI[of _ q])
    show "top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
      unfolding top1_covering_map_on_def using hq_cont hq_surj hq_cov hq_rp by (by100 blast)
  qed
qed

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
      and "top1_locally_path_connected_on E TE"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-6) by (by100 blast)

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
  \<comment> \<open>Existentially package the construction.\<close>
  obtain E' TE' p' e0' where
        hTE': "is_topology_on_strict E' TE'"
    and hp'_cov: "top1_covering_map_on E' TE' B TB p'"
    and hE'_pc: "top1_path_connected_on E' TE'"
    and hE'_lpc: "top1_locally_path_connected_on E' TE'"
    and he0': "e0' \<in> E'" and hp'e0: "p' e0' = b0"
    and hp'_img: "top1_fundamental_group_image_hom E' TE' e0' B TB b0 p' = H"
    sorry \<comment> \<open>Full coset-space construction. Requires defining E' as H-right-cosets of path classes,
       topology via path-extension basis, verifying covering + connectivity + p'_*(π₁) = H.
       Semilocal simple connectivity (assms(4)) ensures the evenly-covered property.\<close>
  show ?thesis sorry \<comment> \<open>Assembly: existential packing with type unification. E'::path-set set, etc.\<close>
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

(** from \<S>83 Theorem 83.4 (Munkres numbering): any covering space of a graph is itself a graph. **)
theorem Theorem_83_4_covering_of_graph_is_graph:
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
  \<comment> \<open>Step 1: For each arc A \<in> \<A>B, the preimage p\<inverse>(A) splits into sheets.
     Each sheet is homeomorphic to A via p (local homeomorphism), hence an arc.\<close>
  have hAE: "\<exists>\<A>E. (\<forall>A'\<in>\<A>E. A' \<subseteq> E \<and> top1_is_arc_on A' (subspace_topology E TE A'))
      \<and> (\<Union>\<A>E) = E"
    sorry \<comment> \<open>Lift arcs: each evenly-covered neighborhood splits A into sheets.\<close>
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have hE_hausdorff: "is_hausdorff_on E TE"
    sorry \<comment> \<open>Local homeomorphism + Hausdorff base = Hausdorff total space.\<close>
  \<comment> \<open>Step 3: Intersection and weak topology conditions lift from B to E.\<close>
  show ?thesis sorry \<comment> \<open>Combine: lifted arcs + Hausdorff + intersection + weak topology.\<close>
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
  \<comment> \<open>Step 1: X is a graph, so extract arcs.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 2: Choose a maximal tree T \<subseteq> X. A maximal tree exists by Zorn's lemma
     (or, for countable graphs, by explicit construction).\<close>
  obtain T :: "'a set" where hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_max: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
    sorry \<comment> \<open>Existence of maximal tree (Munkres Lemma 84.3).\<close>
  \<comment> \<open>Step 3: X/T is a wedge of circles (one per edge not in T).
     The edges not in T form loops when their endpoints are identified via T-collapse.\<close>
  obtain n :: nat and W :: "'b set" and TW :: "'b set set" and q :: "'a \<Rightarrow> 'b" and p :: 'b
    where hW_wedge: "top1_is_wedge_of_circles_on W TW {..<n} p"
      and hq_quotient: "top1_quotient_map_on X TX W TW q"
      and hq_T: "\<forall>x\<in>T. q x = p"
    sorry \<comment> \<open>Quotient X/T = wedge of circles (Munkres Lemma 84.5).\<close>
  \<comment> \<open>Step 4: The quotient map q: X \<rightarrow> X/T is a homotopy equivalence
     (since T is contractible in X).\<close>
  have hq_equiv: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    sorry \<comment> \<open>Homotopy equivalence of quotient: Theorem 58.7 or direct SvK argument.\<close>
  \<comment> \<open>Step 5: \<pi>_1(X/T) = \<pi>_1(wedge of n circles) is free on n generators (Theorem 71.1).\<close>
  have hW_free: "\<exists>(G::'g set) mul e invg (\<iota>::'s \<Rightarrow> 'g) S.
      top1_is_free_group_full_on G mul e invg \<iota> S
      \<and> top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier W TW (q x0))
          (top1_fundamental_group_mul W TW (q x0))"
    sorry \<comment> \<open>Theorem_71_1 applied to the wedge W.\<close>
  \<comment> \<open>Step 6: Combine: \<pi>_1(X) \<cong> \<pi>_1(W) \<cong> free group \<Rightarrow> \<pi>_1(X) is free.\<close>
  show ?thesis sorry \<comment> \<open>Transitivity: groups_isomorphic_trans_fwd + sym. Needs group axioms for sym.\<close>
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
      and "e0' \<in> E'"
    sorry \<comment> \<open>Existence of covering space (Theorem 82.1) for the H-image in \<pi>_1(X).\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2: covering of graph is graph).
     \<pi>_1(E) is free (Theorem 84.7: fund group of connected graph is free).
     p_* injective (covering maps induce injections on \<pi>_1).
     H \<cong> p_*(\<pi>_1(E)) which is free (subgroup of free = free via injection).\<close>
  show ?thesis sorry \<comment> \<open>Combine: E graph (Thm 83.2) \<Rightarrow> \<pi>_1(E) free (Thm 84.7) \<Rightarrow> H free.\<close>
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
    sorry \<comment> \<open>Wedge of n+1 circles realizes F.\<close>
  \<comment> \<open>Step 2: H \<le> F corresponds to a k-sheeted covering E of X.
     By Theorem 82.1, there exists a covering E with p_*(\<pi>_1(E)) = H-image.\<close>
  obtain E' :: "'b set" and TE' :: "'b set set" and p' :: "'b \<Rightarrow> 'a"
    where hE'_cov: "top1_covering_map_on E' TE' X TX p'"
      and hE'_graph: "top1_is_graph_on E' TE'"
      and hE'_conn: "top1_connected_on E' TE'"
    sorry \<comment> \<open>Covering existence (Theorem 82.1) + covering of graph is graph (Theorem 83.2).\<close>
  \<comment> \<open>Step 3: Euler characteristic. X has 1 vertex, n+1 edges, \<chi>(X) = -n.
     E has k sheets, so \<chi>(E) = k \<cdot> \<chi>(X) = -kn.
     E has k vertices, k(n+1) edges, rank(\<pi>_1(E)) = kn+1.\<close>
  have hE'_free: "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
      top1_is_free_group_full_on H mul e invg \<iota>H SH \<and> card SH = k * n + 1"
    sorry \<comment> \<open>\<pi>_1(E) is free (Theorem 84.7). Euler char gives rank kn+1.\<close>
  show ?thesis using hE'_free by (by100 blast)
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end



























































































































































































































































































 
  
   
    



  








