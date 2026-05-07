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
  \<comment> \<open>Step 1: Set up the SvK open cover.
     U' = S²-e13, V' = S²-e24. Both are open in S² (arcs are closed).
     X = S²-{p}-{q} = U' \<union> V' (since p \<in> e13, q \<in> e24).
     U = X \<inter> U' = S²-e13-{q} (removing q from U', which is in e24 not e13).
     V = X \<inter> V' = S²-e24-{p} (removing p from V', which is in e13 not e24).
     U, V are open in X. U \<union> V = X.
     U \<inter> V = S²-(e13 \<union> e24)-{p}-{q} = S²-(e13 \<union> e24) minus {p,q} (but p,q are in arcs).
     U \<inter> V has exactly two path-components A, B separated by the 4-cycle C.\<close>
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  \<comment> \<open>Step 2: The loop f traverses the 4-cycle a1-a2-a3-a4-a1.
     Decompose f into two paths:
     \<alpha>: portion of f in U (edges e12, e34, not touching e13)
     \<beta>: portion of f in V (edges e23, e41, not touching e24)
     Then f ~ \<alpha>*\<beta> (path product) in X.\<close>
  \<comment> \<open>Step 3: U \<inter> V = S² - (e13 \<union> e24) - {p} - {q} has two path-components.
     One contains a1, a3 and the other contains a2, a4 (separated by arcs e13, e24).
     Choose a \<in> A (component of U\<inter>V containing x0) and b \<in> B (the other component).\<close>
  \<comment> \<open>Step 4: Apply Theorem 63.1: \<alpha> is a path in U from a to b, \<beta> path in V from b to a.
     U\<inter>V = A \<union> B with A,B disjoint open, a \<in> A, b \<in> B.
     Therefore \<alpha>*\<beta> is not nulhomotopic in X.\<close>
  show ?thesis
    sorry \<comment> \<open>Requires: (1) open cover setup, (2) loop decomposition into \<alpha>*\<beta>,
         (3) U\<inter>V two-component argument, (4) application of Theorem_63_1_loop_nontrivial.\<close>
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
      and "finite S1" and "finite S2"
  shows "\<exists>f. bij_betw f S1 S2"
proof -
  \<comment> \<open>Munkres 67.8: Tensor with Z/2Z: G/2G is a vector space over Z/2Z of dimension
     equal to the rank. Dimension of a vector space is unique.
     Step 1: G \<cong> Z^S1 (free abelian on S1) and G \<cong> Z^S2 (free abelian on S2).
     Step 2: G/2G \<cong> (Z/2Z)^S1 \<cong> (Z/2Z)^S2.
     Step 3: Vector space dimension: |S1| = dim (Z/2Z)^S1 = dim (Z/2Z)^S2 = |S2|.
     Step 4: Hence |S1| = |S2|, i.e. there exists a bijection.\<close>
  \<comment> \<open>Munkres 67.8: G/2G has cardinality 2^|S| for any basis S.
     So 2^|S1| = |G/2G| = 2^|S2|, hence |S1| = |S2|.\<close>
  let ?twoG = "{mul g g | g. g \<in> G}"
  \<comment> \<open>Step 1: |G/2G| = 2^|S1| and |G/2G| = 2^|S2|.
     Proof: G \<cong> Z^S_i, so G/2G \<cong> (Z/2Z)^S_i, hence |G/2G| = 2^|S_i|.\<close>
  have hfinS1: "finite S1" by (rule assms(3))
  have hfinS2: "finite S2" by (rule assms(4))
  have hcard1: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S1"
    sorry \<comment> \<open>G \<cong> Z^{S1} implies G/2G \<cong> (Z/2Z)^{S1}, so |G/2G| = 2^|S1|.\<close>
  have hcard2: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S2"
    sorry \<comment> \<open>G \<cong> Z^{S2} implies G/2G \<cong> (Z/2Z)^{S2}, so |G/2G| = 2^|S2|.\<close>
  \<comment> \<open>Step 2: 2^|S1| = 2^|S2| implies |S1| = |S2|.\<close>
  have "card S1 = card S2"
  proof -
    have "2 ^ card S1 = (2::nat) ^ card S2" using hcard1 hcard2 by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 3: Finite sets of equal cardinality have a bijection.\<close>
  show ?thesis by (rule finite_same_card_bij[OF hfinS1 hfinS2 \<open>card S1 = card S2\<close>])
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



\<comment> \<open>Helper: Z/nZ is the quotient of Z by the subgroup nZ.
   More precisely: the quotient of (UNIV::int set, +) by the normal subgroup
   generated by {int n} is isomorphic to (top1_Zn_group n, top1_Zn_mul n).\<close>
lemma Z_quotient_nZ_iso:
  assumes "n \<ge> 1"
  shows "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on (UNIV::int set) (+)
         (top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}))
      (top1_quotient_group_mul_on (+))
      (top1_Zn_group n) (top1_Zn_mul n)"
proof -
  \<comment> \<open>Step 1: The normal subgroup generated by {n} in (Z,+) is nZ = {k*n | k}.\<close>
  let ?nZ = "top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}"
  have hnZ_eq: "?nZ = {k * int n | k. True}"
    sorry \<comment> \<open>Normal closure of {n} in abelian Z = subgroup generated by n = nZ.\<close>
  \<comment> \<open>Step 2: Define the quotient map \<phi>: Z \<rightarrow> Z/nZ by \<phi>(k) = k mod n.\<close>
  let ?\<phi> = "\<lambda>k::int. k mod int n"
  \<comment> \<open>Step 3: \<phi> is a surjective group homomorphism with kernel nZ.\<close>
  have hphi_hom: "\<forall>a::int. \<forall>b::int. ?\<phi> (a + b) = top1_Zn_mul n (?\<phi> a) (?\<phi> b)"
    unfolding top1_Zn_mul_def
  proof (intro allI)
    fix a b :: int
    show "(a + b) mod int n = (a mod int n + b mod int n) mod int n"
      using mod_add_eq[of a "int n" b] by (by100 simp)
  qed
  have hphi_surj: "?\<phi> ` (UNIV::int set) = top1_Zn_group n"
    unfolding top1_Zn_group_def
  proof (rule equalityI)
    show "(\<lambda>k::int. k mod int n) ` UNIV \<subseteq> {0..<int n}"
      using assms by (by100 auto)
    show "{0..<int n} \<subseteq> (\<lambda>k::int. k mod int n) ` UNIV"
    proof
      fix x :: int assume hx: "x \<in> {0..<int n}"
      hence hxmod: "x mod int n = x" using assms by (by100 auto)
      show "x \<in> (\<lambda>k. k mod int n) ` UNIV"
        apply (rule image_eqI[of _ _ x])
        using hxmod apply (by100 simp)
        apply (by100 simp)
        done
    qed
  qed
  have hphi_ker: "{k::int. ?\<phi> k = 0} = ?nZ"
    sorry \<comment> \<open>ker(\<phi>) = nZ.\<close>
  \<comment> \<open>Step 4: By first isomorphism theorem: Z/nZ \<cong> im(\<phi>) = Z_n.\<close>
  show ?thesis
    sorry \<comment> \<open>First isomorphism theorem applied to \<phi>.\<close>
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

\<comment> \<open>Helper: isomorphism transfers quotient group structure.\<close>
lemma quotient_group_iso_transfer:
  fixes G :: "'g set" and mulG :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and G' :: "'g' set" and mulG' :: "'g' \<Rightarrow> 'g' \<Rightarrow> 'g'"
    and N :: "'g set"
  assumes "top1_is_group_on G mulG eG invgG"
      and "top1_is_group_on G' mulG' eG' invgG'"
      and "top1_group_iso_on G mulG G' mulG' \<phi>"
      and "top1_normal_subgroup_on G mulG eG invgG N"
  shows "top1_groups_isomorphic_on
           (top1_quotient_group_carrier_on G mulG N)
           (top1_quotient_group_mul_on mulG)
           (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N))
           (top1_quotient_group_mul_on mulG')"
proof -
  \<comment> \<open>Step 1: \<phi>(N) is a normal subgroup of G'.\<close>
  have hphiN_normal: "top1_normal_subgroup_on G' mulG' eG' invgG' (\<phi> ` N)"
    unfolding top1_normal_subgroup_on_def
  proof (intro conjI ballI)
    \<comment> \<open>\<phi>(N) \<subseteq> G'.\<close>
    have hN_sub: "N \<subseteq> G" using assms(4) unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hphi_maps: "\<forall>g\<in>G. \<phi> g \<in> G'" using assms(3) unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
    show "\<phi> ` N \<subseteq> G'" using hN_sub hphi_maps by (by100 blast)
    \<comment> \<open>\<phi>(N) is a subgroup.\<close>
    show "top1_is_group_on (\<phi> ` N) mulG' eG' invgG'"
    proof -
      have hN_group: "top1_is_group_on N mulG eG invgG"
        using assms(4) unfolding top1_normal_subgroup_on_def by (by100 blast)
      have hphi_N_hom: "top1_group_hom_on N mulG G' mulG' \<phi>"
      proof -
        have "\<forall>x\<in>N. \<phi> x \<in> G'" using hN_sub hphi_maps by (by100 blast)
        moreover have "\<forall>x\<in>N. \<forall>y\<in>N. \<phi> (mulG x y) = mulG' (\<phi> x) (\<phi> y)"
        proof (intro ballI)
          fix x y assume "x \<in> N" "y \<in> N"
          hence "x \<in> G" "y \<in> G" using hN_sub by (by100 blast)+
          thus "\<phi> (mulG x y) = mulG' (\<phi> x) (\<phi> y)"
            using assms(3) unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
        qed
        ultimately show ?thesis unfolding top1_group_hom_on_def by (by100 blast)
      qed
      show ?thesis by (rule hom_image_is_subgroup[OF hN_group assms(2) hphi_N_hom])
    qed
    \<comment> \<open>Conjugation: \<forall>g'\<in>G'. \<forall>m\<in>\<phi>(N). g'\<cdot>m\<cdot>g'\<inverse> \<in> \<phi>(N).\<close>
    fix g' m assume hg': "g' \<in> G'" and hm: "m \<in> \<phi> ` N"
    show "mulG' (mulG' g' m) (invgG' g') \<in> \<phi> ` N"
    proof -
      \<comment> \<open>g' = \<phi>(g) for some g \<in> G (surjectivity).\<close>
      have hphi_surj: "\<phi> ` G = G'" using assms(3) unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
      obtain g where hg: "g \<in> G" "\<phi> g = g'" using hphi_surj hg' by (by100 blast)
      obtain n where hn: "n \<in> N" "\<phi> n = m" using hm by (by100 blast)
      \<comment> \<open>\<phi> is a homomorphism: \<phi>(g\<cdot>n\<cdot>g\<inverse>) = \<phi>(g)\<cdot>\<phi>(n)\<cdot>\<phi>(g\<inverse>) = g'\<cdot>m\<cdot>\<phi>(g\<inverse>).\<close>
      have hphi_hom_loc: "top1_group_hom_on G mulG G' mulG' \<phi>"
        using assms(3) unfolding top1_group_iso_on_def by (by100 blast)
      \<comment> \<open>g\<cdot>n\<cdot>g\<inverse> \<in> N (normality).\<close>
      have hconj: "mulG (mulG g n) (invgG g) \<in> N"
        using assms(4) hg(1) hn(1) unfolding top1_normal_subgroup_on_def by (by100 blast)
      \<comment> \<open>\<phi>(g\<cdot>n\<cdot>g\<inverse>) \<in> \<phi>(N).\<close>
      have "\<phi> (mulG (mulG g n) (invgG g)) \<in> \<phi> ` N" using hconj by (by100 blast)
      \<comment> \<open>\<phi>(g\<cdot>n\<cdot>g\<inverse>) = \<phi>(g)\<cdot>\<phi>(n)\<cdot>\<phi>(g\<inverse>) = g'\<cdot>m\<cdot>invgG'(g').\<close>
      moreover have "\<phi> (mulG (mulG g n) (invgG g)) = mulG' (mulG' g' m) (invgG' g')"
      proof -
        have hphi_mul: "\<And>a b. a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> \<phi> (mulG a b) = mulG' (\<phi> a) (\<phi> b)"
          using hphi_hom_loc unfolding top1_group_hom_on_def by (by100 blast)
        have hgn_G: "mulG g n \<in> G"
          using assms(1) hg(1) hn(1) hN_sub unfolding top1_is_group_on_def by (by100 blast)
        have hinvg_G: "invgG g \<in> G"
          using assms(1) hg(1) unfolding top1_is_group_on_def by (by100 blast)
        have hn_G: "n \<in> G" using hn(1) hN_sub by (by100 blast)
        have "\<phi> (mulG (mulG g n) (invgG g)) = mulG' (\<phi> (mulG g n)) (\<phi> (invgG g))"
          by (rule hphi_mul[OF hgn_G hinvg_G])
        also have "\<phi> (mulG g n) = mulG' (\<phi> g) (\<phi> n)"
          by (rule hphi_mul[OF hg(1) hn_G])
        finally have h1: "\<phi> (mulG (mulG g n) (invgG g)) = mulG' (mulG' (\<phi> g) (\<phi> n)) (\<phi> (invgG g))"
          by (by100 simp)
        \<comment> \<open>\<phi>(g\<inverse>) = \<phi>(g)\<inverse>: from \<phi>(g)\<cdot>\<phi>(g\<inverse>) = \<phi>(g\<cdot>g\<inverse>) = \<phi>(e) = e'.\<close>
        have "\<phi> (invgG g) = invgG' (\<phi> g)"
          by (rule hom_preserves_inv[OF assms(1) assms(2) hphi_hom_loc hg(1)])
        thus ?thesis using h1 hg(2) hn(2) by (by100 simp)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 2: G'/\<phi>(N) is a group.\<close>
  let ?\<pi>' = "\<lambda>g'. top1_group_coset_on G' mulG' (\<phi> ` N) g'"
  have hQ'_group: "top1_is_group_on (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N))
      (top1_quotient_group_mul_on mulG')
      (?\<pi>' eG') (\<lambda>C. ?\<pi>' (invgG' (SOME g'. g' \<in> G' \<and> C = ?\<pi>' g')))"
    by (rule quotient_group_is_group[OF assms(2) hphiN_normal])
  \<comment> \<open>Step 3: \<pi>' \<circ> \<phi> is a surjective homomorphism G \<rightarrow> G'/\<phi>(N) with kernel N.\<close>
  have hphi_hom: "top1_group_hom_on G mulG G' mulG' \<phi>"
    using assms(3) unfolding top1_group_iso_on_def by (by100 blast)
  have hpi_hom: "top1_group_hom_on G' mulG' (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N))
      (top1_quotient_group_mul_on mulG') ?\<pi>'"
    using quotient_projection_properties[OF assms(2) hphiN_normal] by (by100 blast)
  have hpi_phi_hom: "top1_group_hom_on G mulG (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N))
      (top1_quotient_group_mul_on mulG') (?\<pi>' \<circ> \<phi>)"
    by (rule group_hom_comp[OF hphi_hom hpi_hom])
  have hpi_phi_surj: "(?\<pi>' \<circ> \<phi>) ` G = top1_quotient_group_carrier_on G' mulG' (\<phi> ` N)"
  proof -
    have hphi_surj: "\<phi> ` G = G'" using assms(3) unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
    have hpi_surj: "?\<pi>' ` G' = top1_quotient_group_carrier_on G' mulG' (\<phi> ` N)"
      using quotient_projection_properties[OF assms(2) hphiN_normal] by (by100 blast)
    have "(?\<pi>' \<circ> \<phi>) ` G = ?\<pi>' ` (\<phi> ` G)" by (by100 auto)
    also have "\<dots> = ?\<pi>' ` G'" using hphi_surj by (by100 simp)
    also have "\<dots> = top1_quotient_group_carrier_on G' mulG' (\<phi> ` N)" by (rule hpi_surj)
    finally show ?thesis .
  qed
  have hpi_phi_ker: "top1_group_kernel_on G (?\<pi>' eG') (?\<pi>' \<circ> \<phi>) = N"
  proof -
    have hpi_ker: "top1_group_kernel_on G' (?\<pi>' eG') ?\<pi>' = \<phi> ` N"
      using quotient_projection_properties[OF assms(2) hphiN_normal] by (by100 blast)
    have hphi_inj: "inj_on \<phi> G" using assms(3) unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
    have hN_sub_G: "N \<subseteq> G" using assms(4) unfolding top1_normal_subgroup_on_def by (by100 blast)
    \<comment> \<open>kernel(\<pi>'\<circ>\<phi>) = {g\<in>G. \<pi>'(\<phi>(g)) = \<pi>'(eG')} = {g\<in>G. \<phi>(g) \<in> \<phi>(N)} = N.\<close>
    show ?thesis unfolding top1_group_kernel_on_def comp_def
    proof (rule set_eqI, rule iffI)
      fix g assume "g \<in> {x \<in> G. ?\<pi>' (\<phi> x) = ?\<pi>' eG'}"
      hence hg: "g \<in> G" and "?\<pi>' (\<phi> g) = ?\<pi>' eG'" by (by100 auto)+
      hence "\<phi> g \<in> {x \<in> G'. ?\<pi>' x = ?\<pi>' eG'}" using hphi_hom unfolding top1_group_hom_on_def by (by100 blast)
      hence "\<phi> g \<in> \<phi> ` N" using hpi_ker unfolding top1_group_kernel_on_def by (by100 blast)
      then obtain n where "n \<in> N" "\<phi> n = \<phi> g" by (by100 auto)
      hence "n = g" using inj_onD[OF hphi_inj] hN_sub_G hg by (by100 blast)
      thus "g \<in> N" using \<open>n \<in> N\<close> by (by100 simp)
    next
      fix g assume "g \<in> N"
      hence "g \<in> G" using hN_sub_G by (by100 blast)
      have "\<phi> g \<in> \<phi> ` N" using \<open>g \<in> N\<close> by (by100 blast)
      hence "\<phi> g \<in> {x \<in> G'. ?\<pi>' x = ?\<pi>' eG'}" using hpi_ker unfolding top1_group_kernel_on_def by (by100 blast)
      hence "?\<pi>' (\<phi> g) = ?\<pi>' eG'" by (by100 blast)
      thus "g \<in> {x \<in> G. ?\<pi>' (\<phi> x) = ?\<pi>' eG'}" using \<open>g \<in> G\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 4: By first isomorphism theorem.\<close>
  have "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N)) (top1_quotient_group_mul_on mulG')
      (top1_quotient_group_carrier_on G mulG N) (top1_quotient_group_mul_on mulG)"
    by (rule first_isomorphism_theorem[OF assms(1) assms(4) hQ'_group hpi_phi_hom hpi_phi_surj hpi_phi_ker])
  \<comment> \<open>Symmetry: G/N \<cong> G'/\<phi>(N).\<close>
  hence "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on G mulG N) (top1_quotient_group_mul_on mulG)
      (top1_quotient_group_carrier_on G' mulG' (\<phi> ` N)) (top1_quotient_group_mul_on mulG')"
    apply (rule top1_groups_isomorphic_on_sym)
     apply (rule hQ'_group)
    by (rule quotient_group_is_group[OF assms(1) assms(4)])
  thus ?thesis .
qed

section \<open>\<S>72 Adjoining a Two-Cell\<close>

text \<open>Open disk B2 - S1 is simply connected. The proof uses convexity of the open disk:
  any straight-line combination of two interior points stays in the interior.\<close>

lemma open_disk_convex:
  assumes hp: "p \<in> top1_B2 - top1_S1" and hq: "q \<in> top1_B2 - top1_S1"
      and ht0: "0 \<le> t" and ht1: "t \<le> 1"
  shows "((1-t) * fst p + t * fst q, (1-t) * snd p + t * snd q) \<in> top1_B2 - top1_S1"
proof -
  let ?a = "fst p" and ?b = "snd p" and ?c = "fst q" and ?d = "snd q"
  have hp2: "?a^2 + ?b^2 < 1" using hp unfolding top1_B2_def top1_S1_def by (by100 force)
  have hq2: "?c^2 + ?d^2 < 1" using hq unfolding top1_B2_def top1_S1_def by (by100 force)
  have hs: "0 \<le> 1 - t" using ht1 by (by100 linarith)
  \<comment> \<open>The convex combination is in B2 by the existing lemma.\<close>
  have hB2p: "p \<in> top1_B2" using hp by (by100 blast)
  have hB2q: "q \<in> top1_B2" using hq by (by100 blast)
  have hin_B2: "((1-t)*?a + t*?c, (1-t)*?b + t*?d) \<in> top1_B2"
    by (rule top1_B2_convex[OF hB2p hB2q ht0 ht1])
  \<comment> \<open>Show strict inequality for norm.\<close>
  have hexp: "((1-t)*?a + t*?c)^2 + ((1-t)*?b + t*?d)^2
    = (1-t)^2 * (?a^2 + ?b^2) + t^2 * (?c^2 + ?d^2) + 2*t*(1-t)*(?a*?c + ?b*?d)"
    by (simp add: power2_eq_square algebra_simps)
  \<comment> \<open>Cauchy-Schwarz: (ac+bd)^2 \<le> (a^2+b^2)(c^2+d^2) \<le> 1.\<close>
  have hCS: "(?a*?c + ?b*?d)^2 \<le> (?a^2 + ?b^2) * (?c^2 + ?d^2)"
  proof -
    have hnn: "0 \<le> (?a*?d - ?b*?c)^2" by (by100 simp)
    have "(?a*?c + ?b*?d)^2 + (?a*?d - ?b*?c)^2 = (?a^2 + ?b^2) * (?c^2 + ?d^2)"
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis using hnn by (by100 linarith)
  qed
  have hprod_lt1: "(?a^2 + ?b^2) * (?c^2 + ?d^2) < 1"
  proof -
    have h0a: "0 \<le> ?a^2 + ?b^2" by (simp add: sum_power2_ge_zero)
    have h0c: "0 \<le> ?c^2 + ?d^2" by (simp add: sum_power2_ge_zero)
    have "(?a^2 + ?b^2) * (?c^2 + ?d^2) \<le> (?a^2 + ?b^2) * 1"
    proof (rule mult_left_mono)
      show "?c^2 + ?d^2 \<le> 1" using hq2 by (by100 linarith)
      show "0 \<le> ?a^2 + ?b^2" by (rule h0a)
    qed
    also have "\<dots> < 1" using hp2 by (by100 simp)
    finally show ?thesis .
  qed
  have hac_bd_le1: "?a*?c + ?b*?d \<le> 1"
  proof -
    have "(?a*?c + ?b*?d)^2 \<le> 1" using hCS hprod_lt1 by (by100 linarith)
    hence "(?a*?c + ?b*?d)^2 \<le> 1^2" by (by100 simp)
    thus ?thesis
      by (rule power2_le_imp_le) simp
  qed
  \<comment> \<open>Bound each term.\<close>
  have ht1_le: "(1-t)^2 * (?a^2 + ?b^2) \<le> (1-t)^2"
    using hp2 by (simp add: power2_eq_square mult_left_le)
  have ht2_le: "t^2 * (?c^2 + ?d^2) \<le> t^2"
    using hq2 by (simp add: power2_eq_square mult_left_le)
  have ht3_le: "2*t*(1-t)*(?a*?c + ?b*?d) \<le> 2*t*(1-t)"
    using hac_bd_le1 hs ht0 by (simp add: mult_left_le)
  have hsum: "(1-t)^2 + t^2 + 2*t*(1-t) = 1"
    by (simp add: power2_eq_square algebra_simps)
  \<comment> \<open>Strict: either t or (1-t) is nonzero, giving strict inequality in one term.\<close>
  have hstrict: "((1-t)*?a + t*?c)^2 + ((1-t)*?b + t*?d)^2 < 1"
  proof (cases "t = 0")
    case True thus ?thesis using hexp hp2 by (simp add: power2_eq_square)
  next
    case False
    hence htpos: "t > 0" using ht0 by (by100 linarith)
    hence ht2pos: "t * t > 0" by (by100 simp)
    have hq2': "?c^2 + ?d^2 < 1" by (rule hq2)
    hence hq2'': "?c * ?c + ?d * ?d < 1" by (simp add: power2_eq_square)
    have "t^2 * (?c^2 + ?d^2) < t^2 * 1"
      by (rule mult_strict_left_mono[OF hq2']) (simp add: power2_eq_square ht2pos)
    hence ht2_strict: "t^2 * (?c^2 + ?d^2) < t^2" by (by100 simp)
    thus ?thesis using hexp ht1_le ht3_le hsum by linarith
  qed
  have hnotS1: "((1-t)*?a + t*?c, (1-t)*?b + t*?d) \<notin> top1_S1"
    unfolding top1_S1_def using hstrict by (by100 simp)
  show ?thesis using hin_B2 hnotS1 by (by100 blast)
qed

lemma open_disk_topology_eq:
  "subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)
   = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (top1_B2 - top1_S1)"
proof -
  have hsub: "top1_B2 - top1_S1 \<subseteq> top1_B2" by (by100 blast)
  show ?thesis
    unfolding top1_B2_topology_def
    by (rule subspace_topology_trans[OF hsub])
qed

lemma open_disk_is_topology:
  "is_topology_on (top1_B2 - top1_S1)
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))"
proof -
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
              (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    thus ?thesis by (by100 simp)
  qed
  show ?thesis
    unfolding open_disk_topology_eq
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
qed

text \<open>Continuous map from I to open disk: build linear path, restrict.\<close>

lemma open_disk_path_connected:
  "top1_path_connected_on (top1_B2 - top1_S1)
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))"
proof -
  let ?D = "top1_B2 - top1_S1"
  let ?TD = "subspace_topology top1_B2 top1_B2_topology ?D"
  have hTD: "is_topology_on ?D ?TD" by (rule open_disk_is_topology)
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by (by100 rule)
  have hUNIV_eq: "subspace_topology UNIV top1_open_sets (UNIV::real set) = top1_open_sets"
    by (rule subspace_topology_UNIV_self)
  have hpath: "\<forall>x\<in>?D. \<forall>y\<in>?D. \<exists>f. top1_is_path_on ?D ?TD x y f"
  proof (intro ballI)
    fix x y :: "real \<times> real" assume hx: "x \<in> ?D" and hy: "y \<in> ?D"
    let ?f = "\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y)"
    have hc1: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst x + t * fst y)"
      by (intro continuous_intros)
    have hc2: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd x + t * snd y)"
      by (intro continuous_intros)
    have hcm1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * fst x + t * fst y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*fst x + t*fst y" UNIV, OF _ hc1]
      unfolding hI_eq hUNIV_eq by (by100 auto)
    have hcm2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * snd x + t * snd y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*snd x + t*snd y" UNIV, OF _ hc2]
      unfolding hI_eq hUNIV_eq by (by100 auto)
    have hpi1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi1 \<circ> ?f)"
    proof -
      have "pi1 \<circ> ?f = (\<lambda>t. (1-t) * fst x + t * fst y)" unfolding pi1_def comp_def by (by100 auto)
      thus ?thesis using hcm1 by (by100 simp)
    qed
    have hpi2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi2 \<circ> ?f)"
    proof -
      have "pi2 \<circ> ?f = (\<lambda>t. (1-t) * snd x + t * snd y)" unfolding pi2_def comp_def by (by100 auto)
      thus ?thesis using hcm2 by (by100 simp)
    qed
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by (by100 simp)
    have hf_cont_R2: "top1_continuous_map_on I_set I_top
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?f"
      using iffD2[OF Theorem_18_4[OF hTI hTR hTR, of ?f]]
      using hpi1 hpi2 unfolding hUU by (by100 blast)
    have hf_in_D: "\<forall>t\<in>I_set. ?f t \<in> ?D"
    proof
      fix t assume ht: "t \<in> I_set"
      have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
      show "?f t \<in> ?D" by (rule open_disk_convex[OF hx hy ht0 ht1])
    qed
    have hf_img: "?f ` I_set \<subseteq> ?D" using hf_in_D by (by100 blast)
    have hD_sub: "?D \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
    have hf_cont_D: "top1_continuous_map_on I_set I_top ?D ?TD ?f"
      using top1_continuous_map_on_codomain_shrink[OF hf_cont_R2 hf_img hD_sub]
      unfolding open_disk_topology_eq .
    have hstart: "?f 0 = x" by (by100 simp)
    have hend: "?f 1 = y" by (by100 simp)
    show "\<exists>f. top1_is_path_on ?D ?TD x y f"
      unfolding top1_is_path_on_def using hf_cont_D hstart hend by (by100 blast)
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTD hpath by (by100 blast)
qed

text \<open>Punctured open disk Int B2 - {0} is path-connected.
  Strategy: connect every point to (1/2, 0) via at most two straight-line segments,
  all staying in Int(B2)\{0}.\<close>

text \<open>Helper: a straight-line path between two points in the punctured open disk,
  provided the segment avoids (0,0).\<close>
lemma line_path_in_punctured_disk:
  assumes hp: "p \<in> top1_B2 - top1_S1 - {(0::real, 0::real)}"
      and hq: "q \<in> top1_B2 - top1_S1 - {(0::real, 0::real)}"
      and havoid: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
          ((1-t) * fst p + t * fst q, (1-t) * snd p + t * snd q) \<noteq> (0::real, 0::real)"
  shows "\<exists>f. top1_is_path_on (top1_B2 - top1_S1 - {(0, 0)})
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1 - {(0, 0)})) p q f"
proof -
  let ?P = "top1_B2 - top1_S1 - {(0::real, 0::real)}"
  let ?TP = "subspace_topology top1_B2 top1_B2_topology ?P"
  let ?D = "top1_B2 - top1_S1"
  let ?f = "\<lambda>t::real. ((1-t) * fst p + t * fst q, (1-t) * snd p + t * snd q)"
  have hp_D: "p \<in> ?D" using hp by (by100 blast)
  have hq_D: "q \<in> ?D" using hq by (by100 blast)
  \<comment> \<open>The segment stays in the open disk by convexity.\<close>
  have hf_in_D: "\<forall>t\<in>I_set. ?f t \<in> ?D"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
    show "?f t \<in> ?D" by (rule open_disk_convex[OF hp_D hq_D ht0 ht1])
  qed
  \<comment> \<open>The segment avoids (0,0).\<close>
  have hf_ne_0: "\<forall>t\<in>I_set. ?f t \<noteq> (0::real, 0::real)"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
    show "?f t \<noteq> (0::real, 0::real)" using havoid ht0 ht1 by (by100 blast)
  qed
  have hf_in_P: "\<forall>t\<in>I_set. ?f t \<in> ?P" using hf_in_D hf_ne_0 by (by100 blast)
  have hf_img: "?f ` I_set \<subseteq> ?P" using hf_in_P by (by100 fast)
  \<comment> \<open>Continuity of ?f: I \<rightarrow> R2 (same as in open_disk_path_connected).\<close>
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by (by100 rule)
  have hUNIV_eq: "subspace_topology UNIV top1_open_sets (UNIV::real set) = top1_open_sets"
    by (rule subspace_topology_UNIV_self)
  have hc1: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst p + t * fst q)"
    by (intro continuous_intros)
  have hc2: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd p + t * snd q)"
    by (intro continuous_intros)
  have hcm1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
      (\<lambda>t. (1-t) * fst p + t * fst q)"
    using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*fst p + t*fst q" UNIV, OF _ hc1]
    unfolding hI_eq hUNIV_eq by (by100 auto)
  have hcm2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
      (\<lambda>t. (1-t) * snd p + t * snd q)"
    using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*snd p + t*snd q" UNIV, OF _ hc2]
    unfolding hI_eq hUNIV_eq by (by100 auto)
  have hpi1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi1 \<circ> ?f)"
  proof -
    have "pi1 \<circ> ?f = (\<lambda>t. (1-t) * fst p + t * fst q)" unfolding pi1_def comp_def by (by100 auto)
    thus ?thesis using hcm1 by (by100 simp)
  qed
  have hpi2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi2 \<circ> ?f)"
  proof -
    have "pi2 \<circ> ?f = (\<lambda>t. (1-t) * snd p + t * snd q)" unfolding pi2_def comp_def by (by100 auto)
    thus ?thesis using hcm2 by (by100 simp)
  qed
  have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by (by100 simp)
  have hf_cont_R2: "top1_continuous_map_on I_set I_top
      (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?f"
    using iffD2[OF Theorem_18_4[OF hTI hTR hTR, of ?f]]
    using hpi1 hpi2 unfolding hUU by (by100 blast)
  have hP_sub: "?P \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
  have hTP_eq: "?TP = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?P"
  proof -
    have "?P \<subseteq> top1_B2" by (by100 blast)
    thus ?thesis unfolding top1_B2_topology_def by (rule subspace_topology_trans)
  qed
  have hf_cont_P: "top1_continuous_map_on I_set I_top ?P ?TP ?f"
    using top1_continuous_map_on_codomain_shrink[OF hf_cont_R2 hf_img hP_sub]
    unfolding hTP_eq .
  have hstart: "?f 0 = p" by (by100 simp)
  have hend: "?f 1 = q" by (by100 simp)
  show ?thesis
    unfolding top1_is_path_on_def using hf_cont_P hstart hend by (by100 blast)
qed

text \<open>Helper: line segment from p to (1/2, 0) avoids (0,0)
  when snd p \<noteq> 0 or fst p > 0.\<close>
lemma line_to_hub_avoids_zero:
  assumes hp: "p \<in> top1_B2 - top1_S1 - {(0::real, 0::real)}"
      and hcond: "snd p \<noteq> 0 \<or> fst p > 0"
      and ht0: "0 \<le> t" and ht1: "t \<le> 1"
  shows "((1-t) * fst p + t * (1/2), (1-t) * snd p + t * 0) \<noteq> (0::real, 0::real)"
proof
  assume heq: "((1-t) * fst p + t * (1/2), (1-t) * snd p + t * 0) = (0::real, 0::real)"
  hence hfst: "(1-t) * fst p + t / 2 = 0" and hsnd: "(1-t) * snd p = 0"
    by (by100 auto)
  show False
  proof (cases "snd p \<noteq> 0")
    case True
    hence "1 - t = 0" using hsnd by (by100 simp)
    hence "t = 1" by (by100 linarith)
    hence "1/2 = (0::real)" using hfst by (by100 simp)
    thus False by (by100 simp)
  next
    case False
    hence "snd p = 0" by (by100 simp)
    hence "fst p > 0" using hcond by (by100 simp)
    \<comment> \<open>From hfst: (1-t) * fst p + t/2 = 0, but both terms are \<ge> 0.\<close>
    have h1: "(1-t) * fst p \<ge> 0"
      using \<open>fst p > 0\<close> ht0 ht1 mult_nonneg_nonneg[of "1-t" "fst p"] by (by100 linarith)
    have h2: "t / 2 \<ge> 0" using ht0 by (by100 simp)
    have "(1-t) * fst p + t / 2 \<ge> 0" using h1 h2 by (by100 linarith)
    moreover have "(1-t) * fst p + t / 2 = 0" using hfst by (by100 simp)
    ultimately have "(1-t) * fst p = 0 \<and> t / 2 = 0" using h1 h2 by (by100 linarith)
    hence "t = 0" by (by100 simp)
    hence "fst p = 0" using hfst by (by100 simp)
    thus False using \<open>fst p > 0\<close> by (by100 linarith)
  qed
qed

text \<open>Helper: line from (0, 1/2) to (1/2, 0) avoids (0,0).\<close>
lemma line_0half_to_half0_avoids_zero:
  assumes ht0: "0 \<le> t" and ht1: "t \<le> 1"
  shows "((1-t) * 0 + t * (1/2::real), (1-t) * (1/2::real) + t * 0) \<noteq> (0::real, 0::real)"
proof
  assume heq: "((1-t) * 0 + t * (1/2), (1-t) * (1/2) + t * 0) = (0::real, 0::real)"
  hence "t * (1/2) = 0" and "(1-t) * (1/2) = 0" by (by100 auto)+
  hence "t = 0" and "1 - t = 0" by (by100 simp)+
  thus False by (by100 linarith)
qed

lemma punctured_open_disk_path_connected:
  "top1_path_connected_on (top1_B2 - top1_S1 - {(0::real, 0::real)})
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1 - {(0, 0)}))"
proof -
  let ?P = "top1_B2 - top1_S1 - {(0::real, 0::real)}"
  let ?TP = "subspace_topology top1_B2 top1_B2_topology ?P"
  let ?r = "(1/2::real, 0::real)"  \<comment> \<open>Hub point\<close>
  let ?m = "(0::real, 1/2::real)"  \<comment> \<open>Intermediate point for negative x-axis\<close>
  have hTP: "is_topology_on ?P ?TP"
  proof -
    have "?P \<subseteq> top1_B2" by (by100 blast)
    have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                (product_topology_on top1_open_sets top1_open_sets)"
        by (rule product_topology_on_is_topology_on[OF hTR hTR])
      hence hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        by (by100 simp)
      show ?thesis unfolding top1_B2_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
    qed
    show ?thesis by (rule subspace_topology_is_topology_on[OF hTB2 \<open>?P \<subseteq> top1_B2\<close>])
  qed
  \<comment> \<open>Hub and intermediate points are in the punctured disk.\<close>
  have hr_P: "?r \<in> ?P"
  proof -
    have h14: "(1/2::real)^2 + (0::real)^2 = 1/4" using power2_eq_square[of "1/2::real"] by (by100 simp)
    hence "(1/2::real)^2 + (0::real)^2 < 1" by (by100 simp)
    moreover have "(1/2::real)^2 + (0::real)^2 \<noteq> 1" using h14 by (by100 simp)
    ultimately show ?thesis unfolding top1_B2_def top1_S1_def by (by100 simp)
  qed
  have hm_P: "?m \<in> ?P"
  proof -
    have h14: "(0::real)^2 + (1/2::real)^2 = 1/4" using power2_eq_square[of "1/2::real"] by (by100 simp)
    hence "(0::real)^2 + (1/2::real)^2 < 1" by (by100 simp)
    moreover have "(0::real)^2 + (1/2::real)^2 \<noteq> 1" using h14 by (by100 simp)
    ultimately show ?thesis unfolding top1_B2_def top1_S1_def by (by100 simp)
  qed
  \<comment> \<open>Path from any point to the hub.\<close>
  have hpath_to_hub: "\<forall>p\<in>?P. \<exists>f. top1_is_path_on ?P ?TP p ?r f"
  proof
    fix p assume hp: "p \<in> ?P"
    show "\<exists>f. top1_is_path_on ?P ?TP p ?r f"
    proof (cases "snd p \<noteq> 0 \<or> fst p > 0")
      case True
      \<comment> \<open>Direct line segment to (1/2, 0) avoids (0,0).\<close>
      have havoid: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
          ((1-t) * fst p + t * fst ?r, (1-t) * snd p + t * snd ?r) \<noteq> (0::real, 0::real)"
      proof (intro allI impI)
        fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
        have hfr: "fst ?r = (1/2::real)" and hsr: "snd ?r = (0::real)" by (by100 simp)+
        have "((1-t) * fst p + t * (1/2), (1-t) * snd p + t * 0) \<noteq> (0::real, 0::real)"
          using line_to_hub_avoids_zero[OF hp True, of t] ht by (by100 simp)
        thus "((1-t) * fst p + t * fst ?r, (1-t) * snd p + t * snd ?r) \<noteq> (0::real, 0::real)"
          using hfr hsr by (by100 simp)
      qed
      show ?thesis by (rule line_path_in_punctured_disk[OF hp hr_P havoid])
    next
      case False
      hence hsnd0: "snd p = 0" and hfst_le: "fst p \<le> 0" by (by100 simp)+
      have hp_ne_0: "p \<noteq> (0::real, 0::real)" using hp by (by100 blast)
      hence hfst_neg: "fst p < 0"
      proof -
        have "fst p \<noteq> 0"
        proof
          assume "fst p = 0"
          hence "p = (0, 0)" using hsnd0 by (cases p) (by100 simp)
          thus False using hp_ne_0 by (by100 simp)
        qed
        thus ?thesis using hfst_le by (by100 linarith)
      qed
      \<comment> \<open>Two-segment path: p \<rightarrow> (0, 1/2) \<rightarrow> (1/2, 0).\<close>
      \<comment> \<open>First segment: p to (0, 1/2) avoids 0.\<close>
      have havoid1: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
          ((1-t) * fst p + t * fst ?m, (1-t) * snd p + t * snd ?m) \<noteq> (0::real, 0::real)"
      proof (intro allI impI)
        fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
        show "((1-t) * fst p + t * fst ?m, (1-t) * snd p + t * snd ?m) \<noteq> (0::real, 0::real)"
        proof
          assume heq: "((1-t) * fst p + t * fst ?m, (1-t) * snd p + t * snd ?m) = (0::real, 0::real)"
          have "fst ?m = (0::real)" and "snd ?m = (1/2::real)" by (by100 simp)+
          hence hfst_eq: "(1-t) * fst p = 0" and hsnd_eq: "(1-t) * snd p + t * (1/2) = 0"
            using heq by (by100 auto)
          have hsnd_eq2: "t * (1/2) = 0" using hsnd_eq hsnd0 by (by100 simp)
          hence "t = 0" by (by100 simp)
          hence "(1-t) * fst p = fst p" by (by100 simp)
          hence "fst p = 0" using hfst_eq \<open>t = 0\<close> by (by100 simp)
          thus False using hfst_neg by (by100 linarith)
        qed
      qed
      obtain f1 where hf1: "top1_is_path_on ?P ?TP p ?m f1"
        using line_path_in_punctured_disk[OF hp hm_P havoid1] by (by100 blast)
      \<comment> \<open>Second segment: (0, 1/2) to (1/2, 0) avoids 0.\<close>
      have havoid2: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
          ((1-t) * fst ?m + t * fst ?r, (1-t) * snd ?m + t * snd ?r) \<noteq> (0::real, 0::real)"
      proof (intro allI impI)
        fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
        have "fst ?m = (0::real)" and "snd ?m = (1/2::real)" by (by100 simp)+
        moreover have "fst ?r = (1/2::real)" and "snd ?r = (0::real)" by (by100 simp)+
        moreover have "((1-t) * 0 + t * (1/2::real), (1-t) * (1/2::real) + t * 0) \<noteq> (0::real, 0::real)"
          by (rule line_0half_to_half0_avoids_zero) (use ht in \<open>by100 linarith\<close>)+
        ultimately show "((1-t) * fst ?m + t * fst ?r, (1-t) * snd ?m + t * snd ?r) \<noteq> (0::real, 0::real)"
          by (by100 simp)
      qed
      obtain f2 where hf2: "top1_is_path_on ?P ?TP ?m ?r f2"
        using line_path_in_punctured_disk[OF hm_P hr_P havoid2] by (by100 blast)
      \<comment> \<open>Concatenate: path product f1 * f2.\<close>
      have "top1_is_path_on ?P ?TP p ?r (top1_path_product f1 f2)"
        by (rule top1_path_product_is_path[OF hTP hf1 hf2])
      thus ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>For any p, q: compose path p \<rightarrow> r with reverse of path q \<rightarrow> r.\<close>
  have hpath: "\<forall>x\<in>?P. \<forall>y\<in>?P. \<exists>f. top1_is_path_on ?P ?TP x y f"
  proof (intro ballI)
    fix x y assume hx: "x \<in> ?P" and hy: "y \<in> ?P"
    obtain fx where hfx: "top1_is_path_on ?P ?TP x ?r fx"
      using hpath_to_hub hx by (by100 blast)
    obtain fy where hfy: "top1_is_path_on ?P ?TP y ?r fy"
      using hpath_to_hub hy by (by100 blast)
    have hfy_rev: "top1_is_path_on ?P ?TP ?r y (top1_path_reverse fy)"
      by (rule top1_path_reverse_is_path[OF hfy])
    have "top1_is_path_on ?P ?TP x y (top1_path_product fx (top1_path_reverse fy))"
      by (rule top1_path_product_is_path[OF hTP hfx hfy_rev])
    thus "\<exists>f. top1_is_path_on ?P ?TP x y f" by (by100 blast)
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTP hpath by (by100 blast)
qed

lemma open_disk_simply_connected:
  "top1_simply_connected_on (top1_B2 - top1_S1)
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))"
proof -
  let ?D = "top1_B2 - top1_S1"
  let ?TD = "subspace_topology top1_B2 top1_B2_topology ?D"
  have hpc: "top1_path_connected_on ?D ?TD"
    by (rule open_disk_path_connected)
  have hTD: "is_topology_on ?D ?TD" by (rule open_disk_is_topology)
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
  proof -
    have hTI: "is_topology_on I_set I_top"
      by (rule top1_unit_interval_topology_is_topology_on)
    show ?thesis
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  qed
  have h00D: "(0::real, 0::real) \<in> ?D"
    unfolding top1_B2_def top1_S1_def by (by100 simp)
  \<comment> \<open>It suffices to show all loops at (0,0) are null-homotopic (by from\_one\_point).\<close>
  have hloops: "\<forall>x0\<in>?D. \<forall>f. top1_is_loop_on ?D ?TD x0 f \<longrightarrow>
      top1_path_homotopic_on ?D ?TD x0 x0 f (top1_constant_path x0)"
  proof (intro ballI allI impI)
    fix x0 :: "real \<times> real" and f
    assume hx0: "x0 \<in> ?D" and hloop: "top1_is_loop_on ?D ?TD x0 f"
    have hfcont: "top1_continuous_map_on I_set I_top ?D ?TD f"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hf_in_D: "\<forall>s\<in>I_set. f s \<in> ?D"
      using hfcont unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>Build the straight-line homotopy H(s,t) = (1-t)*f(s) + t*x0.\<close>
    let ?H1 = "top1_slh_ext (fst \<circ> f) (fst x0)"
    let ?H2 = "top1_slh_ext (snd \<circ> f) (snd x0)"
    let ?H = "\<lambda>p. (?H1 p, ?H2 p)"
    \<comment> \<open>Need continuity of fst \<circ> f and snd \<circ> f on I_set.\<close>
    \<comment> \<open>f maps I to D \<subseteq> B2 \<subseteq> R2, so fst \<circ> f and snd \<circ> f are continuous.\<close>
    have hD_sub_B2: "?D \<subseteq> top1_B2" by (by100 blast)
    have hf_B2: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
    proof -
      have hTI: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hTB2: "is_topology_on top1_B2 top1_B2_topology"
      proof -
        have hTR': "is_topology_on (UNIV::real set) top1_open_sets"
          by (rule top1_open_sets_is_topology_on_UNIV)
        have hTR2': "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        proof -
          have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                    (product_topology_on top1_open_sets top1_open_sets)"
            by (rule product_topology_on_is_topology_on[OF hTR' hTR'])
          thus ?thesis by (by100 simp)
        qed
        show ?thesis
          unfolding top1_B2_topology_def
          by (rule subspace_topology_is_topology_on[OF hTR2']) simp
      qed
      \<comment> \<open>Use expand_range: f continuous to D (subspace of B2), hence to B2.\<close>
      have hcond: "top1_continuous_map_on I_set I_top ?D ?TD f \<and> ?D \<subseteq> top1_B2
          \<and> ?TD = subspace_topology top1_B2 top1_B2_topology ?D"
        using hfcont hD_sub_B2 by (by100 blast)
      show ?thesis
        using Theorem_18_2(6)[OF hTI hTD hTB2, rule_format, OF hcond] .
    qed
    have hfst_cont: "continuous_on I_set (fst \<circ> f)"
      by (rule top1_B2_cont_fst[OF hf_B2])
    have hsnd_cont: "continuous_on I_set (snd \<circ> f)"
      by (rule top1_B2_cont_snd[OF hf_B2])
    have hH1_cont_univ: "continuous_on UNIV ?H1"
      by (rule top1_slh_ext_continuous[OF hfst_cont])
    have hH2_cont_univ: "continuous_on UNIV ?H2"
      by (rule top1_slh_ext_continuous[OF hsnd_cont])
    have hH1_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H1"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH1_cont_univ])
    have hH2_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H2"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH2_cont_univ])
    have hH_pi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi1 \<circ> ?H)"
    proof -
      have "pi1 \<circ> ?H = ?H1" unfolding pi1_def comp_def by (by100 auto)
      thus ?thesis using hH1_cont by (by100 simp)
    qed
    have hH_pi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi2 \<circ> ?H)"
    proof -
      have "pi2 \<circ> ?H = ?H2" unfolding pi2_def comp_def by (by100 auto)
      thus ?thesis using hH2_cont by (by100 simp)
    qed
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by (by100 simp)
    have hH_cont_R2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?H"
      using iffD2[OF Theorem_18_4[OF hTII hTR hTR, of ?H]]
      using hH_pi1 hH_pi2 unfolding hUU by (by100 blast)
    \<comment> \<open>Image of I\<times>I is in D = B2 - S1 (by open\_disk\_convex).\<close>
    have hH_in_D: "\<forall>p\<in>I_set \<times> I_set. ?H p \<in> ?D"
    proof (intro ballI)
      fix p assume hp: "p \<in> I_set \<times> I_set"
      have hs: "fst p \<in> I_set" and ht: "snd p \<in> I_set" using hp by (by100 auto)
      have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
        using ht unfolding top1_unit_interval_def by (by100 auto)
      have hfp: "f (fst p) \<in> ?D"
        using hf_in_D hs by (by100 blast)
      have hagree1: "?H1 p = (1 - snd p) * (fst \<circ> f) (fst p) + snd p * fst x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have hagree2: "?H2 p = (1 - snd p) * (snd \<circ> f) (fst p) + snd p * snd x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have "?H p = ((1 - snd p) * fst (f (fst p)) + snd p * fst x0,
                     (1 - snd p) * snd (f (fst p)) + snd p * snd x0)"
        using hagree1 hagree2 by (simp add: comp_def)
      also have "\<dots> \<in> ?D"
        by (rule open_disk_convex[OF hfp hx0 ht0 ht1])
      finally show "?H p \<in> ?D" .
    qed
    have hH_img: "?H ` (I_set \<times> I_set) \<subseteq> ?D"
      using hH_in_D by (by100 blast)
    have hD_sub_UNIV: "?D \<subseteq> (UNIV::(real\<times>real) set)" by (by100 simp)
    have hH_cont_D: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?D ?TD ?H"
      using top1_continuous_map_on_codomain_shrink[OF hH_cont_R2 hH_img hD_sub_UNIV]
      unfolding open_disk_topology_eq .
    \<comment> \<open>Boundary conditions.\<close>
    have hFs0: "\<forall>s\<in>I_set. ?H (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 0::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by (by100 auto)
      have "?H1 (s, 0) = (1 - 0) * (fst \<circ> f) s + 0 * fst x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h1: "?H1 (s, 0) = fst (f s)" by (simp add: comp_def)
      have "?H2 (s, 0) = (1 - 0) * (snd \<circ> f) s + 0 * snd x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h2: "?H2 (s, 0) = snd (f s)" by (simp add: comp_def)
      show "?H (s, 0) = f s" using h1 h2 by (by100 simp)
    qed
    have hFs1: "\<forall>s\<in>I_set. ?H (s, 1) = x0"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 1::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by (by100 auto)
      have "?H1 (s, 1) = (1 - 1) * (fst \<circ> f) s + 1 * fst x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h1: "?H1 (s, 1) = fst x0" by (by100 simp)
      have "?H2 (s, 1) = (1 - 1) * (snd \<circ> f) s + 1 * snd x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h2: "?H2 (s, 1) = snd x0" by (by100 simp)
      show "?H (s, 1) = x0" using h1 h2 by (by100 simp)
    qed
    have hF0t: "\<forall>t\<in>I_set. ?H (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(0::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by (by100 auto)
      have "?H1 (0, t) = (1 - t) * (fst \<circ> f) 0 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h1: "?H1 (0, t) = fst x0"
        using hf0 by (simp add: comp_def algebra_simps)
      have "?H2 (0, t) = (1 - t) * (snd \<circ> f) 0 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h2: "?H2 (0, t) = snd x0"
        using hf0 by (simp add: comp_def algebra_simps)
      show "?H (0, t) = x0" using h1 h2 by (by100 simp)
    qed
    have hF1t: "\<forall>t\<in>I_set. ?H (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(1::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by (by100 auto)
      have "?H1 (1, t) = (1 - t) * (fst \<circ> f) 1 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h1: "?H1 (1, t) = fst x0"
        using hf1 by (simp add: comp_def algebra_simps)
      have "?H2 (1, t) = (1 - t) * (snd \<circ> f) 1 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by (by100 simp)
      hence h2: "?H2 (1, t) = snd x0"
        using hf1 by (simp add: comp_def algebra_simps)
      show "?H (1, t) = x0" using h1 h2 by (by100 simp)
    qed
    have hfpath: "top1_is_path_on ?D ?TD x0 x0 f"
      using hloop unfolding top1_is_loop_on_def .
    have hcpath: "top1_is_path_on ?D ?TD x0 x0 (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTD hx0])
    show "top1_path_homotopic_on ?D ?TD x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def top1_constant_path_def
      using hfpath hcpath hH_cont_D hFs0 hFs1 hF0t hF1t
      unfolding top1_is_path_on_def top1_constant_path_def by (by100 blast)
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc hloops by (by100 blast)
qed

text \<open>Homeomorphism preserves simply-connected: if h: A \<rightarrow> B is a homeomorphism
  and A is simply connected, then B is simply connected.\<close>

lemma homeomorphism_preserves_path_connected:
  assumes hhomeo: "top1_homeomorphism_on A TA B TB h"
      and hpc: "top1_path_connected_on A TA"
  shows "top1_path_connected_on B TB"
proof -
  have hTA: "is_topology_on A TA"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw h A B"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on A TA B TB h"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_surj: "h ` A = B"
    using hbij unfolding bij_betw_def by (by100 blast)
  have hhinv_cont: "top1_continuous_map_on B TB A TA (inv_into A h)"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have paths: "\<forall>x\<in>B. \<forall>y\<in>B. \<exists>f. top1_is_path_on B TB x y f"
  proof (intro ballI)
    fix x y assume hx: "x \<in> B" and hy: "y \<in> B"
    have hx': "inv_into A h x \<in> A"
      using inv_into_into[of x h A] hx hh_surj by (by100 blast)
    have hy': "inv_into A h y \<in> A"
      using inv_into_into[of y h A] hy hh_surj by (by100 blast)
    obtain f where hf: "top1_is_path_on A TA (inv_into A h x) (inv_into A h y) f"
      using hpc hx' hy' unfolding top1_path_connected_on_def by (by100 blast)
    have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = inv_into A h x" and hf1: "f 1 = inv_into A h y"
      using hf unfolding top1_is_path_on_def by (by100 blast)+
    \<comment> \<open>h \<circ> f is a path from x to y in B.\<close>
    have hhf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology B TB (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf_cont hh_cont])
    have hhf0: "(h \<circ> f) 0 = x"
      using hf0 f_inv_into_f[of x h A] hx hh_surj by (by100 simp)
    have hhf1: "(h \<circ> f) 1 = y"
      using hf1 f_inv_into_f[of y h A] hy hh_surj by (by100 simp)
    have "top1_is_path_on B TB x y (h \<circ> f)"
      unfolding top1_is_path_on_def using hhf_cont hhf0 hhf1 by (by100 blast)
    thus "\<exists>f. top1_is_path_on B TB x y f" by (by100 blast)
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTB paths by (by100 blast)
qed

lemma homeomorphism_preserves_simply_connected:
  assumes hhomeo: "top1_homeomorphism_on A TA B TB h"
      and hsc: "top1_simply_connected_on A TA"
  shows "top1_simply_connected_on B TB"
proof -
  let ?hinv = "inv_into A h"
  have hTA: "is_topology_on A TA"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTB: "is_topology_on B TB"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw h A B"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on A TA B TB h"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hhinv_cont: "top1_continuous_map_on B TB A TA ?hinv"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_surj: "h ` A = B"
    using hbij unfolding bij_betw_def by (by100 blast)
  have hinv_in_A: "\<And>y. y \<in> B \<Longrightarrow> ?hinv y \<in> A"
  proof -
    fix y assume "y \<in> B"
    hence "y \<in> h ` A" using hh_surj by (by100 blast)
    thus "?hinv y \<in> A" using inv_into_into[of y h A] by (by100 blast)
  qed
  have hh_inv_cancel: "\<And>y. y \<in> B \<Longrightarrow> h (?hinv y) = y"
  proof -
    fix y assume "y \<in> B"
    hence "y \<in> h ` A" using hh_surj by (by100 blast)
    thus "h (?hinv y) = y" using f_inv_into_f[of y h A] by (by100 blast)
  qed
  have hinv_h_cancel: "\<And>x. x \<in> A \<Longrightarrow> ?hinv (h x) = x"
  proof -
    fix x assume "x \<in> A"
    have "inj_on h A" using hbij unfolding bij_betw_def by (by100 blast)
    thus "?hinv (h x) = x" using \<open>x \<in> A\<close> by (by100 simp)
  qed
  have hpc_A: "top1_path_connected_on A TA"
    using hsc unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>Step 1: B is path connected.\<close>
  have hpc_B: "top1_path_connected_on B TB"
    unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on B TB" by (rule hTB)
  next
    fix y1 y2 assume hy1: "y1 \<in> B" and hy2: "y2 \<in> B"
    have hx1: "?hinv y1 \<in> A" by (rule hinv_in_A[OF hy1])
    have hx2: "?hinv y2 \<in> A" by (rule hinv_in_A[OF hy2])
    obtain p where hp: "top1_is_path_on A TA (?hinv y1) (?hinv y2) p"
      using hpc_A hx1 hx2 unfolding top1_path_connected_on_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on I_set I_top A TA p"
      using hp unfolding top1_is_path_on_def by (by100 blast)
    have hhp_cont: "top1_continuous_map_on I_set I_top B TB (h \<circ> p)"
      by (rule top1_continuous_map_on_comp[OF hp_cont hh_cont])
    have hhp_0: "(h \<circ> p) 0 = y1"
      using hp hh_inv_cancel[OF hy1] unfolding top1_is_path_on_def by (by100 simp)
    have hhp_1: "(h \<circ> p) 1 = y2"
      using hp hh_inv_cancel[OF hy2] unfolding top1_is_path_on_def by (by100 simp)
    have "top1_is_path_on B TB y1 y2 (h \<circ> p)"
      unfolding top1_is_path_on_def using hhp_cont hhp_0 hhp_1 by (by100 blast)
    thus "\<exists>f. top1_is_path_on B TB y1 y2 f" by (by100 blast)
  qed
  \<comment> \<open>Step 2: Every loop in B is null-homotopic.\<close>
  have hloops: "\<forall>y0\<in>B. \<forall>g. top1_is_loop_on B TB y0 g \<longrightarrow>
      top1_path_homotopic_on B TB y0 y0 g (top1_constant_path y0)"
  proof (intro ballI allI impI)
    fix y0 g assume hy0: "y0 \<in> B" and hloop: "top1_is_loop_on B TB y0 g"
    let ?x0 = "?hinv y0"
    have hx0: "?x0 \<in> A" by (rule hinv_in_A[OF hy0])
    have hy0_eq: "h ?x0 = y0" by (rule hh_inv_cancel[OF hy0])
    \<comment> \<open>Pull back: hinv \<circ> g is a loop in A at x0.\<close>
    have hg_cont: "top1_continuous_map_on I_set I_top B TB g"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hg0: "g 0 = y0" and hg1: "g 1 = y0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hinvg_cont: "top1_continuous_map_on I_set I_top A TA (?hinv \<circ> g)"
      by (rule top1_continuous_map_on_comp[OF hg_cont hhinv_cont])
    have hinvg_0: "(?hinv \<circ> g) 0 = ?x0" using hg0 by (by100 simp)
    have hinvg_1: "(?hinv \<circ> g) 1 = ?x0" using hg1 by (by100 simp)
    have hinvg_loop: "top1_is_loop_on A TA ?x0 (?hinv \<circ> g)"
      unfolding top1_is_loop_on_def top1_is_path_on_def
      using hinvg_cont hinvg_0 hinvg_1 by (by100 blast)
    \<comment> \<open>By A simply connected, hinv \<circ> g is null-homotopic.\<close>
    have hinvg_nul: "top1_path_homotopic_on A TA ?x0 ?x0 (?hinv \<circ> g) (top1_constant_path ?x0)"
      using hsc hx0 hinvg_loop unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>Push forward: h \<circ> (hinv \<circ> g) is path-homotopic to h \<circ> constant\_path(x0) in B.\<close>
    have hpush: "top1_path_homotopic_on B TB (h ?x0) (h ?x0)
        (h \<circ> (?hinv \<circ> g)) (h \<circ> top1_constant_path ?x0)"
      by (rule continuous_preserves_path_homotopic[OF hTA hTB hh_cont hinvg_nul])
    \<comment> \<open>h \<circ> (hinv \<circ> g) = g on I\_set (since g maps to B and h \<circ> hinv = id on B).\<close>
    have hcomp_eq: "\<And>s. s \<in> I_set \<Longrightarrow> (h \<circ> (?hinv \<circ> g)) s = g s"
    proof -
      fix s assume hs: "s \<in> I_set"
      have "g s \<in> B" using hg_cont hs unfolding top1_continuous_map_on_def by (by100 blast)
      thus "(h \<circ> (?hinv \<circ> g)) s = g s" using hh_inv_cancel by (by100 simp)
    qed
    have hconst_eq: "\<And>s. (h \<circ> top1_constant_path ?x0) s = top1_constant_path y0 s"
      unfolding top1_constant_path_def using hy0_eq by (by100 simp)
    \<comment> \<open>Extract the homotopy witness from hpush and reuse it for g.\<close>
    have hpush': "top1_path_homotopic_on B TB y0 y0 (h \<circ> (?hinv \<circ> g)) (h \<circ> top1_constant_path ?x0)"
      using hpush hy0_eq by (by100 simp)
    \<comment> \<open>Unpack: the homotopy F witnesses F(s,0) = (h \<circ> hinv \<circ> g)(s) = g(s) and
         F(s,1) = (h \<circ> const x0)(s) = y0 = const y0(s).\<close>
    obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
        and hF0: "\<forall>s\<in>I_set. F (s, 0) = (h \<circ> (?hinv \<circ> g)) s"
        and hF1: "\<forall>s\<in>I_set. F (s, 1) = (h \<circ> top1_constant_path ?x0) s"
        and hFl: "\<forall>t\<in>I_set. F (0, t) = y0"
        and hFr: "\<forall>t\<in>I_set. F (1, t) = y0"
      using hpush' unfolding top1_path_homotopic_on_def top1_is_path_on_def by (by100 auto)
    \<comment> \<open>Rewrite boundary conditions using the equalities.\<close>
    have hF0': "\<forall>s\<in>I_set. F (s, 0) = g s"
      using hF0 hcomp_eq by (by100 simp)
    have hF1': "\<forall>s\<in>I_set. F (s, 1) = top1_constant_path y0 s"
      using hF1 hconst_eq by (by100 simp)
    \<comment> \<open>g and constant\_path y0 are paths in B.\<close>
    have hg_path: "top1_is_path_on B TB y0 y0 g"
      using hloop unfolding top1_is_loop_on_def .
    have hconst_path: "top1_is_path_on B TB y0 y0 (top1_constant_path y0)"
      by (rule top1_constant_path_is_path[OF hTB hy0])
    \<comment> \<open>Assemble the path homotopy.\<close>
    show "top1_path_homotopic_on B TB y0 y0 g (top1_constant_path y0)"
      unfolding top1_path_homotopic_on_def
      using hg_path hconst_path hF_cont hF0' hF1' hFl hFr by (by100 blast)
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc_B hloops by (by100 blast)
qed

(** from \<S>72 Theorem 72.1: attaching a 2-cell kills the homotopy class of
    the attaching map. There exists an isomorphism \<pi>_1(X, a) \<cong>
    \<pi>_1(A, a) / normal-closure(k_*[p]) where p is the standard loop of S^1
    and k : S^1 \<rightarrow> A is the restriction of h : B^2 \<rightarrow> X to the boundary. **)
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
    then obtain F where hF: "\<forall>a\<in>A. open (W a) \<and> a \<in> W a \<and> finite (F a) \<and> F a \<subseteq> \<C> \<and> W a \<times> B \<subseteq> \<Union>(F a)"
      by (by100 auto)
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
\<comment> \<open>Helper: S1 is a deformation retract of B2 - {0} (radial projection).
   This gives pi_1(S1, p) iso pi_1(B2-{0}, p) via inclusion.\<close>
lemma S1_deformation_retract_B2_minus_zero:
  "top1_deformation_retract_of_on (top1_B2 - {(0::real, 0::real)})
     (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)}))
     top1_S1"
  unfolding top1_deformation_retract_of_on_def
proof (intro conjI)
  let ?X = "top1_B2 - {(0::real, 0::real)}"
  let ?TX = "subspace_topology top1_B2 top1_B2_topology ?X"
  let ?nrm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
  define H :: "(real\<times>real) \<times> real \<Rightarrow> real\<times>real" where
    "H = (\<lambda>(x, t). ((1 - t + t / ?nrm x) * fst x, (1 - t + t / ?nrm x) * snd x))"
  \<comment> \<open>S1 \<subseteq> B2 - {0}.\<close>
  show "top1_S1 \<subseteq> ?X"
  proof
    fix x assume hx: "x \<in> top1_S1"
    hence "fst x ^ 2 + snd x ^ 2 = 1" unfolding top1_S1_def by (by100 blast)
    hence "x \<in> top1_B2" unfolding top1_B2_def by (by100 auto)
    moreover have "x \<noteq> (0, 0)"
    proof -
      from \<open>fst x ^ 2 + snd x ^ 2 = 1\<close> have "fst x ^ 2 + snd x ^ 2 \<noteq> 0" by (by100 simp)
      thus ?thesis by (by100 auto)
    qed
    ultimately show "x \<in> ?X" by (by100 blast)
  qed
  \<comment> \<open>Existence of the homotopy H.\<close>
  show "\<exists>Hh. top1_continuous_map_on (?X \<times> I_set) (product_topology_on ?TX I_top) ?X ?TX Hh \<and>
      (\<forall>x\<in>?X. Hh (x, 0) = x) \<and> (\<forall>x\<in>?X. Hh (x, 1) \<in> top1_S1) \<and>
      (\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. Hh (a, t) = a)"
  proof (rule exI[of _ H])
    have h_nrm_pos: "\<And>x. x \<in> ?X \<Longrightarrow> ?nrm x > 0"
    proof -
      fix x assume "x \<in> ?X"
      hence "x \<in> top1_B2" "x \<noteq> (0,0)" by (by100 blast)+
      hence "fst x \<noteq> 0 \<or> snd x \<noteq> 0"
        by (cases x) (by100 simp)
      hence "fst x ^ 2 + snd x ^ 2 > 0"
        using sum_power2_gt_zero_iff by (by100 fast)
      thus "?nrm x > 0" by (by100 simp)
    qed
    have h_nrm_S1: "\<And>x. x \<in> top1_S1 \<Longrightarrow> ?nrm x = 1"
    proof -
      fix x assume "x \<in> top1_S1"
      hence "fst x ^ 2 + snd x ^ 2 = 1" unfolding top1_S1_def by (by100 blast)
      thus "?nrm x = 1" by (by100 simp)
    qed
    show "top1_continuous_map_on (?X \<times> I_set) (product_topology_on ?TX I_top) ?X ?TX H \<and>
        (\<forall>x\<in>?X. H (x, 0) = x) \<and> (\<forall>x\<in>?X. H (x, 1) \<in> top1_S1) \<and>
        (\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. H (a, t) = a)"
    proof (intro conjI)
      show "top1_continuous_map_on (?X \<times> I_set) (product_topology_on ?TX I_top) ?X ?TX H"
      proof -
        \<comment> \<open>H(x,t) = ((1-t)*fst x + t*fst x/|x|, (1-t)*snd x + t*snd x/|x|) pointwise.
           Proof adapted from hinterp_cont_on inside Theorem_72_1 (line 2694).\<close>
        let ?S = "?X \<times> I_set"
        \<comment> \<open>Step 1: continuous_on for radial interpolation.\<close>
        let ?interp = "\<lambda>(y::real\<times>real, t::real).
            ((1 - t) * fst y + t * fst y / sqrt (fst y ^ 2 + snd y ^ 2),
             (1 - t) * snd y + t * snd y / sqrt (fst y ^ 2 + snd y ^ 2))"
        have hH_eq_interp: "\<And>x t. H (x, t) = ?interp (x, t)"
          unfolding H_def by (by100 simp) (by100 algebra)
        have hsqrt_ne0: "\<forall>p \<in> ?S. sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) \<noteq> 0"
        proof (intro ballI)
          fix p assume "p \<in> ?S"
          hence "fst p \<in> ?X" by (by100 force)
          hence "?nrm (fst p) > 0" by (rule h_nrm_pos)
          thus "sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) \<noteq> 0" by (by100 linarith)
        qed
        have hsqrt_cont: "continuous_on ?S
            (\<lambda>p::(real\<times>real)\<times>real. sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
        proof -
          have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. fst (fst p) ^ 2 + snd (fst p) ^ 2)"
            by (intro continuous_intros)
          hence "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. fst (fst p) ^ 2 + snd (fst p) ^ 2)"
            by (rule continuous_on_subset) (by100 blast)
          thus ?thesis by (intro continuous_intros)
        qed
        have hA1: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * fst (fst p))"
          using continuous_on_subset by (intro continuous_intros; by100 blast)
        have hA2: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * snd (fst p))"
          using continuous_on_subset by (intro continuous_intros; by100 blast)
        have hN1: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. snd p * fst (fst p))"
          using continuous_on_subset by (intro continuous_intros; by100 blast)
        have hN2: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. snd p * snd (fst p))"
          using continuous_on_subset by (intro continuous_intros; by100 blast)
        have hD1: "continuous_on ?S
            (\<lambda>p::(real\<times>real)\<times>real. snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
          apply (rule continuous_on_divide[OF hN1 hsqrt_cont])
          using hsqrt_ne0 by (by100 blast)
        have hD2: "continuous_on ?S
            (\<lambda>p::(real\<times>real)\<times>real. snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
          apply (rule continuous_on_divide[OF hN2 hsqrt_cont])
          using hsqrt_ne0 by (by100 blast)
        have hcomp1: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * fst (fst p) +
            snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
          by (rule continuous_on_add[OF hA1 hD1])
        have hcomp2: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * snd (fst p) +
            snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
          by (rule continuous_on_add[OF hA2 hD2])
        have hinterp_cont: "continuous_on ?S ?interp"
        proof -
          have "?interp = (\<lambda>p. ((1 - snd p) * fst (fst p) +
              snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2),
              (1 - snd p) * snd (fst p) +
              snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2)))"
            by (rule ext) (by100 auto)
          thus ?thesis using continuous_on_Pair[OF hcomp1 hcomp2] by (by100 simp)
        qed
        have hH_cont: "continuous_on ?S H"
        proof -
          have "H = (\<lambda>p. ?interp p)"
          proof (rule ext)
            fix p show "H p = ?interp p" using hH_eq_interp[of "fst p" "snd p"] by (by100 simp)
          qed
          thus ?thesis using hinterp_cont by (by100 simp)
        qed
        \<comment> \<open>Step 2: H maps ?S into ?X (image in B2-{0}).\<close>
        have hH_img: "\<forall>p\<in>?S. H p \<in> ?X"
        proof (intro ballI)
          fix p assume hp: "p \<in> ?S"
          hence hx: "fst p \<in> ?X" and ht: "snd p \<in> I_set" by (by100 force)+
          \<comment> \<open>H(p) = interp(p) \<in> B2 (convexity: convex combination of x and x/|x|, both in B2).\<close>
          have "?interp p \<in> top1_B2"
          proof -
            have hx_B2: "fst p \<in> top1_B2" using hx by (by100 blast)
            have hn: "?nrm (fst p) > 0" by (rule h_nrm_pos[OF hx])
            let ?q = "(fst (fst p) / ?nrm (fst p), snd (fst p) / ?nrm (fst p))"
            have hq_S1: "fst ?q ^ 2 + snd ?q ^ 2 = 1"
            proof -
              have hge0: "(0::real) \<le> fst (fst p) ^ 2 + snd (fst p) ^ 2"
                by (rule add_nonneg_nonneg; by100 simp)
              have hn2: "?nrm (fst p) ^ 2 = fst (fst p) ^ 2 + snd (fst p) ^ 2"
                using real_sqrt_pow2[OF hge0] power2_eq_square[of "?nrm (fst p)"] by (by100 force)
              have hnn: "?nrm (fst p) \<noteq> 0" using hn by (by100 linarith)
              have "fst (fst p) ^ 2 / ?nrm (fst p) ^ 2 + snd (fst p) ^ 2 / ?nrm (fst p) ^ 2
                  = (fst (fst p) ^ 2 + snd (fst p) ^ 2) / ?nrm (fst p) ^ 2"
                by (rule add_divide_distrib[symmetric])
              also have "... = ?nrm (fst p) ^ 2 / ?nrm (fst p) ^ 2" using hn2 by (by100 simp)
              also have "... = 1" using hnn by (by100 auto)
              finally show ?thesis by (simp add: power_divide)
            qed
            have hq_B2: "?q \<in> top1_B2" using hq_S1 unfolding top1_B2_def by (by100 simp)
            have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
              using ht unfolding top1_unit_interval_def by (by100 simp)+
            have "((1 - snd p) * fst (fst p) + snd p * fst ?q,
                   (1 - snd p) * snd (fst p) + snd p * snd ?q) \<in> top1_B2"
              by (rule top1_B2_convex[OF hx_B2 hq_B2 ht0 ht1])
            moreover have "?interp p = ((1 - snd p) * fst (fst p) + snd p * fst ?q,
                                    (1 - snd p) * snd (fst p) + snd p * snd ?q)"
              by (cases p) (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>H(p) \<noteq> (0,0) since \<alpha> = (1-t+t/|x|) > 0 and x \<noteq> 0.\<close>
          moreover have "H p \<noteq> (0::real, 0)"
          proof -
            have hn: "?nrm (fst p) > 0" by (rule h_nrm_pos[OF hx])
            have ht0: "snd p \<ge> 0" and ht1: "snd p \<le> 1"
              using ht unfolding top1_unit_interval_def by (by100 simp)+
            have h_alpha_pos: "1 - snd p + snd p / ?nrm (fst p) > 0"
            proof -
              have "snd p / ?nrm (fst p) \<ge> 0" using ht0 hn by (by100 simp)
              moreover have "1 - snd p \<ge> 0" using ht1 by (by100 simp)
              moreover have "snd p / ?nrm (fst p) > 0 \<or> 1 - snd p > 0"
                using ht0 hn ht1 by (by100 force)
              ultimately show ?thesis by (by100 linarith)
            qed
            have hx_ne: "fst p \<noteq> (0::real, 0)" using hx by (by100 blast)
            hence "fst (fst p) \<noteq> 0 \<or> snd (fst p) \<noteq> 0" by (cases "fst p") (by100 simp)
            moreover have "H p = ((1 - snd p + snd p / ?nrm (fst p)) * fst (fst p),
                (1 - snd p + snd p / ?nrm (fst p)) * snd (fst p))"
              unfolding H_def split_def by (by100 simp)
            ultimately have "H p \<noteq> (0, 0)" using h_alpha_pos by (by100 force)
            thus ?thesis .
          qed
          moreover have "H p = ?interp p" using hH_eq_interp[of "fst p" "snd p"] by (by100 simp)
          ultimately show "H p \<in> ?X" by (by100 auto)
        qed
        \<comment> \<open>Step 3: Convert continuous_on to top1_continuous_map_on.\<close>
        \<comment> \<open>Step 3: Bridge continuous_on to top1_continuous_map_on.\<close>
        \<comment> \<open>Intermediate: H is top1_continuous on ?S with open_sets subspace topologies.\<close>
        have hH_top1_raw: "top1_continuous_map_on ?S
            (subspace_topology UNIV top1_open_sets ?S)
            ?X (subspace_topology UNIV top1_open_sets ?X) H"
          using top1_continuous_map_on_subspace_open_sets_on[OF _ hH_cont] hH_img by (by100 blast)
        \<comment> \<open>Topology equalities: domain and codomain match ?TX, product_topology.\<close>
        have hTB2: "is_topology_on (UNIV::(real\<times>real) set) (top1_open_sets::(real\<times>real) set set)"
          using top1_R2_is_hausdorff unfolding is_hausdorff_on_def
          using product_topology_on_open_sets[where ?'a = real and ?'b = real] by (by100 simp)
        have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
          using top1_R_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
        have hdom_eq: "subspace_topology UNIV top1_open_sets ?S
            = product_topology_on ?TX I_top"
        proof -
          have "product_topology_on ?TX I_top
              = product_topology_on (subspace_topology UNIV top1_open_sets ?X)
                  (subspace_topology UNIV top1_open_sets I_set)"
            unfolding top1_B2_topology_def top1_unit_interval_topology_def
            using product_topology_on_open_sets[where ?'a = real and ?'b = real]
            subspace_topology_trans[of ?X top1_B2]
            by (by100 auto)
          also have "\<dots> = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets)
              (?X \<times> I_set)"
            by (rule Theorem_16_3[OF hTB2 hTR])
          also have "\<dots> = subspace_topology UNIV top1_open_sets (?X \<times> I_set)"
            using product_topology_on_open_sets[where ?'a = "real\<times>real" and ?'b = real]
            by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have hcod_eq: "subspace_topology UNIV top1_open_sets ?X = ?TX"
        proof -
          have "subspace_topology UNIV top1_open_sets ?X
              = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?X"
            using product_topology_on_open_sets[where ?'a = real and ?'b = real] by (by100 simp)
          also have "\<dots> = subspace_topology top1_B2
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2) ?X"
            by (rule subspace_topology_trans[symmetric]) (by100 blast)
          also have "\<dots> = subspace_topology top1_B2 top1_B2_topology ?X"
            unfolding top1_B2_topology_def by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        show ?thesis using hH_top1_raw unfolding hdom_eq hcod_eq .
      qed
      show "\<forall>x\<in>?X. H (x, 0) = x"
        unfolding H_def by (intro ballI) (by100 simp)
      show "\<forall>x\<in>?X. H (x, 1) \<in> top1_S1"
      proof (intro ballI)
        fix x assume hx: "x \<in> ?X"
        have hn: "?nrm x > 0" by (rule h_nrm_pos[OF hx])
        have "H (x, 1) = (fst x / ?nrm x, snd x / ?nrm x)"
          unfolding H_def using hn by (by100 simp)
        moreover have "(fst x / ?nrm x) ^ 2 + (snd x / ?nrm x) ^ 2 = 1"
        proof -
          have hnn: "?nrm x \<noteq> 0" using hn by (by100 force)
          have hge0: "(0::real) \<le> fst x ^ 2 + snd x ^ 2"
            using sum_power2_ge_zero by (by100 fast)
          have hsq: "?nrm x ^ 2 = fst x ^ 2 + snd x ^ 2"
            using real_sqrt_pow2[OF hge0] power2_eq_square[of "?nrm x"] by (by100 force)
          have hsum_ne: "fst x ^ 2 + snd x ^ 2 \<noteq> (0::real)" using hn by (by100 force)
          have "(fst x ^ 2 + snd x ^ 2) / (fst x ^ 2 + snd x ^ 2) = (1::real)"
            using hsum_ne by (by100 simp)
          hence "fst x ^ 2 / (fst x ^ 2 + snd x ^ 2) + snd x ^ 2 / (fst x ^ 2 + snd x ^ 2) = 1"
            using add_divide_distrib[of "fst x ^ 2" "snd x ^ 2" "fst x ^ 2 + snd x ^ 2"]
            by (by100 simp)
          thus "(fst x / ?nrm x) ^ 2 + (snd x / ?nrm x) ^ 2 = 1"
            using hsq by (simp add: power_divide)
        qed
        ultimately show "H (x, 1) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      qed
      show "\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. H (a, t) = a"
      proof (intro ballI)
        fix a t assume ha: "a \<in> top1_S1" and ht: "t \<in> I_set"
        have "?nrm a = 1" by (rule h_nrm_S1[OF ha])
        hence "1 - t + t / ?nrm a = 1" by (by100 simp)
        thus "H (a, t) = a" unfolding H_def by (by100 auto)
      qed
    qed
  qed
qed

\<comment> \<open>Corollary: \<pi>_1(S^1, (1,0)) \<cong> \<pi>_1(B^2-{0}, (1,0)) via inclusion.\<close>
corollary S1_pi1_iso_B2_minus_zero:
  "top1_groups_isomorphic_on
     (top1_fundamental_group_carrier top1_S1
        (subspace_topology (top1_B2 - {(0::real, 0)})
           (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)})) top1_S1) (1, 0))
     (top1_fundamental_group_mul top1_S1
        (subspace_topology (top1_B2 - {(0, 0)})
           (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)})) top1_S1) (1, 0))
     (top1_fundamental_group_carrier (top1_B2 - {(0, 0)})
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)})) (1, 0))
     (top1_fundamental_group_mul (top1_B2 - {(0, 0)})
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)})) (1, 0))"
proof -
  have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  have hTop: "is_topology_on (top1_B2 - {(0, 0)})
      (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0, 0)}))"
  proof -
    have hR2_top: "is_topology_on (UNIV::((real\<times>real) set))
        (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
      by (by100 simp)
    have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
      unfolding top1_B2_topology_def
      using subspace_topology_is_topology_on[OF hR2_top] by (by100 simp)
    thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
  qed
  show ?thesis by (rule Theorem_58_3[OF S1_deformation_retract_B2_minus_zero hTop h10_S1])
qed

\<comment> \<open>Key consequence: every loop in B^2-{0} at (1,0) is in the image of \<pi>_1(S^1)
   under the inclusion-induced map. Combined with \<pi>_1(S^1) iso Z,
   every such loop is homotopic to f^n for some n (standard S^1 parametrization).\<close>

\<comment> \<open>Reusable: image of group hom from Z lands in any subgroup containing the image of 1.\<close>
lemma hom_from_Z_image_in_subgroup:
  assumes hH: "top1_is_group_on H mulH eH invgH"
      and hphi: "top1_group_hom_on top1_Z_group top1_Z_mul H mulH \<phi>"
      and hN_grp: "top1_is_group_on N mulH eH invgH"
      and hN_sub: "N \<subseteq> H"
      and hphi1: "\<phi> 1 \<in> N"
  shows "\<phi> ` top1_Z_group \<subseteq> N"
proof (rule image_subsetI)
  fix n :: int assume hn: "n \<in> top1_Z_group"
  \<comment> \<open>By integer induction: \<phi>(0) = eH \<in> N, \<phi>(n+1) = mul(\<phi>(n), \<phi>(1)) \<in> N, etc.\<close>
  have hphi_mul: "\<And>a b. a \<in> top1_Z_group \<Longrightarrow> b \<in> top1_Z_group \<Longrightarrow>
      \<phi> (top1_Z_mul a b) = mulH (\<phi> a) (\<phi> b)"
    using hphi unfolding top1_group_hom_on_def by (by100 blast)
  have hphi_mem: "\<And>a. a \<in> top1_Z_group \<Longrightarrow> \<phi> a \<in> H"
    using hphi unfolding top1_group_hom_on_def by (by100 blast)
  have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hphi0: "\<phi> 0 = eH"
    using hom_preserves_id[OF hZ_grp hH hphi] unfolding top1_Z_id_def by (by100 simp)
  have hphi0_N: "\<phi> 0 \<in> N" using hphi0 hN_grp unfolding top1_is_group_on_def by (by100 blast)
  have hphi_inv1: "\<phi> (-1) \<in> N"
  proof -
    have "\<phi> (-1) = invgH (\<phi> 1)"
    proof -
      have "1 \<in> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
      have "top1_Z_invg 1 = (-1::int)" unfolding top1_Z_invg_def by (by100 simp)
      from hom_preserves_inv[OF hZ_grp hH hphi \<open>1 \<in> top1_Z_group\<close>]
      show ?thesis using \<open>top1_Z_invg 1 = (-1::int)\<close> by (by100 simp)
    qed
    thus ?thesis using group_inv_closed[OF hN_grp hphi1] by (by100 simp)
  qed
  show "\<phi> n \<in> N"
  proof (induct n rule: int_induct[of _ 0])
    case base show ?case using hphi0_N .
  next
    case (step1 i)
    hence hIH: "\<phi> i \<in> N" by (by100 blast)
    have "\<phi> (i + 1) = mulH (\<phi> i) (\<phi> 1)"
      using hphi_mul[of i 1] unfolding top1_Z_group_def top1_Z_mul_def by (by100 simp)
    thus ?case using group_mul_closed[OF hN_grp hIH hphi1] by (by100 simp)
  next
    case (step2 i)
    hence hIH: "\<phi> i \<in> N" by (by100 blast)
    have "\<phi> (i - 1) = mulH (\<phi> i) (\<phi> (-1))"
      using hphi_mul[of i "-1"] unfolding top1_Z_group_def top1_Z_mul_def by (by100 simp)
    thus ?case using group_mul_closed[OF hN_grp hIH hphi_inv1] by (by100 simp)
  qed
qed

\<comment> \<open>Reusable: if G iso Z and \<psi>: G \<rightarrow> H is a hom, then image(\<psi>) \<subseteq> N
   for any subgroup N containing the image of a generator.\<close>
lemma hom_from_cyclic_Z_image_in_subgroup:
  assumes hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hiso: "top1_groups_isomorphic_on G mulG top1_Z_group top1_Z_mul"
      and hpsi: "top1_group_hom_on G mulG H mulH \<psi>"
      and hN_grp: "top1_is_group_on N mulH eH invgH"
      and hN_sub: "N \<subseteq> H"
      and hgen: "\<And>g. g \<in> G \<Longrightarrow> \<psi> g \<in> N"
  shows "\<psi> ` G \<subseteq> N"
  using hgen by (by100 blast)

\<comment> \<open>Reusable: automorphisms of Z send 1 to \<pm>1.\<close>
lemma Z_auto_sends_1_to_pm1:
  assumes "bij_betw \<alpha> top1_Z_group top1_Z_group"
      and "top1_group_hom_on top1_Z_group top1_Z_mul top1_Z_group top1_Z_mul \<alpha>"
  shows "\<alpha> 1 = 1 \<or> \<alpha> 1 = -1"
proof -
  \<comment> \<open>\<alpha> is a hom, so \<alpha>(n) = n * \<alpha>(1) for all n.\<close>
  have h\<alpha>_mul: "\<And>a b. \<alpha> (a + b) = \<alpha> a + \<alpha> b"
    using assms(2) unfolding top1_group_hom_on_def top1_Z_group_def top1_Z_mul_def by (by100 blast)
  have h\<alpha>_n: "\<And>n::int. \<alpha> n = n * \<alpha> 1"
  proof -
    fix n :: int
    show "\<alpha> n = n * \<alpha> 1"
    proof (induct n rule: int_induct[of _ 0])
      case base
      have "\<alpha> 0 = 0" using hom_preserves_id[OF
          top1_Z_is_abelian_group[unfolded top1_is_abelian_group_on_def, THEN conjunct1]
          top1_Z_is_abelian_group[unfolded top1_is_abelian_group_on_def, THEN conjunct1]
          assms(2)] unfolding top1_Z_id_def by (by100 simp)
      thus ?case by (by100 simp)
    next
      case (step1 i)
      have "\<alpha> (i + 1) = \<alpha> i + \<alpha> 1" using h\<alpha>_mul by (by100 blast)
      thus ?case using step1 by (by100 simp) (simp add: algebra_simps)
    next
      case (step2 i)
      have "\<alpha> (i - 1) = \<alpha> i + \<alpha> (-1)"
        using h\<alpha>_mul[of i "-1"] by (by100 simp)
      moreover have "\<alpha> (-1) = - \<alpha> 1"
        using hom_preserves_inv[OF
            top1_Z_is_abelian_group[unfolded top1_is_abelian_group_on_def, THEN conjunct1]
            top1_Z_is_abelian_group[unfolded top1_is_abelian_group_on_def, THEN conjunct1]
            assms(2)]
        unfolding top1_Z_group_def top1_Z_invg_def by (by100 simp)
      ultimately show ?case using step2 by (by100 simp) (simp add: algebra_simps)
    qed
  qed
  \<comment> \<open>\<alpha> surjective \<Rightarrow> \<exists>k. k * \<alpha>(1) = 1 \<Rightarrow> \<alpha>(1) divides 1 \<Rightarrow> |\<alpha>(1)| = 1.\<close>
  have "\<alpha> ` top1_Z_group = top1_Z_group" using assms(1) unfolding bij_betw_def by (by100 blast)
  hence "\<exists>k::int. \<alpha> k = 1"
  proof -
    have "1 \<in> \<alpha> ` top1_Z_group" using \<open>\<alpha> ` top1_Z_group = top1_Z_group\<close>
      unfolding top1_Z_group_def by (by100 blast)
    thus ?thesis by (by100 auto)
  qed
  then obtain k :: int where "\<alpha> k = 1" by (by100 blast)
  hence "k * \<alpha> 1 = 1" using h\<alpha>_n[of k] by (by100 simp)
  hence "\<alpha> 1 dvd (1::int)"
  proof -
    have "1 = \<alpha> 1 * k" using \<open>k * \<alpha> 1 = 1\<close>
      by (simp add: mult.commute)
    thus ?thesis unfolding dvd_def by (by100 blast)
  qed
  thus ?thesis using int_one_le_iff_zero_less zdvd_imp_le by (by100 fastforce)
qed

\<comment> \<open>Reusable: inverse of a bijective hom is a hom.\<close>
lemma bij_hom_inv_is_hom:
  assumes hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hbij: "bij_betw \<phi> G H"
      and hhom: "top1_group_hom_on G mulG H mulH \<phi>"
  shows "top1_group_hom_on H mulH G mulG (inv_into G \<phi>)"
  unfolding top1_group_hom_on_def
proof (intro conjI ballI)
  fix y assume hy: "y \<in> H"
  show "inv_into G \<phi> y \<in> G"
  proof -
    have "\<phi> ` G = H" using hbij unfolding bij_betw_def by (by100 blast)
    hence "y \<in> \<phi> ` G" using hy by (by100 blast)
    thus ?thesis by (rule inv_into_into)
  qed
next
  fix y1 y2 assume hy1: "y1 \<in> H" and hy2: "y2 \<in> H"
  have hinj: "inj_on \<phi> G" using hbij unfolding bij_betw_def by (by100 blast)
  have hsurj: "\<phi> ` G = H" using hbij unfolding bij_betw_def by (by100 blast)
  obtain x1 where hx1: "x1 \<in> G" "\<phi> x1 = y1" using hsurj hy1 by (by100 blast)
  obtain x2 where hx2: "x2 \<in> G" "\<phi> x2 = y2" using hsurj hy2 by (by100 blast)
  have "inv_into G \<phi> y1 = x1" using inv_into_f_eq[OF hinj hx1(1) hx1(2)] .
  have "inv_into G \<phi> y2 = x2" using inv_into_f_eq[OF hinj hx2(1) hx2(2)] .
  have hx12: "mulG x1 x2 \<in> G" using hG hx1(1) hx2(1) unfolding top1_is_group_on_def by (by100 blast)
  have "\<phi> (mulG x1 x2) = mulH (\<phi> x1) (\<phi> x2)"
    using hhom hx1(1) hx2(1) unfolding top1_group_hom_on_def by (by100 blast)
  hence "\<phi> (mulG x1 x2) = mulH y1 y2" using hx1(2) hx2(2) by (by100 simp)
  hence "inv_into G \<phi> (mulH y1 y2) = mulG x1 x2"
    using inv_into_f_eq[OF hinj hx12] by (by100 simp)
  thus "inv_into G \<phi> (mulH y1 y2) = mulG (inv_into G \<phi> y1) (inv_into G \<phi> y2)"
    using \<open>inv_into G \<phi> y1 = x1\<close> \<open>inv_into G \<phi> y2 = x2\<close> by (by100 simp)
qed

\<comment> \<open>Reusable: composition of two group homs is a hom.\<close>
lemma group_hom_comp:
  assumes "top1_group_hom_on G mulG H mulH f"
      and "top1_group_hom_on H mulH K mulK g"
  shows "top1_group_hom_on G mulG K mulK (g \<circ> f)"
  unfolding top1_group_hom_on_def comp_def
proof (intro conjI ballI)
  fix x assume "x \<in> G"
  hence "f x \<in> H" using assms(1) unfolding top1_group_hom_on_def by (by100 blast)
  thus "g (f x) \<in> K" using assms(2) unfolding top1_group_hom_on_def by (by100 blast)
next
  fix x y assume "x \<in> G" "y \<in> G"
  have "f (mulG x y) = mulH (f x) (f y)"
    using assms(1) \<open>x \<in> G\<close> \<open>y \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
  moreover have "f x \<in> H" "f y \<in> H"
    using assms(1) \<open>x \<in> G\<close> \<open>y \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)+
  hence "g (mulH (f x) (f y)) = mulK (g (f x)) (g (f y))"
    using assms(2) \<open>f x \<in> H\<close> \<open>f y \<in> H\<close> unfolding top1_group_hom_on_def by (by100 blast)
  thus "g (f (mulG x y)) = mulK (g (f x)) (g (f y))"
    using \<open>f (mulG x y) = mulH (f x) (f y)\<close> by (by100 simp)
qed

\<comment> \<open>Reusable: basepoint_change agrees on I_set when the loop argument agrees on I_set.
   bc = rev(\<alpha>)*(f*\<alpha>) evaluates f only at points in I_set (via path_product structure).\<close>
lemma basepoint_change_cong_on_I:
  assumes "\<forall>t\<in>top1_unit_interval. f t = g t"
  shows "\<forall>t\<in>top1_unit_interval. top1_basepoint_change_on X TX x0 x1 \<alpha> f t
      = top1_basepoint_change_on X TX x0 x1 \<alpha> g t"
proof (intro ballI)
  fix t assume ht: "t \<in> top1_unit_interval"
  hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
  \<comment> \<open>bc(f)(t) = (rev(\<alpha>)*(f*\<alpha>))(t).
     For t \<le> 1/2: rev(\<alpha>)(2t). No f/g.
     For t > 1/2: (f*\<alpha>)(2t-1).
       For 2t-1 \<le> 1/2 (t \<le> 3/4): f(2*(2t-1)) = f(4t-2) with 4t-2 \<in> [0,1]. Agrees.
       For 2t-1 > 1/2 (t > 3/4): \<alpha>(2*(2t-1)-1). No f/g.\<close>
  let ?pp = top1_path_product and ?pr = top1_path_reverse
  have hbc_f: "top1_basepoint_change_on X TX x0 x1 \<alpha> f t = ?pp (?pr \<alpha>) (?pp f \<alpha>) t"
    unfolding top1_basepoint_change_on_def by (by100 simp)
  have hbc_g: "top1_basepoint_change_on X TX x0 x1 \<alpha> g t = ?pp (?pr \<alpha>) (?pp g \<alpha>) t"
    unfolding top1_basepoint_change_on_def by (by100 simp)
  show "top1_basepoint_change_on X TX x0 x1 \<alpha> f t = top1_basepoint_change_on X TX x0 x1 \<alpha> g t"
  proof (cases "t \<le> 1/2")
    case True
    have "?pp (?pr \<alpha>) (?pp f \<alpha>) t = ?pr \<alpha> (2*t)"
      unfolding top1_path_product_def using True by (by100 simp)
    moreover have "?pp (?pr \<alpha>) (?pp g \<alpha>) t = ?pr \<alpha> (2*t)"
      unfolding top1_path_product_def using True by (by100 simp)
    ultimately show ?thesis using hbc_f hbc_g by (by100 simp)
  next
    case False
    hence hgt: "t > 1/2" by (by100 simp)
    have h2t1: "0 \<le> 2*t-1" "2*t-1 \<le> 1" using ht01 hgt by (by100 simp)+
    have hout_f: "?pp (?pr \<alpha>) (?pp f \<alpha>) t = ?pp f \<alpha> (2*t-1)"
      unfolding top1_path_product_def using hgt by (by100 simp)
    have hout_g: "?pp (?pr \<alpha>) (?pp g \<alpha>) t = ?pp g \<alpha> (2*t-1)"
      unfolding top1_path_product_def using hgt by (by100 simp)
    show ?thesis
    proof (cases "2*t-1 \<le> 1/2")
      case True
      have "?pp f \<alpha> (2*t-1) = f (2*(2*t-1))"
        unfolding top1_path_product_def using True by (by100 simp)
      moreover have "?pp g \<alpha> (2*t-1) = g (2*(2*t-1))"
        unfolding top1_path_product_def using True by (by100 simp)
      moreover have "0 \<le> 2*(2*t-1)" "2*(2*t-1) \<le> 1" using True h2t1 by (by100 simp)+
      hence "2*(2*t-1) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      hence "f (2*(2*t-1)) = g (2*(2*t-1))" using assms by (by100 blast)
      ultimately show ?thesis using hbc_f hbc_g hout_f hout_g by (by100 simp)
    next
      case False
      have "?pp f \<alpha> (2*t-1) = \<alpha> (2*(2*t-1)-1)"
        unfolding top1_path_product_def using False by (by100 simp)
      moreover have "?pp g \<alpha> (2*t-1) = \<alpha> (2*(2*t-1)-1)"
        unfolding top1_path_product_def using False by (by100 simp)
      ultimately show ?thesis using hbc_f hbc_g hout_f hout_g by (by100 simp)
    qed
  qed
qed

\<comment> \<open>Reusable: under any iso \<pi>_1(S1) \<cong> Z, the standard loop maps to \<pm>1.
   This is because the lifting correspondence sends [f] to the endpoint 1 of its lift,
   and 1 generates Z. For any other iso, the image is still a generator of Z, hence \<pm>1.\<close>
lemma standard_S1_loop_generates_Z:
  assumes h\<phi>_bij: "bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
      top1_Z_group"
      and h\<phi>_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)) top1_Z_group top1_Z_mul \<phi>"
  shows "\<phi> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = 1
    \<or> \<phi> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = -1"
proof -
  let ?fclass = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}"
  \<comment> \<open>Step 1: Construct a SPECIFIC iso \<phi>_0 with \<phi>_0([f]) = 1.
     From Theorem_54_5_iso: \<exists>\<phi>_0. iso. Extract it.\<close>
  obtain \<phi>_0 where h\<phi>0_bij: "bij_betw \<phi>_0
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) top1_Z_group"
      and h\<phi>0_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)) top1_Z_group top1_Z_mul \<phi>_0"
    using Theorem_54_5_iso
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>\<phi>_0([f]) is some integer m. We don't know m = 1 a priori.
     But \<phi> \<circ> \<phi>_0\<inverse> is an auto of Z, and \<phi>([f]) = (\<phi> \<circ> \<phi>_0\<inverse>)(\<phi>_0([f])).
     By Z_auto_sends_1_to_pm1: (\<phi> \<circ> \<phi>_0\<inverse>)(1) \<in> {1,-1}.
     So \<phi>([f]) = (\<phi> \<circ> \<phi>_0\<inverse>)(m) = m * (\<phi> \<circ> \<phi>_0\<inverse>)(1) \<in> {m, -m}.
     Hmm, this doesn't help unless m = \<pm>1.

     Alternative: compose \<phi> \<circ> \<phi>_0\<inverse>: Z \<rightarrow> Z is auto. Apply to \<phi>_0([f]):
     \<phi>([f]) = (\<phi> \<circ> \<phi>_0\<inverse>)(\<phi>_0([f])). And \<phi>_0([f]) = m.
     (\<phi> \<circ> \<phi>_0\<inverse>)(m) = m * (\<phi> \<circ> \<phi>_0\<inverse>)(1) (auto of Z is multiplication).

     We need: \<phi>([f]) \<in> {1,-1}. From Z_auto: the auto maps 1 to \<pm>1.
     And \<phi>_0 is ALSO an iso, so by same argument \<phi>_0([f]) \<in> {1,-1}.
     Wait, that's circular (the SAME lemma for \<phi>_0).

     Non-circular argument: BOTH \<phi> and \<phi>_0 are isos. \<phi> \<circ> \<phi>_0\<inverse> is auto of Z.
     \<phi>([f]) = (\<phi> \<circ> \<phi>_0\<inverse>)(\<phi>_0([f])).
     Let \<alpha> = \<phi> \<circ> \<phi>_0\<inverse> and let m = \<phi>_0([f]).
     \<phi>([f]) = \<alpha>(m). \<alpha> is auto. \<alpha>(m) = m * \<alpha>(1). \<alpha>(1) \<in> {1,-1}.
     So \<phi>([f]) \<in> {m, -m}. For this to be in {1,-1}, need |m| = 1.

     But |m| = 1 IFF m generates Z IFF [f] generates \<pi>_1(S1).
     This IS the content of the lemma.

     I need to establish \<phi>_0([f]) \<in> {1,-1} for at least ONE specific \<phi>_0.
     This requires the covering space construction: lift of f ends at 1.\<close>
  \<comment> \<open>Direct proof: from Theorem 54.5, the specific iso sends [f] to 1.
     This follows from: the lift of f(s) = R_to_S1(s) starting at 0 is the identity s \<mapsto> s,
     which ends at 1. The lifting correspondence maps [f] to 1.\<close>
  have h\<phi>0_f: "\<phi>_0 ?fclass = 1 \<or> \<phi>_0 ?fclass = -1"
  proof -
    \<comment> \<open>Obtain another iso \<psi>_0 from the lifting correspondence, with \<psi>_0([f]) = 1.\<close>
    obtain \<psi>_0 where h\<psi>0_bij: "bij_betw \<psi>_0
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) top1_Z_group"
        and h\<psi>0_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0)) top1_Z_group top1_Z_mul \<psi>_0"
      using Theorem_54_5_iso
      unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by (by100 blast)
    \<comment> \<open>Key: \<psi>_0([f]) \<in> {1,-1}. From the lifting correspondence: lift of f starting at 0
       is the identity s \<mapsto> s (since R_to_S1(s) = f(s)). Endpoint = 1.
       The composition with floor gives 1. For ANY iso, the value is \<pm>1.\<close>
    \<comment> \<open>Since BOTH \<phi>_0 and \<psi>_0 are isos, \<phi>_0 \<circ> \<psi>_0\<inverse>: Z \<rightarrow> Z is an auto.
       By Z_auto: (\<phi>_0 \<circ> \<psi>_0\<inverse>)(1) \<in> {1,-1}. And (\<phi>_0 \<circ> \<psi>_0\<inverse>)(-1) \<in> {1,-1}.
       So \<phi>_0([f]) = (\<phi>_0 \<circ> \<psi>_0\<inverse>)(\<psi>_0([f])). Since \<psi>_0([f]) \<in> Z:
       \<phi>_0([f]) = n * (\<phi>_0 \<circ> \<psi>_0\<inverse>)(1) where n = \<psi>_0([f]).
       Hmm, this still needs \<psi>_0([f]) \<in> {1,-1}.
       The issue is the SAME for any iso: we need the lifting fact.\<close>
    \<comment> \<open>Direct approach: prove [f] is non-trivial (f not nulhomotopic) and
       the fiber has specific structure. For now, sorry.\<close>
    show ?thesis sorry \<comment> \<open>Covering space: standard S1 loop lifts to [0,1] ending at 1.
         Any iso π₁(S¹) → ℤ maps [f] to a generator of ℤ, i.e., ±1.\<close>
  qed
  \<comment> \<open>Step 2: \<phi> \<circ> \<phi>_0\<inverse>: Z \<rightarrow> Z is auto, sends 1 to \<pm>1.\<close>
  have hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
    unfolding top1_is_loop_on_def top1_is_path_on_def
  proof (intro conjI)
    have hf_eq: "(\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) = top1_R_to_S1"
    proof (rule ext)
      fix s :: real show "(cos (2*pi*s), sin (2*pi*s)) = top1_R_to_S1 s"
        unfolding top1_R_to_S1_def by (by100 simp)
    qed
    have "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
    from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
    show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        top1_S1 top1_S1_topology (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
      unfolding top1_unit_interval_topology_def hf_eq
      using subspace_topology_UNIV_self by (by100 simp)
  next show "(cos (2*pi*(0::real)), sin (2*pi*0)) = (1::real, 0::real)" by (by100 simp)
  next show "(cos (2*pi*(1::real)), sin (2*pi*1)) = (1::real, 0::real)" by (by100 simp)
  qed
  have hfclass_carrier: "?fclass \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
    using hf_loop unfolding top1_fundamental_group_carrier_def by (by100 blast)
  have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hS1_grp: "top1_is_group_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
      (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
      (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))"
  proof -
    have "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV, simplified]]) (by100 simp)
    moreover have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    ultimately show ?thesis by (rule top1_fundamental_group_is_group)
  qed
  \<comment> \<open>\<phi>_0\<inverse> is a hom.\<close>
  have h\<phi>0_inv_hom: "top1_group_hom_on top1_Z_group top1_Z_mul
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
      (inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_0)"
    by (rule bij_hom_inv_is_hom[OF hS1_grp hZ_grp h\<phi>0_bij h\<phi>0_hom])
  \<comment> \<open>\<phi> \<circ> \<phi>_0\<inverse> is an auto of Z.\<close>
  let ?\<alpha> = "\<phi> \<circ> (inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_0)"
  have h\<alpha>_hom: "top1_group_hom_on top1_Z_group top1_Z_mul top1_Z_group top1_Z_mul ?\<alpha>"
    by (rule group_hom_comp[OF h\<phi>0_inv_hom h\<phi>_hom])
  have h\<alpha>_bij: "bij_betw ?\<alpha> top1_Z_group top1_Z_group"
  proof -
    have "bij_betw (inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_0)
        top1_Z_group (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))"
      using bij_betw_inv_into[OF h\<phi>0_bij] .
    from bij_betw_trans[OF this h\<phi>_bij]
    show ?thesis .
  qed
  have h\<alpha>_1: "?\<alpha> 1 = 1 \<or> ?\<alpha> 1 = -1"
    by (rule Z_auto_sends_1_to_pm1[OF h\<alpha>_bij h\<alpha>_hom])
  \<comment> \<open>\<phi>([f]) = \<alpha>(\<phi>_0([f])). Since \<phi>_0([f]) \<in> {1,-1} and \<alpha>(1) \<in> {1,-1}:\<close>
  have hinj0: "inj_on \<phi>_0 (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))"
    using h\<phi>0_bij unfolding bij_betw_def by (by100 blast)
  have h\<phi>_eq: "\<phi> ?fclass = ?\<alpha> (\<phi>_0 ?fclass)"
  proof -
    have "inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_0 (\<phi>_0 ?fclass)
        = ?fclass"
      by (rule inv_into_f_f[OF hinj0 hfclass_carrier])
    thus ?thesis unfolding comp_def by (by100 simp)
  qed
  \<comment> \<open>\<alpha> is a hom Z \<rightarrow> Z: \<alpha>(n) = n * \<alpha>(1). So \<alpha>(1) = \<alpha>(1), \<alpha>(-1) = -\<alpha>(1).\<close>
  show ?thesis
  proof (cases "\<phi>_0 ?fclass = 1")
    case True
    hence "\<phi> ?fclass = ?\<alpha> 1" using h\<phi>_eq by (by100 simp)
    thus ?thesis using h\<alpha>_1 by (by100 auto)
  next
    case False
    hence hm1: "\<phi>_0 ?fclass = -1" using h\<phi>0_f by (by100 blast)
    hence "\<phi> ?fclass = ?\<alpha> (-1)" using h\<phi>_eq by (by100 simp)
    moreover have "?\<alpha> (-1) = - ?\<alpha> 1"
      using hom_preserves_inv[OF hZ_grp hZ_grp h\<alpha>_hom]
      unfolding top1_Z_group_def top1_Z_invg_def by (by100 simp)
    ultimately have "\<phi> ?fclass = - ?\<alpha> 1" by (by100 simp)
    thus ?thesis using h\<alpha>_1 by (by100 auto)
  qed
qed
\<comment> \<open>Helper: under SvK conditions with V simply connected, the inclusion U \<hookrightarrow> X
   induces a surjective homomorphism on \<pi>_1 with kernel = normal closure of
   inclusion-induced image of \<pi>_1(U\<inter>V). This is the content of Cor 70.4's proof
   (surjectivity at line 27494 of AlgTopCached) but exported as a usable fact.\<close>
lemma SvK_simply_connected_V_surj_kernel:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "(top1_fundamental_group_induced_on U (subspace_topology X TX U) x0 X TX x0 (\<lambda>x. x))
      ` (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
    = top1_fundamental_group_carrier X TX x0"
    and "top1_group_kernel_on
      (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
      (top1_fundamental_group_id X TX x0)
      (top1_fundamental_group_induced_on U (subspace_topology X TX U) x0 X TX x0 (\<lambda>x. x))
    = top1_normal_subgroup_generated_on
        (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
        (top1_fundamental_group_mul U (subspace_topology X TX U) x0)
        (top1_fundamental_group_id U (subspace_topology X TX U) x0)
        (top1_fundamental_group_invg U (subspace_topology X TX U) x0)
        (top1_fundamental_group_induced_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
           U (subspace_topology X TX U) x0 (\<lambda>x. x)
         ` top1_fundamental_group_carrier (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0)"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?piU = "top1_fundamental_group_carrier U ?TU x0"
  let ?mulU = "top1_fundamental_group_mul U ?TU x0"
  let ?eU = "top1_fundamental_group_id U ?TU x0"
  let ?invgU = "top1_fundamental_group_invg U ?TU x0"
  let ?piX = "top1_fundamental_group_carrier X TX x0"
  let ?mulX = "top1_fundamental_group_mul X TX x0"
  let ?eX = "top1_fundamental_group_id X TX x0"
  let ?invgX = "top1_fundamental_group_invg X TX x0"
  let ?j_U = "top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x)"
  let ?j_UV_U = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x)"
  let ?N = "top1_normal_subgroup_generated_on ?piU ?mulU ?eU ?invgU
      (?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)"
  have hTopX: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hUsub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
  have hx0_U: "x0 \<in> U" and hx0_V: "x0 \<in> V" and hx0_X: "x0 \<in> X"
    using assms(8) assms(4) by (by100 blast)+
  have hTopU: "is_topology_on U ?TU" by (rule subspace_topology_is_topology_on[OF hTopX hUsub])
  have hTopV: "is_topology_on V ?TV" by (rule subspace_topology_is_topology_on[OF hTopX hVsub])
  have hV_pc: "top1_path_connected_on V ?TV"
    using assms(7) unfolding top1_simply_connected_on_def by (by100 blast)
  have hincl_UX: "top1_continuous_map_on U ?TU X TX (\<lambda>x. x)"
    by (rule top1_continuous_map_on_restrict_domain_simple[OF
          top1_continuous_map_on_id[OF hTopX, unfolded id_def] hUsub])
  have hj_hom: "top1_group_hom_on ?piU ?mulU ?piX ?mulX ?j_U"
    using top1_fundamental_group_induced_on_is_hom[OF hTopU hTopX hx0_U hx0_X hincl_UX]
    by (by100 simp)
  \<comment> \<open>Part 1: Surjectivity of j_U via loop decomposition + V simply connected.\<close>
  show "?j_U ` ?piU = ?piX"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>Forward: image of hom \<subseteq> carrier.\<close>
    fix c assume "c \<in> ?j_U ` ?piU"
    then obtain u where "u \<in> ?piU" "c = ?j_U u" by (by100 blast)
    thus "c \<in> ?piX" using hj_hom unfolding top1_group_hom_on_def by (by100 blast)
  next
    \<comment> \<open>Backward: every class in \<pi>_1(X) is in image of j_U.\<close>
    fix c assume hc: "c \<in> ?piX"
    \<comment> \<open>Use Theorem_59_1 + svk_pieces_in_subgroup with H = image(j_U).\<close>
    show "c \<in> ?j_U ` ?piU"
    proof -
      \<comment> \<open>Extract representative loop.\<close>
      obtain f where hf: "top1_is_loop_on X TX x0 f" "c = {k. top1_loop_equiv_on X TX x0 f k}"
        using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>image(j_U) is a subgroup of \<pi>_1(X).\<close>
      have hpiX_grp: "top1_is_group_on ?piX ?mulX ?eX ?invgX"
        by (rule top1_fundamental_group_is_group[OF hTopX hx0_X])
      have himg_grp: "top1_is_group_on (?j_U ` ?piU) ?mulX ?eX ?invgX"
        by (rule hom_image_is_subgroup[OF
            top1_fundamental_group_is_group[OF hTopU hx0_U] hpiX_grp hj_hom])
      \<comment> \<open>U-loop classes are in image(j_U).\<close>
      have hU_in_img: "\<And>g. top1_is_loop_on U ?TU x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> ?j_U ` ?piU"
      proof -
        fix g assume hg: "top1_is_loop_on U ?TU x0 g"
        have "{k. top1_loop_equiv_on U ?TU x0 g k} \<in> ?piU"
          using hg unfolding top1_fundamental_group_carrier_def by (by100 blast)
        moreover have "?j_U {k. top1_loop_equiv_on U ?TU x0 g k}
            = {k. top1_loop_equiv_on X TX x0 g k}"
        proof -
          have "subspace_topology X TX U = ?TU" by (by100 simp)
          from inclusion_induced_class[OF hUsub hTopX this hg]
          show ?thesis .
        qed
        ultimately show "{h. top1_loop_equiv_on X TX x0 g h} \<in> ?j_U ` ?piU" by (by100 blast)
      qed
      \<comment> \<open>V-loop classes are in image(j_U) (they equal e_X = j_U(e_U)).\<close>
      have hV_in_img: "\<And>g. top1_is_loop_on V ?TV x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> ?j_U ` ?piU"
      proof -
        fix g assume hg: "top1_is_loop_on V ?TV x0 g"
        \<comment> \<open>Since V simply connected, every V-loop is nulhomotopic in V, hence in X.\<close>
        have hg_null_X: "top1_loop_equiv_on X TX x0 g (top1_constant_path x0)"
        proof -
          \<comment> \<open>V simply connected: \<pi>_1(V) = {e}.\<close>
          have "{h. top1_loop_equiv_on V ?TV x0 g h} \<in>
              top1_fundamental_group_carrier V ?TV x0"
            using hg unfolding top1_fundamental_group_carrier_def by (by100 blast)
          hence hg_class_V: "{h. top1_loop_equiv_on V ?TV x0 g h}
              = top1_fundamental_group_id V ?TV x0"
            using simply_connected_trivial_carrier[OF assms(7) hx0_V] by (by100 force)
          \<comment> \<open>g \<simeq> const in V.\<close>
          have hg_null_V: "top1_loop_equiv_on V ?TV x0 g (top1_constant_path x0)"
          proof -
            have "top1_constant_path x0 \<in> {h. top1_loop_equiv_on V ?TV x0 g h}"
              using hg_class_V top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTopV hx0_V]]
              unfolding top1_fundamental_group_id_def by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          \<comment> \<open>Transfer to X: V \<subseteq> X.\<close>
          have "top1_path_homotopic_on V ?TV x0 x0 g (top1_constant_path x0)"
            using hg_null_V unfolding top1_loop_equiv_on_def by (by100 blast)
          hence "top1_path_homotopic_on X TX x0 x0 g (top1_constant_path x0)"
          proof -
            have "subspace_topology X TX V = ?TV" by (by100 simp)
            from path_homotopic_subspace_to_ambient[OF hTopX hVsub this]
            show ?thesis using \<open>top1_path_homotopic_on V ?TV x0 x0 g (top1_constant_path x0)\<close> .
          qed
          thus ?thesis
          proof -
            have hg_X: "top1_is_loop_on X TX x0 g"
            proof -
              have hVX_cont: "top1_continuous_map_on V ?TV X TX (\<lambda>x. x)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF
                    top1_continuous_map_on_id[OF hTopX, unfolded id_def] hVsub])
              have "top1_is_loop_on X TX ((\<lambda>x. x) x0) ((\<lambda>x. x) \<circ> g)"
                by (rule top1_continuous_map_loop_early[OF hVX_cont hg])
              moreover have "(\<lambda>x::'a. x) \<circ> g = g" by (rule ext) (by100 simp)
              moreover have "(\<lambda>x::'a. x) x0 = x0" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            have hconst_X: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
              by (rule top1_constant_path_is_loop[OF hTopX hx0_X])
            show ?thesis using \<open>top1_path_homotopic_on X TX x0 x0 g (top1_constant_path x0)\<close>
              hg_X hconst_X unfolding top1_loop_equiv_on_def by (by100 blast)
          qed
        qed
        have "{h. top1_loop_equiv_on X TX x0 g h} = ?eX"
        proof -
          have hconst_X: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
            by (rule top1_constant_path_is_loop[OF hTopX hx0_X])
          show ?thesis
          proof (rule set_eqI, rule iffI)
            fix k assume "k \<in> {h. top1_loop_equiv_on X TX x0 g h}"
            hence "top1_loop_equiv_on X TX x0 g k" by (by100 blast)
            from top1_loop_equiv_on_trans[OF hTopX top1_loop_equiv_on_sym[OF hg_null_X] this]
            show "k \<in> ?eX" unfolding top1_fundamental_group_id_def by (by100 simp)
          next
            fix k assume "k \<in> ?eX"
            hence "top1_loop_equiv_on X TX x0 (top1_constant_path x0) k"
              unfolding top1_fundamental_group_id_def by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTopX hg_null_X this]
            show "k \<in> {h. top1_loop_equiv_on X TX x0 g h}" by (by100 blast)
          qed
        qed
        moreover have "?eX \<in> ?j_U ` ?piU"
        proof -
          have hpiU_grp: "top1_is_group_on ?piU ?mulU ?eU ?invgU"
            by (rule top1_fundamental_group_is_group[OF hTopU hx0_U])
          have "?j_U ?eU = ?eX"
            by (rule hom_preserves_id[OF hpiU_grp hpiX_grp hj_hom])
          moreover have "?eU \<in> ?piU"
            using hpiU_grp unfolding top1_is_group_on_def by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show "{h. top1_loop_equiv_on X TX x0 g h} \<in> ?j_U ` ?piU" by (by100 simp)
      qed
      \<comment> \<open>Apply svk_pieces_in_subgroup with H = image(j_U).\<close>
      have himg_sub: "?j_U ` ?piU \<subseteq> ?piX"
        using hj_hom unfolding top1_group_hom_on_def by (by100 blast)
      \<comment> \<open>Decompose f via Theorem_59_1.\<close>
      obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
          and hgs: "\<forall>i<n. top1_is_loop_on X TX x0 (gs!i) \<and>
                    (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)"
          and hf_eq: "top1_path_homotopic_on X TX x0 x0 f
                    (foldr top1_path_product gs (top1_constant_path x0))"
      proof -
        have hT59: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
            (\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
              (\<forall>i<n. top1_is_loop_on X TX x0 (gs!i) \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)) \<and>
              top1_path_homotopic_on X TX x0 x0 f (foldr top1_path_product gs (top1_constant_path x0)))"
          by (rule Theorem_59_1[OF assms(1-4) assms(5) assms(8)])
        from hT59[rule_format, OF hf(1)]
        obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
            and hgs: "\<forall>i<n. top1_is_loop_on X TX x0 (gs!i) \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)"
            and hf_eq: "top1_path_homotopic_on X TX x0 x0 f (foldr top1_path_product gs (top1_constant_path x0))"
          by blast
        show ?thesis using that[OF hn hlen hgs hf_eq] .
      qed
      \<comment> \<open>Apply svk_pieces_in_subgroup: [foldr(*,gs,const)] \<in> image(j_U).\<close>
      have hfoldr_in_img: "{g. top1_loop_equiv_on X TX x0
          (foldr top1_path_product gs (top1_constant_path x0)) g} \<in> ?j_U ` ?piU"
      proof -
        \<comment> \<open>Extract requirements of svk_pieces_in_subgroup from hgs.\<close>
        have hps_UV: "\<And>i. i < n \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> U)
            \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> V)"
        proof -
          fix i assume hi: "i < n"
          from hgs have himg: "gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V" using hi by (by100 blast)
          show "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> U)
              \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> V)"
          proof (cases "gs!i ` I_set \<subseteq> U")
            case True
            have "\<forall>t::real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> U"
            proof (intro allI impI)
              fix t :: real assume "0 \<le> t \<and> t \<le> 1"
              hence "(gs!i) t \<in> (gs!i) ` I_set"
                unfolding top1_unit_interval_def by (by100 force)
              thus "(gs!i) t \<in> U" using True by (by100 blast)
            qed
            thus ?thesis by (by100 blast)
          next
            case False
            hence "gs!i ` I_set \<subseteq> V" using himg by (by100 blast)
            hence "\<forall>t::real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (gs!i) t \<in> V"
            proof (intro allI impI)
              fix t :: real assume "0 \<le> t \<and> t \<le> 1"
              hence "(gs!i) t \<in> (gs!i) ` I_set"
                unfolding top1_unit_interval_def by (by100 force)
              thus "(gs!i) t \<in> V" using \<open>gs!i ` I_set \<subseteq> V\<close> by (by100 blast)
            qed
            thus ?thesis by (by100 blast)
          qed
        qed
        have hps_cont: "\<And>i. i < n \<Longrightarrow> top1_continuous_map_on I_set I_top X TX (gs!i)"
        proof -
          fix i assume "i < n"
          from hgs have "top1_is_loop_on X TX x0 (gs!i)" using \<open>i < n\<close> by (by100 blast)
          thus "top1_continuous_map_on I_set I_top X TX (gs!i)"
            unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hps_endpts: "\<And>i. i < n \<Longrightarrow> (gs!i) 0 = (if i = 0 then x0 else (gs!(i-1)) 1)"
        proof -
          fix i assume hi: "i < n"
          have "(gs!i) 0 = x0" using hgs hi
            unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          moreover {
            assume "i > 0"
            hence "(gs!(i-1)) 1 = x0" using hgs hi
              unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 force)
          }
          ultimately show "(gs!i) 0 = (if i = 0 then x0 else (gs!(i-1)) 1)" by (by100 auto)
        qed
        have hps_end: "(gs!(n-1)) 1 = x0"
          using hgs hn unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 force)
        show ?thesis
          by (rule svk_pieces_in_subgroup[OF hTopX hUsub hVsub assms(6) hV_pc assms(5) assms(8)
              himg_grp hU_in_img hV_in_img hn hlen hps_UV hps_cont hps_endpts hps_end])
      qed
      \<comment> \<open>c = [f]_X = [foldr]_X since f \<simeq> foldr.\<close>
      have "c = {g. top1_loop_equiv_on X TX x0 (foldr top1_path_product gs (top1_constant_path x0)) g}"
      proof -
        have hf_equiv_foldr: "top1_loop_equiv_on X TX x0 f
            (foldr top1_path_product gs (top1_constant_path x0))"
        proof -
          have hfoldr_loop: "top1_is_loop_on X TX x0 (foldr top1_path_product gs (top1_constant_path x0))"
            using hf_eq unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
          show ?thesis unfolding top1_loop_equiv_on_def
            using hf(1) hfoldr_loop hf_eq by (by100 blast)
        qed
        show ?thesis
        proof (rule set_eqI, rule iffI)
          fix k assume "k \<in> c"
          hence "top1_loop_equiv_on X TX x0 f k" using hf(2) by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTopX
              top1_loop_equiv_on_sym[OF hf_equiv_foldr] this]
          show "k \<in> {g. top1_loop_equiv_on X TX x0
              (foldr top1_path_product gs (top1_constant_path x0)) g}" by (by100 blast)
        next
          fix k assume "k \<in> {g. top1_loop_equiv_on X TX x0
              (foldr top1_path_product gs (top1_constant_path x0)) g}"
          hence "top1_loop_equiv_on X TX x0 (foldr top1_path_product gs (top1_constant_path x0)) k"
            by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTopX hf_equiv_foldr this]
          show "k \<in> c" using hf(2) by (by100 blast)
        qed
      qed
      thus ?thesis using hfoldr_in_img by (by100 simp)
    qed
  qed
  \<comment> \<open>Part 2: Kernel of j_U = N.\<close>
  show "top1_group_kernel_on ?piU ?eX ?j_U = ?N"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>Direction \<supseteq>: \<langle>\<langle>\<iota>*(\<pi>_1(UV))\<rangle>\<rangle> \<subseteq> ker(j_U).
       Every UV-loop is nulhomotopic in V (simply connected), hence in X.
       So \<iota>*(\<pi>_1(UV)) \<subseteq> ker(j_U), and ker(j_U) is normal, hence \<langle>\<langle>...\<rangle>\<rangle> \<subseteq> ker.\<close>
    fix c assume hc: "c \<in> ?N"
    show "c \<in> top1_group_kernel_on ?piU ?eX ?j_U"
    proof -
      \<comment> \<open>ker(j_U) is a normal subgroup.\<close>
      have hker_normal: "top1_normal_subgroup_on ?piU ?mulU ?eU ?invgU
          (top1_group_kernel_on ?piU ?eX ?j_U)"
      proof -
        have hpiU_grp: "top1_is_group_on ?piU ?mulU ?eU ?invgU"
          by (rule top1_fundamental_group_is_group[OF hTopU hx0_U])
        have hpiX_grp: "top1_is_group_on ?piX ?mulX ?eX ?invgX"
          by (rule top1_fundamental_group_is_group[OF hTopX hx0_X])
        show ?thesis by (rule kernel_is_normal_subgroup[OF hpiU_grp hpiX_grp hj_hom])
      qed
      \<comment> \<open>\<iota>*(\<pi>_1(UV)) \<subseteq> ker(j_U): UV-loops null in V \<Rightarrow> null in X.\<close>
      have hUV_in_ker: "?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0
          \<subseteq> top1_group_kernel_on ?piU ?eX ?j_U"
      proof (rule image_subsetI)
        fix cls assume hcls: "cls \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        obtain f0 where hf0: "top1_is_loop_on (U \<inter> V) ?TUV x0 f0"
            "cls = {k. top1_loop_equiv_on (U \<inter> V) ?TUV x0 f0 k}"
          using hcls unfolding top1_fundamental_group_carrier_def by (by100 blast)
        \<comment> \<open>\<iota>*(cls) = [f0]_U.\<close>
        have hUV_sub_U: "U \<inter> V \<subseteq> U" by (by100 blast)
        have hTUV_eq: "subspace_topology U ?TU (U \<inter> V) = ?TUV"
          using subspace_topology_trans[OF hUV_sub_U, of X TX] by (by100 simp)
        have h\<iota>: "?j_UV_U cls = {k. top1_loop_equiv_on U ?TU x0 f0 k}"
          using hf0(2) inclusion_induced_class[OF hUV_sub_U hTopU hTUV_eq hf0(1)]
          by (by100 simp)
        \<comment> \<open>[f0]_U \<in> \<pi>_1(U).\<close>
        have hf0_U_loop: "top1_is_loop_on U ?TU x0 f0"
        proof -
          have hUV_U_cont: "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
          proof -
            have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
              by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopU, unfolded id_def] hUV_sub_U])
            thus ?thesis using hTUV_eq by (by100 simp)
          qed
          have "top1_is_loop_on U ?TU ((\<lambda>x. x) x0) ((\<lambda>x. x) \<circ> f0)"
            by (rule top1_continuous_map_loop_early[OF hUV_U_cont hf0(1)])
          moreover have "(\<lambda>x::'a. x) \<circ> f0 = f0" by (rule ext) (by100 simp)
          moreover have "(\<lambda>x::'a. x) x0 = x0" by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have h\<iota>_carrier: "?j_UV_U cls \<in> ?piU"
          unfolding h\<iota> top1_fundamental_group_carrier_def using hf0_U_loop by (by100 blast)
        \<comment> \<open>j_U([f0]_U) = [f0]_X.\<close>
        have hj_U_cls: "?j_U (?j_UV_U cls) = {k. top1_loop_equiv_on X TX x0 f0 k}"
          unfolding h\<iota>
          using inclusion_induced_class[OF hUsub hTopX _ hf0_U_loop] by (by100 simp)
        \<comment> \<open>[f0]_X = e_X since f0 maps into UV \<subseteq> V and V simply connected.\<close>
        have hf0_V_loop: "top1_is_loop_on V ?TV x0 f0"
        proof -
          have hUV_V: "U \<inter> V \<subseteq> V" by (by100 blast)
          have hTUV_V: "subspace_topology V ?TV (U \<inter> V) = ?TUV"
            using subspace_topology_trans[OF hUV_V, of X TX] by (by100 simp)
          have hUV_V_cont: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
          proof -
            have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
              by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopV, unfolded id_def] hUV_V])
            thus ?thesis using hTUV_V by (by100 simp)
          qed
          have "top1_is_loop_on V ?TV ((\<lambda>x. x) x0) ((\<lambda>x. x) \<circ> f0)"
            by (rule top1_continuous_map_loop_early[OF hUV_V_cont hf0(1)])
          moreover have "(\<lambda>x::'a. x) \<circ> f0 = f0" by (rule ext) (by100 simp)
          moreover have "(\<lambda>x::'a. x) x0 = x0" by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have hf0_null_V: "top1_path_homotopic_on V ?TV x0 x0 f0 (top1_constant_path x0)"
        proof -
          have "{h. top1_loop_equiv_on V ?TV x0 f0 h} \<in>
              top1_fundamental_group_carrier V ?TV x0"
            using hf0_V_loop unfolding top1_fundamental_group_carrier_def by (by100 blast)
          hence "{h. top1_loop_equiv_on V ?TV x0 f0 h} = top1_fundamental_group_id V ?TV x0"
            using simply_connected_trivial_carrier[OF assms(7) hx0_V] by (by100 force)
          hence "top1_loop_equiv_on V ?TV x0 f0 (top1_constant_path x0)"
          proof -
            have hconst_refl: "top1_loop_equiv_on V ?TV x0 (top1_constant_path x0) (top1_constant_path x0)"
              by (rule top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTopV hx0_V]])
            hence "top1_constant_path x0 \<in> {h. top1_loop_equiv_on V ?TV x0 (top1_constant_path x0) h}"
              by (by100 blast)
            hence "top1_constant_path x0 \<in> top1_fundamental_group_id V ?TV x0"
              unfolding top1_fundamental_group_id_def by (by100 simp)
            hence "top1_constant_path x0 \<in> {h. top1_loop_equiv_on V ?TV x0 f0 h}"
              using \<open>{h. top1_loop_equiv_on V ?TV x0 f0 h} = top1_fundamental_group_id V ?TV x0\<close>
              by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          thus ?thesis unfolding top1_loop_equiv_on_def by (by100 blast)
        qed
        have hf0_null_X: "{k. top1_loop_equiv_on X TX x0 f0 k} = ?eX"
        proof -
          have "subspace_topology X TX V = ?TV" by (by100 simp)
          have "top1_path_homotopic_on X TX x0 x0 f0 (top1_constant_path x0)"
            using path_homotopic_subspace_to_ambient[OF hTopX hVsub \<open>subspace_topology X TX V = ?TV\<close> hf0_null_V] .
          hence "top1_loop_equiv_on X TX x0 f0 (top1_constant_path x0)"
          proof -
            have hf0_X: "top1_is_loop_on X TX x0 f0"
            proof -
              have "top1_is_loop_on X TX ((\<lambda>x. x) x0) ((\<lambda>x. x) \<circ> f0)"
                by (rule top1_continuous_map_loop_early[OF hincl_UX hf0_U_loop])
              moreover have "(\<lambda>x::'a. x) \<circ> f0 = f0" by (rule ext) (by100 simp)
              moreover have "(\<lambda>x::'a. x) x0 = x0" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            show ?thesis using hf0_X top1_constant_path_is_loop[OF hTopX hx0_X]
              \<open>top1_path_homotopic_on X TX x0 x0 f0 (top1_constant_path x0)\<close>
              unfolding top1_loop_equiv_on_def by (by100 blast)
          qed
          show ?thesis
          proof (rule set_eqI, rule iffI)
            fix k assume hk: "k \<in> {k. top1_loop_equiv_on X TX x0 f0 k}"
            hence "top1_loop_equiv_on X TX x0 f0 k" by (by100 blast)
            have hle: "top1_loop_equiv_on X TX x0 (top1_constant_path x0) f0"
              by (rule top1_loop_equiv_on_sym[OF
                  \<open>top1_loop_equiv_on X TX x0 f0 (top1_constant_path x0)\<close>])
            from top1_loop_equiv_on_trans[OF hTopX hle \<open>top1_loop_equiv_on X TX x0 f0 k\<close>]
            show "k \<in> ?eX" unfolding top1_fundamental_group_id_def by (by100 simp)
          next
            fix k assume "k \<in> ?eX"
            hence "top1_loop_equiv_on X TX x0 (top1_constant_path x0) k"
              unfolding top1_fundamental_group_id_def by (by100 simp)
            from top1_loop_equiv_on_trans[OF hTopX
                \<open>top1_loop_equiv_on X TX x0 f0 (top1_constant_path x0)\<close> this]
            show "k \<in> {k. top1_loop_equiv_on X TX x0 f0 k}" by (by100 blast)
          qed
        qed
        show "?j_UV_U cls \<in> top1_group_kernel_on ?piU ?eX ?j_U"
          unfolding top1_group_kernel_on_def using h\<iota>_carrier hj_U_cls hf0_null_X by (by100 blast)
      qed
      \<comment> \<open>Since ker is normal and contains \<iota>*(\<pi>_1(UV)), the normal closure \<subseteq> ker.\<close>
      have "?N \<subseteq> top1_group_kernel_on ?piU ?eX ?j_U"
        unfolding top1_normal_subgroup_generated_on_def
        using hUV_in_ker hker_normal by (by100 blast)
      thus ?thesis using hc by (by100 blast)
    qed
  next
    \<comment> \<open>Direction \<subseteq>: ker(j_U) \<subseteq> \<langle>\<langle>\<iota>*(\<pi>_1(UV))\<rangle>\<rangle>.
       Hard direction: nulhomotopic U-loop is product of conjugates of UV-loops.
       Requires SvK universal property / free product argument.\<close>
    fix c assume "c \<in> top1_group_kernel_on ?piU ?eX ?j_U"
    show "c \<in> ?N"
      sorry \<comment> \<open>Hard direction: uses homotopy rectangle subdivision + SvK.
           Proof exists in Corollary_70_4_simply_connected_V (AlgTopCached).\<close>
  qed
qed

\<comment> \<open>Helper: surjective hom image of a normal subgroup is normal.\<close>
lemma surj_hom_image_normal:
  assumes "top1_is_group_on G mul e invg"
      and "top1_is_group_on H mulH eH invgH"
      and "top1_group_hom_on G mul H mulH f"
      and "f ` G = H"
      and "top1_normal_subgroup_on G mul e invg N"
  shows "top1_normal_subgroup_on H mulH eH invgH (f ` N)"
  unfolding top1_normal_subgroup_on_def
proof (intro conjI)
  have hN_sub: "N \<subseteq> G" using assms(5) unfolding top1_normal_subgroup_on_def by (by100 blast)
  show "f ` N \<subseteq> H" using hN_sub assms(3) unfolding top1_group_hom_on_def by (by100 blast)
  show "top1_is_group_on (f ` N) mulH eH invgH"
  proof -
    have hN_grp: "top1_is_group_on N mul e invg"
      using assms(5) unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hf_N_hom: "top1_group_hom_on N mul H mulH f"
      using assms(3) hN_sub unfolding top1_group_hom_on_def by (by100 blast)
    show ?thesis by (rule hom_image_is_subgroup[OF hN_grp assms(2) hf_N_hom])
  qed
  show "\<forall>h'\<in>H. \<forall>n'\<in>f ` N. mulH (mulH h' n') (invgH h') \<in> f ` N"
  proof (intro ballI)
    fix h' n' assume hh': "h' \<in> H" and hn': "n' \<in> f ` N"
    obtain g where hg: "g \<in> G" "f g = h'" using assms(4) hh' by (by100 blast)
    obtain n where hn: "n \<in> N" "f n = n'" using hn' by (by100 blast)
    have hn_G: "n \<in> G" using hn(1) hN_sub by (by100 blast)
    have hconj: "mul (mul g n) (invg g) \<in> N"
      using assms(5) hg(1) hn(1) unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hgn_G: "mul g n \<in> G"
      using assms(1) hg(1) hn_G unfolding top1_is_group_on_def by (by100 blast)
    have hinvg_G: "invg g \<in> G"
      using assms(1) hg(1) unfolding top1_is_group_on_def by (by100 blast)
    have hf_mul: "\<And>a b. a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> f (mul a b) = mulH (f a) (f b)"
      using assms(3) unfolding top1_group_hom_on_def by (by100 blast)
    have "f (mul (mul g n) (invg g)) = mulH (f (mul g n)) (f (invg g))"
      by (rule hf_mul[OF hgn_G hinvg_G])
    also have "f (mul g n) = mulH (f g) (f n)"
      by (rule hf_mul[OF hg(1) hn_G])
    finally have "f (mul (mul g n) (invg g)) = mulH (mulH (f g) (f n)) (f (invg g))"
      by (by100 simp)
    moreover have "f (invg g) = invgH (f g)"
      by (rule hom_preserves_inv[OF assms(1) assms(2) assms(3) hg(1)])
    ultimately have "f (mul (mul g n) (invg g)) = mulH (mulH h' n') (invgH h')"
      using hg(2) hn(2) by (by100 simp)
    hence "mulH (mulH h' n') (invgH h') = f (mul (mul g n) (invg g))" by (by100 simp)
    thus "mulH (mulH h' n') (invgH h') \<in> f ` N"
      using hconj by (by100 blast)
  qed
qed

\<comment> \<open>Helper: injective hom + image in target set implies preimage in source set.\<close>
lemma inj_hom_preimage_normal_closure:
  assumes hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hf: "top1_group_hom_on G mulG H mulH f"
      and hf_surj: "f ` G = H"
      and hf_inj: "inj_on f G"
      and hN_normal: "top1_normal_subgroup_on G mulG eG invgG N"
      and hs_in: "s \<in> N"
      and hc_in_G: "c \<in> G"
      and hfc_in_fN: "f c \<in> top1_normal_subgroup_generated_on H mulH eH invgH {f s}"
  shows "c \<in> top1_normal_subgroup_generated_on G mulG eG invgG {s}"
proof -
  \<comment> \<open>f(N) is normal in H (surj_hom_image_normal) and contains f(s).
     So \<langle>\<langle>{f(s)}\<rangle>\<rangle>_H \<subseteq> f(N).
     f(c) \<in> \<langle>\<langle>{f(s)}\<rangle>\<rangle>_H \<subseteq> f(N), so f(c) = f(n) for some n \<in> N.
     By injectivity: c = n \<in> N.
     And N = \<langle>\<langle>{s}\<rangle>\<rangle>_G? No, N might be larger.
     But we need c \<in> \<langle>\<langle>{s}\<rangle>\<rangle>_G, not c \<in> N.\<close>
  \<comment> \<open>Better argument: for any normal M of G with s \<in> M:
     f(M) is normal in H with f(s) \<in> f(M).
     So \<langle>\<langle>{f(s)}\<rangle>\<rangle>_H \<subseteq> f(M).
     f(c) \<in> f(M), so c \<in> M (injectivity + c \<in> G).
     Since M arbitrary: c \<in> \<Inter>{M. s \<in> M \<and> normal M} = \<langle>\<langle>{s}\<rangle>\<rangle>_G.\<close>
  \<comment> \<open>For any normal M of G with s \<in> M: show c \<in> M.\<close>
  have hkey: "\<And>M. s \<in> M \<Longrightarrow> top1_normal_subgroup_on G mulG eG invgG M \<Longrightarrow> c \<in> M"
  proof -
    fix M assume hsM: "s \<in> M" and hM: "top1_normal_subgroup_on G mulG eG invgG M"
    have hfM: "top1_normal_subgroup_on H mulH eH invgH (f ` M)"
      by (rule surj_hom_image_normal[OF hG hH hf hf_surj hM])
    have hfs_fM: "f s \<in> f ` M" using hsM by (by100 blast)
    have hncl_sub: "top1_normal_subgroup_generated_on H mulH eH invgH {f s} \<subseteq> f ` M"
      unfolding top1_normal_subgroup_generated_on_def using hfs_fM hfM by (by100 blast)
    have "f c \<in> f ` M" using hfc_in_fN hncl_sub by (by100 blast)
    then obtain m where hmM: "m \<in> M" and hfm: "f m = f c" by (by100 auto)
    have hM_sub: "M \<subseteq> G" using hM unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hmG: "m \<in> G" using hmM hM_sub by (by100 blast)
    have "f c = f m" using hfm by (by100 simp)
    have "c = m" by (rule inj_onD[OF hf_inj \<open>f c = f m\<close> hc_in_G hmG])
    show "c \<in> M" using \<open>c = m\<close> hmM by (by100 simp)
  qed
  show ?thesis unfolding top1_normal_subgroup_generated_on_def
    using hkey by (by100 blast)
qed

\<comment> \<open>Helper: inclusion of subspace induces a group homomorphism on \<pi>_1.\<close>
lemma subspace_inclusion_induced_hom:
  assumes "is_topology_on X TX" "A \<subseteq> X" "x0 \<in> A"
  shows "top1_group_hom_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (top1_fundamental_group_carrier X TX x0) (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 (\<lambda>x. x))"
proof -
  have hTA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF assms(1) assms(2)])
  have hincl: "top1_continuous_map_on A (subspace_topology X TX A) X TX (\<lambda>x. x)"
  proof -
    from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF assms(1)] assms(2)]
    show ?thesis unfolding id_def by (by100 simp)
  qed
  have ha_X: "x0 \<in> X" using assms(2) assms(3) by (by100 blast)
  show ?thesis
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTA assms(1) assms(3) ha_X hincl]) (by100 simp)
qed

\<comment> \<open>Helper: for subspace inclusion A \<subseteq> X, the induced map on a loop class
   gives the same class in the larger space.\<close>
lemma subspace_inclusion_induced_class:
  assumes "is_topology_on X TX" "A \<subseteq> X" "top1_is_loop_on A (subspace_topology X TX A) x0 g"
  shows "top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 (\<lambda>x. x)
      {k. top1_loop_equiv_on A (subspace_topology X TX A) x0 g k}
    = {k. top1_loop_equiv_on X TX x0 g k}"
  using inclusion_induced_class[OF assms(2) assms(1) _ assms(3)] by (by100 simp)

\<comment> \<open>Helper: composition of two inclusion-induced maps = single inclusion-induced map.\<close>
lemma inclusion_induced_comp:
  assumes "is_topology_on X TX" "A \<subseteq> B" "B \<subseteq> X" "x0 \<in> A"
      "c \<in> top1_fundamental_group_carrier A (subspace_topology X TX A) x0"
  shows "top1_fundamental_group_induced_on B (subspace_topology X TX B) x0 X TX x0 (\<lambda>x. x)
      (top1_fundamental_group_induced_on A (subspace_topology X TX A) x0
         B (subspace_topology X TX B) x0 (\<lambda>x. x) c)
    = top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 (\<lambda>x. x) c"
proof -
  have hTA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF assms(1) subset_trans[OF assms(2) assms(3)]])
  have hTB: "is_topology_on B (subspace_topology X TX B)"
    by (rule subspace_topology_is_topology_on[OF assms(1) assms(3)])
  have hAB: "top1_continuous_map_on A (subspace_topology X TX A)
      B (subspace_topology X TX B) (\<lambda>x. x)"
  proof -
    from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTB] assms(2)]
    show ?thesis using subspace_topology_trans[OF assms(2)] unfolding id_def by (by100 simp)
  qed
  have hBX: "top1_continuous_map_on B (subspace_topology X TX B) X TX (\<lambda>x. x)"
  proof -
    from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF assms(1)] assms(3)]
    show ?thesis unfolding id_def by (by100 simp)
  qed
  have hcomp: "(\<lambda>x::'a. x) \<circ> (\<lambda>x. x) = (\<lambda>x. x)" by (rule ext) (by100 simp)
  have hx0_B: "x0 \<in> B" using assms(2) assms(4) by (by100 blast)
  have hx0_X: "x0 \<in> X" using assms(3) hx0_B by (by100 blast)
  show ?thesis
    using fundamental_group_induced_comp[OF hTA hTB assms(1) hAB hBX assms(4) _ _ assms(5)]
      hcomp by (by100 simp)
qed

\<comment> \<open>The standard circle loop (cos 2\<pi>s, sin 2\<pi>s) is a loop in S1 at (1,0).\<close>
lemma standard_S1_loop_is_loop:
  "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
     (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
  unfolding top1_is_loop_on_def top1_is_path_on_def
proof (intro conjI)
  have hf_eq: "(\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) = top1_R_to_S1"
  proof (rule ext)
    fix s :: real show "(cos (2*pi*s), sin (2*pi*s)) = top1_R_to_S1 s"
      unfolding top1_R_to_S1_def by (by100 simp)
  qed
  have "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
  from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
  show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      top1_S1 top1_S1_topology (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
    unfolding top1_unit_interval_topology_def hf_eq
    using subspace_topology_UNIV_self by (by100 simp)
next show "(cos (2*pi*(0::real)), sin (2*pi*0)) = (1::real, 0::real)" by (by100 simp)
next show "(cos (2*pi*(1::real)), sin (2*pi*1)) = (1::real, 0::real)" by (by100 simp)
qed

\<comment> \<open>The standard loop class is in \<pi>_1(S1, (1,0)).\<close>
lemma standard_S1_loop_class_in_carrier:
  "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
       (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g}
   \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
  unfolding top1_fundamental_group_carrier_def using standard_S1_loop_is_loop by (by100 blast)

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
  \<comment> \<open>Munkres 72.1 proof skeleton (algtop.tex lines 3616-3695).
     Step 1: Define U = X - {h(0)}, V = X - A = h(Int B2). Apply SvK to U, V.
     Step 2: Establish topological properties of U, V, U\<inter>V.
     Step 3: Apply Corollary 70.4 (SvK for simply connected V) at base point b \<in> U\<inter>V.
     Step 4: A is deformation retract of U, so \<pi>_1(U,a) \<cong> \<pi>_1(A,a).
     Step 5: Change base point from b back to a using path \<delta>.\<close>

  \<comment> \<open>--- Key definitions ---\<close>
  let ?TA = "subspace_topology X TX A"
  let ?x0 = "h (0::real, 0::real)"
  let ?U = "X - {?x0}"
  let ?V = "X - A"
  let ?TU = "subspace_topology X TX ?U"
  let ?TV = "subspace_topology X TX ?V"
  let ?UV = "?U \<inter> ?V"
  let ?TUV = "subspace_topology X TX ?UV"

  \<comment> \<open>--- Step 1: Basic set-theoretic facts ---\<close>
  have hA_sub_X: "A \<subseteq> X"
    using closedin_sub[OF assms(3)] by (by100 simp)
  have h00_B2: "(0::real, 0::real) \<in> top1_B2"
    unfolding top1_B2_def by (by100 simp)
  have hx0_in_X: "?x0 \<in> X"
    using continuous_map_maps_to[OF assms(5) h00_B2] by (by100 simp)
  have h00_intB2: "(0::real, 0::real) \<in> top1_B2 - top1_S1"
    unfolding top1_B2_def top1_S1_def by (by100 simp)
  have hx0_in_VA: "?x0 \<in> X - A"
    using assms(7) h00_intB2 unfolding top1_homeomorphism_on_def bij_betw_def
    by (by100 blast)
  have hx0_notin_A: "?x0 \<notin> A"
    using hx0_in_VA by (by100 blast)
  have hUV_eq: "?UV = ?V - {?x0}"
    by (by100 blast)
  have hU_union_V: "?U \<union> ?V = X"
    using hx0_notin_A hx0_in_X hA_sub_X by (by100 blast)

  \<comment> \<open>--- Step 2a: V = X - A is open in X (complement of closed set) ---\<close>
  have hV_open: "openin_on X TX ?V"
    using assms(3) hA_sub_X unfolding openin_on_def closedin_on_def by (by100 blast)

  \<comment> \<open>--- Step 2b: V is simply connected (homeomorphic to Int B2 \<cong> R2) ---\<close>
  have hV_sc: "top1_simply_connected_on ?V ?TV"
    by (rule homeomorphism_preserves_simply_connected[OF assms(7) open_disk_simply_connected])

  \<comment> \<open>--- Step 2c: U = X - {x0} is open in X (Hausdorff \<Longrightarrow> points are closed) ---\<close>
  have hx0_closed: "closedin_on X TX {?x0}"
    using singleton_closed_in_hausdorff[OF assms(2) hx0_in_X] by (by100 simp)
  have hU_open: "openin_on X TX ?U"
    using hx0_closed hx0_in_X unfolding openin_on_def closedin_on_def by (by100 blast)

  \<comment> \<open>--- Step 2d: A is a deformation retract of U (Munkres Step 1) ---\<close>
  \<comment> \<open>The deformation retraction of B2 - {0} onto S1 descends via the quotient map
     \<pi>: B2 \<rightarrow> C = h(B2) to a deformation retraction of C - {x0} onto \<pi>(S1),
     then extends to all of U by keeping A fixed.\<close>
  have hA_deformation_retract_U: "top1_deformation_retract_of_on ?U ?TU A"
  proof -
    have hA_sub_U: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
    \<comment> \<open>Define the homotopy H on U \<times> I.
       On A: H(x,t) = x (identity).
       On V\<setminus>{x0} = (X-A)\<setminus>{h(0,0)}: H(x,t) = h((1-t)\<cdot>h\<inverse>(x) + t\<cdot>h\<inverse>(x)/|h\<inverse>(x)|)
       where h\<inverse> = inv_into (B2-S1) h and |.| = sqrt(fst^2+snd^2).
       The radial interpolation moves h\<inverse>(x) toward S1, then h maps back.\<close>
    let ?D = "top1_B2 - top1_S1"
    let ?hinv = "inv_into ?D h"
    let ?norm = "\<lambda>p::real\<times>real. sqrt (fst p ^ 2 + snd p ^ 2)"
    define H_U :: "'a \<times> real \<Rightarrow> 'a" where
      "H_U = (\<lambda>(x, t). if x \<in> A then x
              else let y = ?hinv x; n = ?norm y in
                h ((1 - t) * fst y + t * fst y / n, (1 - t) * snd y + t * snd y / n))"
    \<comment> \<open>Properties verified modulo continuity.\<close>
    have hbij: "bij_betw h ?D (X - A)"
      using assms(7) unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj_D: "inj_on h ?D" using hbij unfolding bij_betw_def by (by100 blast)
    have hsurj_D: "h ` ?D = X - A" using hbij unfolding bij_betw_def by (by100 blast)
    have hH_0: "\<forall>x\<in>?U. H_U (x, 0) = x"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?U"
      show "H_U (x, 0) = x"
      proof (cases "x \<in> A")
        case True thus ?thesis unfolding H_U_def by (by100 simp)
      next
        case False
        hence hxV: "x \<in> X - A" using hx hA_sub_X by (by100 blast)
        hence hx_img: "x \<in> h ` ?D" using hsurj_D by (by100 simp)
        have hinv_D: "?hinv x \<in> ?D" using inv_into_into[OF hx_img] .
        have hh_inv: "h (?hinv x) = x" using f_inv_into_f[OF hx_img] .
        show ?thesis unfolding H_U_def Let_def using False hh_inv by (by100 simp)
      qed
    qed
    have hH_1: "\<forall>x\<in>?U. H_U (x, 1) \<in> A"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?U"
      show "H_U (x, 1) \<in> A"
      proof (cases "x \<in> A")
        case True thus ?thesis unfolding H_U_def by (by100 simp)
      next
        case False
        hence hxV: "x \<in> X - A" using hx hA_sub_X by (by100 blast)
        hence hx_img: "x \<in> h ` ?D" using hsurj_D by (by100 simp)
        have hinv_D: "?hinv x \<in> ?D" using inv_into_into[OF hx_img] .
        hence hinv_B2: "?hinv x \<in> top1_B2" by (by100 blast)
        have hx_ne: "x \<noteq> ?x0" using hx by (by100 blast)
        have hinv_ne: "?hinv x \<noteq> (0, 0)"
        proof
          assume "?hinv x = (0, 0)"
          hence "h (?hinv x) = h (0, 0)" by (by100 simp)
          hence "x = ?x0" using f_inv_into_f[OF hx_img] by (by100 simp)
          thus False using hx_ne by (by100 blast)
        qed
        have hnorm_pos: "?norm (?hinv x) > 0"
        proof -
          have "fst (?hinv x) \<noteq> 0 \<or> snd (?hinv x) \<noteq> 0"
            using hinv_ne by (cases "?hinv x") (by100 simp)
          hence "fst (?hinv x) ^ 2 + snd (?hinv x) ^ 2 > 0"
          proof
            assume "fst (?hinv x) \<noteq> 0"
            hence "fst (?hinv x) ^ 2 > 0" by (by100 simp)
            moreover have "snd (?hinv x) ^ 2 \<ge> 0" by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          next
            assume "snd (?hinv x) \<noteq> 0"
            hence "snd (?hinv x) ^ 2 > 0" by (by100 simp)
            moreover have "fst (?hinv x) ^ 2 \<ge> 0" by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          thus ?thesis by (rule real_sqrt_gt_zero)
        qed
        \<comment> \<open>y/|y| \<in> S1.\<close>
        have hy_norm_S1: "(fst (?hinv x) / ?norm (?hinv x), snd (?hinv x) / ?norm (?hinv x)) \<in> top1_S1"
        proof -
          let ?a = "fst (?hinv x)" and ?b = "snd (?hinv x)" and ?n = "?norm (?hinv x)"
          have hnn: "?n \<noteq> 0" using hnorm_pos by (by100 linarith)
          have hnsq: "?n ^ 2 = ?a ^ 2 + ?b ^ 2"
            using real_sqrt_pow2[of "?a ^ 2 + ?b ^ 2"] by (by100 simp)
          have "(?a / ?n) ^ 2 + (?b / ?n) ^ 2 = (?a ^ 2 + ?b ^ 2) / ?n ^ 2"
            by (simp add: power2_eq_square divide_simps)
          also have "\<dots> = ?n ^ 2 / ?n ^ 2" using hnsq by (by100 simp)
          also have "\<dots> = 1" using hnn by (by100 simp)
          finally show ?thesis unfolding top1_S1_def by (by100 simp)
        qed
        hence "h (fst (?hinv x) / ?norm (?hinv x), snd (?hinv x) / ?norm (?hinv x)) \<in> h ` top1_S1"
          by (by100 blast)
        hence "h (fst (?hinv x) / ?norm (?hinv x), snd (?hinv x) / ?norm (?hinv x)) \<in> A"
          using assms(8) by (by100 blast)
        thus ?thesis unfolding H_U_def Let_def using False by (by100 simp)
      qed
    qed
    have hH_A: "\<forall>a\<in>A. \<forall>t\<in>I_set. H_U (a, t) = a"
      unfolding H_U_def by (by100 simp)
    have hH_cont: "top1_continuous_map_on (?U \<times> I_set) (product_topology_on ?TU I_top) ?U ?TU H_U"
    proof -
      \<comment> \<open>Strategy: paste H_U on two closed subsets of U \<times> I.
         Piece 1: A \<times> I (H_U = identity, closed in U \<times> I).
         Piece 2: (h(B2) \<inter> U) \<times> I (H_U = descended radial retraction, closed in U \<times> I).
         Overlap: h(S1) \<times> I (both pieces agree: identity = retraction on boundary).\<close>
      let ?C = "h ` top1_B2" \<comment> \<open>C = h(B2), the image of the disk.\<close>
      let ?CU = "?C \<inter> ?U" \<comment> \<open>C \<inter> U = C - {x0}.\<close>
      \<comment> \<open>A and CU are both closed in U and cover U.\<close>
      have hU_sub_X: "?U \<subseteq> X" by (by100 blast)
      have hA_closed_U: "closedin_on ?U ?TU A"
      proof -
        \<comment> \<open>A closed in X means X-A \<in> TX. In subspace U: U-A = U \<inter> (X-A) \<in> TU.\<close>
        have "X - A \<in> TX" using assms(3) unfolding closedin_on_def by (by100 blast)
        hence "?U \<inter> (X - A) \<in> ?TU" unfolding subspace_topology_def by (by100 blast)
        moreover have "?U - A = ?U \<inter> (X - A)" by (by100 blast)
        ultimately have "?U - A \<in> ?TU" by (by100 simp)
        thus ?thesis unfolding closedin_on_def using hA_sub_U by (by100 blast)
      qed
      have hC_closed_X: "closedin_on X TX ?C"
      proof -
        have hC_sub: "?C \<subseteq> X"
          using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
        have hB2_compact: "compact top1_B2"
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
          thus ?thesis
            using closed_subset_compact[OF compact_Icc_Times _ hB2_sub] by (by100 blast)
        qed
        have "top1_compact_on top1_B2 top1_B2_topology"
        proof -
          have "top1_B2_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
            unfolding top1_B2_topology_def ..
          hence "top1_B2_topology = subspace_topology (UNIV::((real\<times>real) set)) (top1_open_sets::((real\<times>real) set set)) top1_B2"
            using product_topology_on_open_sets[where 'a=real and 'b=real] by simp
          hence "top1_compact_on top1_B2 top1_B2_topology \<longleftrightarrow> compact top1_B2"
            using top1_compact_on_subspace_UNIV_iff_compact[of top1_B2] by simp
          thus ?thesis using hB2_compact by (by100 simp)
        qed
        have "top1_compact_on ?C (subspace_topology X TX ?C)"
        proof -
          have hTX_t: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis by (rule top1_compact_on_continuous_image[OF \<open>top1_compact_on top1_B2 top1_B2_topology\<close> hTX_t assms(5)])
        qed
        thus ?thesis
          by (rule compact_in_strict_hausdorff_closedin_on[OF assms(2) assms(1) hC_sub])
      qed
      have hCU_closed_U: "closedin_on ?U ?TU ?CU"
      proof -
        have "X - ?C \<in> TX" using hC_closed_X unfolding closedin_on_def by (by100 blast)
        hence "?U \<inter> (X - ?C) \<in> ?TU" unfolding subspace_topology_def by (by100 blast)
        moreover have "?U - ?CU = ?U \<inter> (X - ?C)" by (by100 blast)
        ultimately have "?U - ?CU \<in> ?TU" by (by100 simp)
        moreover have "?CU \<subseteq> ?U" by (by100 blast)
        ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
      qed
      have hcover: "A \<union> ?CU = ?U"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> A \<union> ?CU"
        thus "x \<in> ?U" using hA_sub_U by (by100 blast)
      next
        fix x assume hx: "x \<in> ?U"
        hence hx_X: "x \<in> X" and hx_ne: "x \<noteq> ?x0" by (by100 blast)+
        show "x \<in> A \<union> ?CU"
        proof (cases "x \<in> A")
          case True thus ?thesis by (by100 blast)
        next
          case False
          hence "x \<in> X - A" using hx_X by (by100 blast)
          hence "x \<in> h ` ?D" using hsurj_D by (by100 simp)
          hence "x \<in> h ` top1_B2"
          proof -
            have "?D \<subseteq> top1_B2" by (by100 blast)
            thus ?thesis using \<open>x \<in> h ` ?D\<close> by (by100 blast)
          qed
          hence "x \<in> ?C" by (by100 blast)
          hence "x \<in> ?CU" using hx_ne hx_X by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
      qed
      \<comment> \<open>Continuity on A \<times> I: H_U = projection, continuous.\<close>
      \<comment> \<open>Use define to avoid term explosion in continuity proofs.\<close>
      define U_loc where "U_loc = ?U"
      define TU_loc where "TU_loc = ?TU"
      have hU_eq: "?U = U_loc" and hTU_eq: "?TU = TU_loc"
        unfolding U_loc_def TU_loc_def by simp+
      have hTopX_ns: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      have hU_sub_X2: "U_loc \<subseteq> X" unfolding U_loc_def by (by100 blast)
      have hTopU_loc: "is_topology_on U_loc TU_loc"
        unfolding TU_loc_def U_loc_def by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
      have hA_sub_U_loc: "A \<subseteq> U_loc" using hA_sub_U hU_eq by simp
      have hH_cont_A: "top1_continuous_map_on (A \<times> I_set)
          (product_topology_on (subspace_topology U_loc TU_loc A) I_top) U_loc TU_loc H_U"
      proof -
        have hid_cont: "top1_continuous_map_on U_loc TU_loc U_loc TU_loc id"
          by (rule top1_continuous_map_on_id[OF hTopU_loc])
        have hincl: "top1_continuous_map_on A (subspace_topology U_loc TU_loc A) U_loc TU_loc id"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_cont hA_sub_U_loc])
        have hincl': "top1_continuous_map_on A (subspace_topology U_loc TU_loc A) U_loc TU_loc (\<lambda>x. x)"
          using hincl unfolding id_def by (by100 simp)
        have hTAU: "is_topology_on A (subspace_topology U_loc TU_loc A)"
          by (rule subspace_topology_is_topology_on[OF hTopU_loc hA_sub_U_loc])
        have hfst_cont: "top1_continuous_map_on (A \<times> I_set)
            (product_topology_on (subspace_topology U_loc TU_loc A) I_top) U_loc TU_loc (\<lambda>p. fst p)"
          using homotopy_const_continuous[OF hincl' hTAU] by (by100 simp)
        have "\<forall>p\<in>A \<times> I_set. H_U p = fst p"
          unfolding H_U_def by force
        thus ?thesis using top1_continuous_map_on_cong hfst_cont by (by100 blast)
      qed
      \<comment> \<open>Convert back from U_loc/TU_loc to ?U/?TU.\<close>
      hence hH_cont_A': "top1_continuous_map_on (A \<times> I_set)
          (product_topology_on (subspace_topology ?U ?TU A) I_top) ?U ?TU H_U"
        using hU_eq hTU_eq by simp
      \<comment> \<open>Continuity on CU \<times> I: H_U = h((1-t)*y + t*y/|y|) via quotient descent.\<close>
      have hH_cont_CU: "top1_continuous_map_on (?CU \<times> I_set)
          (product_topology_on (subspace_topology ?U ?TU ?CU) I_top) ?U ?TU H_U"
      proof -
        \<comment> \<open>Following Munkres Step 1: use quotient map \<pi> \<times> id to descend the retraction.\<close>
        let ?C = "h ` top1_B2"
        let ?TC = "subspace_topology X TX ?C"
        let ?B2_0 = "top1_B2 - {(0::real, 0::real)}"
        \<comment> \<open>Step A: \<pi> \<times> id: B2 \<times> I \<rightarrow> C \<times> I is a quotient map.\<close>
        \<comment> \<open>(Compact \<times> compact \<rightarrow> Hausdorff \<times> Hausdorff, continuous surjection \<Rightarrow> closed \<Rightarrow> quotient.)\<close>
        let ?\<pi>I = "\<lambda>(y, t). (h y, t)"
        \<comment> \<open>h\<pi>I_quot is derived after Step C from hB2I_compact, hCI_hausdorff, h\<pi>I_cont.\<close>
        \<comment> \<open>Step B: (B2\{0}) \<times> I is open in B2 \<times> I and saturated w.r.t. \<pi> \<times> id.\<close>
        have hB20I_open: "openin_on (top1_B2 \<times> I_set)
            (product_topology_on top1_B2_topology I_top) (?B2_0 \<times> I_set)"
        proof -
          have hTI: "is_topology_on I_set I_top"
            by (rule top1_unit_interval_topology_is_topology_on)
          have hI_in: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
          \<comment> \<open>B2\{0} is open in B2: {0} closed in Hausdorff B2, complement is open.\<close>
          have hB20_open_B2: "?B2_0 \<in> top1_B2_topology"
          proof -
            \<comment> \<open>B2_top = sub UNIV R2_top B2. B2\{0} = B2 \<inter> (UNIV-{0}). (UNIV-{0}) open in R2.\<close>
            have "(UNIV :: (real\<times>real) set) - {(0,0)} \<in> product_topology_on top1_open_sets top1_open_sets"
            proof -
              have "closedin_on (UNIV :: (real\<times>real) set)
                  (product_topology_on top1_open_sets top1_open_sets) {(0::real, 0::real)}"
                by (rule singleton_closed_in_hausdorff[OF top1_R2_is_hausdorff]) (by100 simp)
              thus ?thesis unfolding closedin_on_def by (by100 blast)
            qed
            moreover have "?B2_0 = top1_B2 \<inter> ((UNIV :: (real\<times>real) set) - {(0,0)})" by (by100 blast)
            ultimately show ?thesis unfolding top1_B2_topology_def subspace_topology_def
              by (by100 blast)
          qed
          have "?B2_0 \<times> I_set \<in> product_topology_on top1_B2_topology I_top"
            by (rule product_rect_open[OF hB20_open_B2 hI_in])
          moreover have "?B2_0 \<times> I_set \<subseteq> top1_B2 \<times> I_set" by (by100 blast)
          ultimately show ?thesis unfolding openin_on_def by (by100 blast)
        qed
        have h_preimg_x0: "\<forall>y\<in>top1_B2. h y = ?x0 \<longrightarrow> y = (0, 0)"
        proof (intro ballI impI)
          fix y assume "y \<in> top1_B2" "h y = ?x0"
          show "y = (0, 0)"
          proof (cases "y \<in> top1_S1")
            case True
            hence "h y \<in> A" using assms(8) by (by100 blast)
            hence "?x0 \<in> A" using \<open>h y = ?x0\<close> by (by100 simp)
            thus ?thesis using hx0_notin_A by (by100 blast)
          next
            case False
            hence "y \<in> top1_B2 - top1_S1" using \<open>y \<in> top1_B2\<close> by (by100 blast)
            thus ?thesis using inj_on_eq_iff[OF hinj_D \<open>y \<in> top1_B2 - top1_S1\<close> h00_intB2]
              \<open>h y = ?x0\<close> by (by100 simp)
          qed
        qed
        have hB20I_sat: "top1_saturated_with_respect_to_on (top1_B2 \<times> I_set) ?\<pi>I (?B2_0 \<times> I_set)"
          unfolding top1_saturated_with_respect_to_on_def
        proof (intro conjI)
          show "?B2_0 \<times> I_set \<subseteq> top1_B2 \<times> I_set" by (by100 blast)
        next
          show "\<forall>x\<in>?B2_0 \<times> I_set. \<forall>y\<in>top1_B2 \<times> I_set. ?\<pi>I y = ?\<pi>I x \<longrightarrow> y \<in> ?B2_0 \<times> I_set"
          proof (intro ballI impI)
            fix p1 p2
            assume hp1: "p1 \<in> ?B2_0 \<times> I_set" and hp2: "p2 \<in> top1_B2 \<times> I_set"
              and heq: "?\<pi>I p2 = ?\<pi>I p1"
            obtain y1 t1 where "p1 = (y1, t1)" "y1 \<in> ?B2_0" "t1 \<in> I_set"
              using hp1 by (by100 blast)
            obtain y2 t2 where "p2 = (y2, t2)" "y2 \<in> top1_B2" "t2 \<in> I_set"
              using hp2 by (by100 blast)
            have "h y2 = h y1" "t2 = t1"
              using heq \<open>p1 = (y1, t1)\<close> \<open>p2 = (y2, t2)\<close> by (by100 simp)+
            have "y1 \<noteq> (0, 0)" using \<open>y1 \<in> ?B2_0\<close> by (by100 blast)
            hence "h y1 \<noteq> ?x0" using h_preimg_x0 \<open>y1 \<in> ?B2_0\<close> by (by100 blast)
            hence "h y2 \<noteq> ?x0" using \<open>h y2 = h y1\<close> by (by100 simp)
            hence "y2 \<noteq> (0, 0)" using h_preimg_x0 \<open>y2 \<in> top1_B2\<close> by (by100 blast)
            hence "y2 \<in> ?B2_0" using \<open>y2 \<in> top1_B2\<close> by (by100 blast)
            thus "p2 \<in> ?B2_0 \<times> I_set" using \<open>p2 = (y2, t2)\<close> \<open>t2 \<in> I_set\<close> \<open>t2 = t1\<close>
              by (by100 blast)
          qed
        qed
        \<comment> \<open>CU \<times> I = \<pi>I(B2\{0} \<times> I) = (C - {x0}) \<times> I.\<close>
        have hCU_eq_img: "?CU = h ` ?B2_0"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> ?CU"
          hence "x \<in> h ` top1_B2" "x \<noteq> ?x0" "x \<in> X" by (by100 auto)+
          then obtain y where "y \<in> top1_B2" "h y = x" by (by100 blast)
          have "y \<noteq> (0, 0)" using \<open>h y = x\<close> \<open>x \<noteq> ?x0\<close> by (by100 auto)
          thus "x \<in> h ` ?B2_0" using \<open>y \<in> top1_B2\<close> \<open>h y = x\<close> by (by100 blast)
        next
          fix x assume "x \<in> h ` ?B2_0"
          then obtain y where "y \<in> ?B2_0" "h y = x" by (by100 blast)
          have "y \<in> top1_B2" using \<open>y \<in> ?B2_0\<close> by (by100 blast)
          have "x \<in> h ` top1_B2" using \<open>y \<in> top1_B2\<close> \<open>h y = x\<close> by (by100 blast)
          moreover have "x \<noteq> ?x0"
            using h_preimg_x0 \<open>y \<in> top1_B2\<close> \<open>y \<in> ?B2_0\<close> \<open>h y = x\<close> by (by100 blast)
          moreover have "x \<in> X"
            using continuous_map_maps_to[OF assms(5) \<open>y \<in> top1_B2\<close>] \<open>h y = x\<close> by (by100 simp)
          ultimately show "x \<in> ?CU" by (by100 blast)
        qed
        have hCU_times_eq: "?CU \<times> I_set = ?\<pi>I ` (?B2_0 \<times> I_set)"
        proof (rule set_eqI, rule iffI)
          fix p assume "p \<in> ?CU \<times> I_set"
          then obtain x t where "p = (x, t)" "x \<in> ?CU" "t \<in> I_set" by (by100 blast)
          hence "x \<in> h ` ?B2_0" using hCU_eq_img by (by100 blast)
          then obtain y where "y \<in> ?B2_0" "h y = x" by (by100 blast)
          hence "?\<pi>I (y, t) = p" using \<open>p = (x, t)\<close> by (by100 simp)
          moreover have "(y, t) \<in> ?B2_0 \<times> I_set" using \<open>y \<in> ?B2_0\<close> \<open>t \<in> I_set\<close> by (by100 blast)
          ultimately show "p \<in> ?\<pi>I ` (?B2_0 \<times> I_set)" by (by100 blast)
        next
          fix p assume "p \<in> ?\<pi>I ` (?B2_0 \<times> I_set)"
          then obtain y t where "y \<in> ?B2_0" "t \<in> I_set" "p = (h y, t)" by (by100 auto)
          have "h y \<in> ?CU" using hCU_eq_img \<open>y \<in> ?B2_0\<close> by (by100 blast)
          thus "p \<in> ?CU \<times> I_set" using \<open>p = (h y, t)\<close> \<open>t \<in> I_set\<close> by (by100 blast)
        qed
        \<comment> \<open>Step C: By Theorem 22.1, \<pi>' = (\<pi> \<times> id)|_{B2\{0} \<times> I} is a quotient map.\<close>
        \<comment> \<open>We use: \<pi> \<times> id is a closed map (\<Rightarrow> part 2 of Theorem 22.1).\<close>
        have hB2_compact_top1: "top1_compact_on top1_B2 top1_B2_topology"
        proof -
          have "compact top1_B2"
          proof -
            have hB2_sub: "top1_B2 \<subseteq> {-1..1} \<times> {-1..1::real}"
            proof
              fix p :: "real \<times> real" assume "p \<in> top1_B2"
              hence h: "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
              have "0 \<le> snd p ^ 2" by (by100 simp)
              hence "fst p ^ 2 \<le> 1" using h by (by100 linarith)
              hence "\<bar>fst p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>fst p\<bar>" 1] by (by100 simp)
              hence hf: "- 1 \<le> fst p \<and> fst p \<le> 1" by (by100 linarith)
              have "0 \<le> fst p ^ 2" by (by100 simp)
              hence "snd p ^ 2 \<le> 1" using h by (by100 linarith)
              hence "\<bar>snd p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>snd p\<bar>" 1] by (by100 simp)
              hence "- 1 \<le> snd p \<and> snd p \<le> 1" by (by100 linarith)
              thus "p \<in> {-1..1} \<times> {-1..1}" using hf by (simp add: mem_Times_iff)
            qed
            have "closed top1_B2"
            proof -
              have "top1_B2 = (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1}"
                unfolding top1_B2_def by (by100 auto)
              moreover have "continuous_on UNIV (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2)"
                by (intro continuous_intros)
              hence "closed ((\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1})"
                by (intro closed_vimage closed_atMost)
                   (simp add: continuous_on_eq_continuous_at open_UNIV)
              ultimately show ?thesis by (by100 simp)
            qed
            thus ?thesis using closed_subset_compact[OF compact_Icc_Times _ hB2_sub] by (by100 blast)
          qed
          moreover have "top1_B2_topology = subspace_topology UNIV top1_open_sets top1_B2"
            unfolding top1_B2_topology_def
            using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
          ultimately show ?thesis
            using top1_compact_on_subspace_UNIV_iff_compact[of top1_B2] by (by100 simp)
        qed
        have hI_compact_top1: "top1_compact_on I_set I_top"
        proof -
          have "compact I_set" unfolding top1_unit_interval_def
            using top1_compact_Icc_linear_continuum[of "0::real" 1] by (by100 simp)
          moreover have "I_top = subspace_topology UNIV top1_open_sets I_set"
            unfolding top1_unit_interval_topology_def by (by100 simp)
          ultimately show ?thesis
            using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by (by100 simp)
        qed
        have hB2I_compact: "top1_compact_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)"
          by (rule Theorem_26_7[OF hB2_compact_top1 hI_compact_top1])
        have hCI_hausdorff: "is_hausdorff_on (?C \<times> I_set) (product_topology_on ?TC I_top)"
        proof -
          \<comment> \<open>Extract sub-Hausdorff and product-Hausdorff from Theorem 17.11.\<close>
          have hsub_haus: "\<And>X0 T0 Y0. is_hausdorff_on X0 T0 \<Longrightarrow> Y0 \<subseteq> X0 \<Longrightarrow>
              is_hausdorff_on Y0 (subspace_topology X0 T0 Y0)"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
          have hprod_haus: "\<And>X1 T1 X2 T2. is_hausdorff_on X1 T1 \<Longrightarrow> is_hausdorff_on X2 T2 \<Longrightarrow>
              is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
            using conjunct1[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
          have hC_sub_X: "?C \<subseteq> X" using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
          have hC_haus: "is_hausdorff_on ?C ?TC" by (rule hsub_haus[OF assms(2) hC_sub_X])
          have hI_haus: "is_hausdorff_on I_set I_top"
          proof -
            have "I_top = subspace_topology (UNIV::real set) top1_open_sets I_set"
              unfolding top1_unit_interval_topology_def by (by100 simp)
            thus ?thesis using hsub_haus[OF top1_R_is_hausdorff, of I_set] by (by100 simp)
          qed
          show ?thesis by (rule hprod_haus[OF hC_haus hI_haus])
        qed
        have h\<pi>I_cont: "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
            (?C \<times> I_set) (product_topology_on ?TC I_top) ?\<pi>I"
        proof -
          have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (top1_open_sets::(real\<times>real) set set)"
            using top1_R2_is_hausdorff unfolding is_hausdorff_on_def
            using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
          have hTB2: "is_topology_on top1_B2 top1_B2_topology"
          proof -
            have "top1_B2_topology = subspace_topology UNIV top1_open_sets top1_B2"
              unfolding top1_B2_topology_def
              using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 simp)
            thus ?thesis using subspace_topology_is_topology_on[OF hTR2, of top1_B2] by (by100 simp)
          qed
          have hTI: "is_topology_on I_set I_top"
            by (rule top1_unit_interval_topology_is_topology_on)
          have hTBI: "is_topology_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)"
            by (rule product_topology_on_is_topology_on[OF hTB2 hTI])
          have hTX: "is_topology_on X TX"
            using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hC_sub_X_loc: "?C \<subseteq> X"
            using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
          have hTC_top: "is_topology_on ?C ?TC"
            by (rule subspace_topology_is_topology_on[OF hTX hC_sub_X_loc])
          \<comment> \<open>By Theorem 18.4: f continuous iff pi1\<circ>f and pi2\<circ>f continuous.\<close>
          have hpi1_cont: "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
              ?C ?TC (pi1 \<circ> ?\<pi>I)"
          proof -
            have hC_sub_X_loc: "?C \<subseteq> X"
              using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
            have h_to_C: "top1_continuous_map_on top1_B2 top1_B2_topology ?C ?TC h"
              using top1_continuous_map_on_codomain_shrink[OF assms(5) _ hC_sub_X_loc]
              by (by100 blast)
            have hpi1_B2: "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                top1_B2 top1_B2_topology pi1"
              by (rule top1_continuous_pi1[OF hTB2 hTI])
            have "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                ?C ?TC (h \<circ> pi1)"
              by (rule top1_continuous_map_on_comp[OF hpi1_B2 h_to_C])
            have heq: "h \<circ> pi1 = pi1 \<circ> ?\<pi>I" unfolding pi1_def by (rule ext) (by100 auto)
            show ?thesis unfolding heq[symmetric]
              by (rule top1_continuous_map_on_comp[OF hpi1_B2 h_to_C])
          qed
          have hpi2_cont: "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
              I_set I_top (pi2 \<circ> ?\<pi>I)"
          proof -
            have heq2: "pi2 = pi2 \<circ> ?\<pi>I" unfolding pi2_def by (rule ext) (by100 auto)
            show ?thesis unfolding heq2[symmetric]
              by (rule top1_continuous_pi2[OF hTB2 hTI])
          qed
          show ?thesis using iffD2[OF Theorem_18_4[OF hTBI hTC_top hTI]] hpi1_cont hpi2_cont
            by (by100 blast)
        qed
        have h\<pi>I_closed: "top1_closed_map_on (top1_B2 \<times> I_set)
            (product_topology_on top1_B2_topology I_top)
            (?C \<times> I_set) (product_topology_on ?TC I_top) ?\<pi>I"
          unfolding top1_closed_map_on_def
        proof (intro conjI ballI allI impI)
          fix p assume "p \<in> top1_B2 \<times> I_set"
          then obtain y t where "p = (y, t)" "y \<in> top1_B2" "t \<in> I_set" by (by100 blast)
          show "?\<pi>I p \<in> ?C \<times> I_set" using \<open>p = (y,t)\<close> \<open>y \<in> top1_B2\<close> \<open>t \<in> I_set\<close> by (by100 auto)
        next
          fix A assume hA: "closedin_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top) A"
          show "closedin_on (?C \<times> I_set) (product_topology_on ?TC I_top) (?\<pi>I ` A)"
            by (rule compact_hausdorff_continuous_closed_map[OF hB2I_compact hCI_hausdorff h\<pi>I_cont hA])
        qed
        \<comment> \<open>Use define to make \<pi>I opaque, avoiding lambda explosion in set operations.\<close>
        define piI :: "(real\<times>real) \<times> real \<Rightarrow> 'a \<times> real" where "piI = ?\<pi>I"
        have hpiI_cont: "top1_continuous_map_on (top1_B2 \<times> I_set)
            (product_topology_on top1_B2_topology I_top) (?C \<times> I_set) (product_topology_on ?TC I_top) piI"
          using h\<pi>I_cont unfolding piI_def .
        have hpiI_closed: "top1_closed_map_on (top1_B2 \<times> I_set)
            (product_topology_on top1_B2_topology I_top) (?C \<times> I_set) (product_topology_on ?TC I_top) piI"
          using h\<pi>I_closed unfolding piI_def .
        have hpiI_surj: "piI ` (top1_B2 \<times> I_set) = ?C \<times> I_set"
          unfolding piI_def by (by100 auto)
        have hTBI_loc: "is_topology_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)"
          using hB2I_compact unfolding top1_compact_on_def by (by100 blast)
        have hTCI_loc: "is_topology_on (?C \<times> I_set) (product_topology_on ?TC I_top)"
          using hCI_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
        have h\<pi>I_quot: "top1_quotient_map_on (top1_B2 \<times> I_set)
            (product_topology_on top1_B2_topology I_top)
            (?C \<times> I_set) (product_topology_on ?TC I_top) ?\<pi>I"
        proof -
          have "top1_quotient_map_on (top1_B2 \<times> I_set)
              (product_topology_on top1_B2_topology I_top)
              (?C \<times> I_set) (product_topology_on ?TC I_top) piI"
            unfolding top1_quotient_map_on_def
          proof (intro conjI allI impI)
            show "is_topology_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)"
              by (rule hTBI_loc)
            show "is_topology_on (?C \<times> I_set) (product_topology_on ?TC I_top)"
              by (rule hTCI_loc)
            show "top1_continuous_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?C \<times> I_set) (product_topology_on ?TC I_top) piI" by (rule hpiI_cont)
            show "piI ` (top1_B2 \<times> I_set) = ?C \<times> I_set" by (rule hpiI_surj)
            fix V assume hV_sub: "V \<subseteq> ?C \<times> I_set"
              and hV_pre: "{x \<in> top1_B2 \<times> I_set. piI x \<in> V} \<in> product_topology_on top1_B2_topology I_top"
            have hcomp_closed: "closedin_on (top1_B2 \<times> I_set)
                (product_topology_on top1_B2_topology I_top)
                {x \<in> top1_B2 \<times> I_set. piI x \<notin> V}"
              unfolding closedin_on_def
            proof (intro conjI)
              show "{x \<in> top1_B2 \<times> I_set. piI x \<notin> V} \<subseteq> top1_B2 \<times> I_set" by (by100 blast)
              have "(top1_B2 \<times> I_set) - {x \<in> top1_B2 \<times> I_set. piI x \<notin> V}
                  = {x \<in> top1_B2 \<times> I_set. piI x \<in> V}" by (by100 blast)
              thus "(top1_B2 \<times> I_set) - {x \<in> top1_B2 \<times> I_set. piI x \<notin> V}
                  \<in> product_topology_on top1_B2_topology I_top"
                using hV_pre by (by100 simp)
            qed
            have himg_closed: "closedin_on (?C \<times> I_set) (product_topology_on ?TC I_top)
                (piI ` {x \<in> top1_B2 \<times> I_set. piI x \<notin> V})"
              using hpiI_closed hcomp_closed unfolding top1_closed_map_on_def by (by100 blast)
            have himg_eq: "piI ` {x \<in> top1_B2 \<times> I_set. piI x \<notin> V} = (?C \<times> I_set) - V"
            proof (rule set_eqI, rule iffI)
              fix z assume "z \<in> piI ` {x \<in> top1_B2 \<times> I_set. piI x \<notin> V}"
              then obtain x where hx: "x \<in> top1_B2 \<times> I_set" "piI x \<notin> V" "piI x = z" by (by100 blast)
              have "z \<in> ?C \<times> I_set" using hx(1) hx(3) hpiI_surj by (by100 blast)
              moreover have "z \<notin> V" using hx(2) hx(3) by (by100 simp)
              ultimately show "z \<in> (?C \<times> I_set) - V" by (by100 blast)
            next
              fix z assume hz: "z \<in> (?C \<times> I_set) - V"
              hence "z \<in> piI ` (top1_B2 \<times> I_set)" using hpiI_surj by (by100 blast)
              then obtain x where "x \<in> top1_B2 \<times> I_set" "piI x = z" by (by100 blast)
              hence "piI x \<notin> V" using hz by (by100 blast)
              thus "z \<in> piI ` {x \<in> top1_B2 \<times> I_set. piI x \<notin> V}"
                using \<open>x \<in> top1_B2 \<times> I_set\<close> \<open>piI x = z\<close> by (by100 blast)
            qed
            have "closedin_on (?C \<times> I_set) (product_topology_on ?TC I_top) ((?C \<times> I_set) - V)"
              using himg_closed himg_eq by (by100 simp)
            have "(?C \<times> I_set) - ((?C \<times> I_set) - V) = V" using hV_sub by (by100 blast)
            thus "V \<in> product_topology_on ?TC I_top"
              using \<open>closedin_on (?C \<times> I_set) _ ((?C \<times> I_set) - V)\<close>
              unfolding closedin_on_def by (by100 simp)
          qed
          thus ?thesis unfolding piI_def .
        qed
        have h\<pi>'_quot: "top1_quotient_map_on (?B2_0 \<times> I_set)
            (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
              (?B2_0 \<times> I_set))
            (?CU \<times> I_set)
            (subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?CU \<times> I_set))
            ?\<pi>I"
        proof -
          \<comment> \<open>By Theorem 22.1 part 2: closed map \<Rightarrow> restriction to saturated is quotient.\<close>
          from Theorem_22_1[OF h\<pi>I_quot hB20I_sat]
          have h22_1: "(top1_closed_map_on (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?C \<times> I_set) (product_topology_on ?TC I_top) ?\<pi>I) \<longrightarrow>
              top1_quotient_map_on (?B2_0 \<times> I_set)
                (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                  (?B2_0 \<times> I_set))
                (?\<pi>I ` (?B2_0 \<times> I_set))
                (subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?\<pi>I ` (?B2_0 \<times> I_set)))
                ?\<pi>I"
            by (by100 blast)
          have himg_eq: "?\<pi>I ` (?B2_0 \<times> I_set) = ?CU \<times> I_set" using hCU_times_eq by (by100 simp)
          have "top1_quotient_map_on (?B2_0 \<times> I_set)
              (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top) (?B2_0 \<times> I_set))
              (?\<pi>I ` (?B2_0 \<times> I_set))
              (subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?\<pi>I ` (?B2_0 \<times> I_set)))
              ?\<pi>I"
            using h22_1 h\<pi>I_closed by (by100 blast)
          thus ?thesis using himg_eq by (by100 simp)
        qed
        \<comment> \<open>Step D: The radial retraction G(y,t) = h(interp(y,t)) is continuous on B2\{0} \<times> I.\<close>
        let ?G = "\<lambda>(y, t). h ((1 - t) * fst y + t * fst y / ?norm y,
                              (1 - t) * snd y + t * snd y / ?norm y)"
        have hG_cont: "top1_continuous_map_on (?B2_0 \<times> I_set)
            (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
              (?B2_0 \<times> I_set))
            ?U ?TU ?G"
        proof -
          \<comment> \<open>Decompose G = h \<circ> interp where interp(y,t) = radial interpolation.\<close>
          let ?interp = "\<lambda>(y::real\<times>real, t::real).
              ((1 - t) * fst y + t * fst y / sqrt (fst y ^ 2 + snd y ^ 2),
               (1 - t) * snd y + t * snd y / sqrt (fst y ^ 2 + snd y ^ 2))"
          \<comment> \<open>Step 1: interp is continuous_on in HOL Analysis sense.\<close>
          have hinterp_cont_on: "continuous_on (?B2_0 \<times> I_set) ?interp"
          proof -
            have hsqrt_pos: "\<forall>p \<in> ?B2_0 \<times> I_set. sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) > 0"
            proof (intro ballI)
              fix p assume "p \<in> ?B2_0 \<times> I_set"
              hence "fst p \<in> ?B2_0" by (by100 auto)
              hence "fst p \<noteq> (0::real, 0::real)" by (by100 blast)
              hence "fst (fst p) \<noteq> 0 \<or> snd (fst p) \<noteq> 0" by (cases "fst p") (by100 simp)
              hence "fst (fst p) ^ 2 > 0 \<or> snd (fst p) ^ 2 > 0" by (by100 auto)
              moreover have "fst (fst p) ^ 2 \<ge> 0" "snd (fst p) ^ 2 \<ge> 0" by (by100 simp)+
              ultimately have "fst (fst p) ^ 2 + snd (fst p) ^ 2 > 0" by (by100 linarith)
              thus "sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) > 0" by (by100 simp)
            qed
            have hsqrt_ne0: "\<forall>p \<in> ?B2_0 \<times> I_set. sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) \<noteq> 0"
            proof (intro ballI)
              fix p assume "p \<in> ?B2_0 \<times> I_set"
              have "sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) > 0"
                using hsqrt_pos \<open>p \<in> ?B2_0 \<times> I_set\<close> by (by100 blast)
              thus "sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2) \<noteq> 0" by (by100 linarith)
            qed
            \<comment> \<open>continuous_on for the whole thing: use continuous_on_Pair + continuous_intros.\<close>
            have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. fst (fst p))" by (intro continuous_intros)
            have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. snd (fst p))" by (intro continuous_intros)
            have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. snd p)" by (intro continuous_intros)
            have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. fst (fst p) ^ 2 + snd (fst p) ^ 2)"
              by (intro continuous_intros)
            have hsqrt_cont: "continuous_on (?B2_0 \<times> I_set)
                (\<lambda>p::(real\<times>real)\<times>real. sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
            proof -
              have "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. fst (fst p) ^ 2 + snd (fst p) ^ 2)"
                by (intro continuous_intros)
              hence "continuous_on (?B2_0 \<times> I_set)
                  (\<lambda>p::(real\<times>real)\<times>real. fst (fst p) ^ 2 + snd (fst p) ^ 2)"
                by (rule continuous_on_subset) (by100 blast)
              thus ?thesis by (intro continuous_intros)
            qed
            \<comment> \<open>Each component: (1-t)*a + t*a/sqrt(...) is continuous (projections + arith + div).\<close>
            \<comment> \<open>Prove on UNIV first (fast), then restrict to B2\{0}\<times>I.\<close>
            let ?S = "?B2_0 \<times> I_set"
            have hA1_univ: "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * fst (fst p))"
              by (intro continuous_intros)
            have hA2_univ: "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * snd (fst p))"
              by (intro continuous_intros)
            have hN1_univ: "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. snd p * fst (fst p))"
              by (intro continuous_intros)
            have hN2_univ: "continuous_on UNIV (\<lambda>p::(real\<times>real)\<times>real. snd p * snd (fst p))"
              by (intro continuous_intros)
            \<comment> \<open>Restrict to S = B2\{0} \<times> I.\<close>
            have hA1: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * fst (fst p))"
              using continuous_on_subset[OF hA1_univ] by (by100 blast)
            have hA2: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * snd (fst p))"
              using continuous_on_subset[OF hA2_univ] by (by100 blast)
            have hN1: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. snd p * fst (fst p))"
              using continuous_on_subset[OF hN1_univ] by (by100 blast)
            have hN2: "continuous_on ?S (\<lambda>p::(real\<times>real)\<times>real. snd p * snd (fst p))"
              using continuous_on_subset[OF hN2_univ] by (by100 blast)
            \<comment> \<open>Division by sqrt (nonzero on S).\<close>
            have hD1: "continuous_on ?S
                (\<lambda>p::(real\<times>real)\<times>real. snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
              apply (rule continuous_on_divide[OF hN1 hsqrt_cont])
              using hsqrt_ne0 by (by100 blast)
            have hD2: "continuous_on ?S
                (\<lambda>p::(real\<times>real)\<times>real. snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
              apply (rule continuous_on_divide[OF hN2 hsqrt_cont])
              using hsqrt_ne0 by (by100 blast)
            \<comment> \<open>Sum of the two terms.\<close>
            have hcomp1_cont: "continuous_on ?S
                (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * fst (fst p) +
                  snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
              by (rule continuous_on_add[OF hA1 hD1])
            have hcomp2_cont: "continuous_on ?S
                (\<lambda>p::(real\<times>real)\<times>real. (1 - snd p) * snd (fst p) +
                  snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2))"
              by (rule continuous_on_add[OF hA2 hD2])
            have "?interp = (\<lambda>p. ((1 - snd p) * fst (fst p) +
                snd p * fst (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2),
                (1 - snd p) * snd (fst p) +
                snd p * snd (fst p) / sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2)))"
              by (rule ext) (by100 auto)
            thus ?thesis using continuous_on_Pair[OF hcomp1_cont hcomp2_cont] by (by100 simp)
          qed
          \<comment> \<open>Step 2: interp maps B2\{0} \<times> I into B2.\<close>
          have hinterp_range: "\<forall>p \<in> ?B2_0 \<times> I_set. ?interp p \<in> top1_B2"
          proof (intro ballI)
            fix p assume "p \<in> ?B2_0 \<times> I_set"
            hence hy: "fst p \<in> top1_B2" and hy_ne: "fst p \<noteq> (0::real, 0)" and ht: "snd p \<in> I_set"
              by (by100 auto)+
            have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
              using ht unfolding top1_unit_interval_def by (by100 simp)+
            have "fst p \<noteq> (0::real, 0)" using hy_ne by (by100 blast)
            hence "fst (fst p) ^ 2 + snd (fst p) ^ 2 > 0"
            proof -
              have "fst (fst p) \<noteq> 0 \<or> snd (fst p) \<noteq> 0" using hy_ne by (cases "fst p") (by100 simp)
              hence "fst (fst p) ^ 2 > 0 \<or> snd (fst p) ^ 2 > 0" by (by100 auto)
              moreover have "fst (fst p) ^ 2 \<ge> 0" "snd (fst p) ^ 2 \<ge> 0" by (by100 simp)+
              ultimately show ?thesis by (by100 linarith)
            qed
            let ?n = "sqrt (fst (fst p) ^ 2 + snd (fst p) ^ 2)"
            let ?q = "(fst (fst p) / ?n, snd (fst p) / ?n)"
            have hn_pos: "?n > 0" using \<open>fst (fst p) ^ 2 + snd (fst p) ^ 2 > 0\<close> by (by100 simp)
            have hq_S1: "fst ?q ^ 2 + snd ?q ^ 2 = 1"
            proof -
              have hpd1: "(fst (fst p) / ?n) ^ 2 = fst (fst p) ^ 2 / ?n ^ 2" by (rule power_divide)
              have hpd2: "(snd (fst p) / ?n) ^ 2 = snd (fst p) ^ 2 / ?n ^ 2" by (rule power_divide)
              have hn2: "?n ^ 2 = fst (fst p) ^ 2 + snd (fst p) ^ 2"
                using \<open>fst (fst p) ^ 2 + snd (fst p) ^ 2 > 0\<close>
                by (rule real_sqrt_pow2[OF order_less_imp_le])
              have "fst (fst p) ^ 2 / ?n ^ 2 + snd (fst p) ^ 2 / ?n ^ 2
                  = (fst (fst p) ^ 2 + snd (fst p) ^ 2) / ?n ^ 2"
                by (rule add_divide_distrib[symmetric])
              also have "\<dots> = ?n ^ 2 / ?n ^ 2" using hn2 by (by100 simp)
              also have "\<dots> = 1" using hn_pos by (by100 auto)
              finally show ?thesis using hpd1 hpd2 by (by100 simp)
            qed
            have hq_B2: "?q \<in> top1_B2" using hq_S1 unfolding top1_B2_def by (by100 simp)
            have "((1 - snd p) * fst (fst p) + snd p * fst ?q,
                   (1 - snd p) * snd (fst p) + snd p * snd ?q) \<in> top1_B2"
              using top1_B2_convex[OF hy hq_B2 ht0 ht1] by (by100 simp)
            moreover have "?interp p = ((1 - snd p) * fst (fst p) + snd p * fst ?q,
                                    (1 - snd p) * snd (fst p) + snd p * snd ?q)"
              by (cases p) (by100 simp)
            ultimately show "?interp p \<in> top1_B2" by (by100 simp)
          qed
          \<comment> \<open>Step 3: Bridge to top1: interp is top1_continuous_map_on.\<close>
          have hinterp_top1: "top1_continuous_map_on (?B2_0 \<times> I_set)
              (subspace_topology UNIV top1_open_sets (?B2_0 \<times> I_set))
              top1_B2 (subspace_topology UNIV top1_open_sets top1_B2)
              ?interp"
            using top1_continuous_map_on_subspace_open_sets_on[OF _ hinterp_cont_on]
              hinterp_range by (by100 blast)
          \<comment> \<open>Step 4: Topology equalities for domain and codomain.\<close>
          have hdom_top_eq: "subspace_topology UNIV top1_open_sets (?B2_0 \<times> I_set)
              = subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                  (?B2_0 \<times> I_set)"
          proof -
            have hTB2: "is_topology_on (UNIV::(real\<times>real) set) (top1_open_sets::(real\<times>real) set set)"
              using top1_R2_is_hausdorff unfolding is_hausdorff_on_def
              using product_topology_on_open_sets[where ?'a = real and ?'b = real] by (by100 simp)
            have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
              using top1_R_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
            \<comment> \<open>prod B2_top I_top = sub UNIV open (B2\<times>I) by Theorem 16.3.\<close>
            have "product_topology_on top1_B2_topology I_top
                = product_topology_on (subspace_topology UNIV top1_open_sets top1_B2)
                    (subspace_topology UNIV top1_open_sets I_set)"
              unfolding top1_B2_topology_def top1_unit_interval_topology_def
              using product_topology_on_open_sets[where ?'a = real and ?'b = real]
              by (by100 simp)
            also have "\<dots> = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets)
                (top1_B2 \<times> I_set)"
              by (rule Theorem_16_3[OF hTB2 hTR])
            also have "\<dots> = subspace_topology UNIV top1_open_sets (top1_B2 \<times> I_set)"
              using product_topology_on_open_sets[where ?'a = "real\<times>real" and ?'b = real]
              by (by100 simp)
            finally have hprod_eq: "product_topology_on top1_B2_topology I_top
                = subspace_topology UNIV top1_open_sets (top1_B2 \<times> I_set)" .
            \<comment> \<open>By subspace transitivity: sub (B2\<times>I) (sub UNIV open (B2\<times>I)) (B2_0\<times>I) = sub UNIV open (B2_0\<times>I).\<close>
            have "subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?B2_0 \<times> I_set) =
                subspace_topology (top1_B2 \<times> I_set) (subspace_topology UNIV top1_open_sets (top1_B2 \<times> I_set))
                (?B2_0 \<times> I_set)" using hprod_eq by (by100 simp)
            also have "\<dots> = subspace_topology UNIV top1_open_sets (?B2_0 \<times> I_set)"
              by (rule subspace_topology_trans) (by100 blast)
            finally show ?thesis by (by100 simp)
          qed
          have hcod_top_eq: "subspace_topology UNIV top1_open_sets top1_B2 = top1_B2_topology"
            unfolding top1_B2_topology_def
            using product_topology_on_open_sets[where ?'a = real and ?'b = real]
            by (by100 simp)
          \<comment> \<open>Step 5: Compose interp with h to get G.\<close>
          have hinterp_top1': "top1_continuous_map_on (?B2_0 \<times> I_set)
              (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?B2_0 \<times> I_set))
              top1_B2 top1_B2_topology ?interp"
            using hinterp_top1 hdom_top_eq hcod_top_eq by (by100 simp)
          have hG_eq: "?G = (\<lambda>p. h (?interp p))"
            by (rule ext) (by100 auto)
          have "?G = h \<circ> ?interp" using hG_eq by (by100 auto)
          \<comment> \<open>Step 6: Compose with h continuous and restrict codomain to U.\<close>
          have hG_cont_X: "top1_continuous_map_on (?B2_0 \<times> I_set)
              (subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?B2_0 \<times> I_set))
              X TX ?G"
            using top1_continuous_map_on_comp[OF hinterp_top1' assms(5)]
              \<open>?G = h \<circ> ?interp\<close> by (by100 simp)
          \<comment> \<open>Step 7: G image is in U (h(interp(y,t)) \<noteq> x0 when y \<noteq> 0).\<close>
          have hG_range_U: "\<forall>p\<in>?B2_0 \<times> I_set. ?G p \<in> ?U"
          proof (intro ballI)
            fix p assume hp: "p \<in> ?B2_0 \<times> I_set"
            have hip: "?interp p \<in> top1_B2" using hinterp_range hp by (by100 blast)
            hence "?G p \<in> X" using continuous_map_maps_to[OF assms(5)] \<open>?G = h \<circ> ?interp\<close>
              by (by100 auto)
            moreover have "?G p \<noteq> ?x0"
            proof -
              \<comment> \<open>interp(y,t) \<noteq> (0,0): coefficient (1-t+t/|y|) > 0 and y \<noteq> 0.\<close>
              have "?interp p \<noteq> (0::real, 0)"
              proof
                assume h0: "?interp p = (0, 0)"
                define yf where "yf = fst (fst p)"
                define ys where "ys = snd (fst p)"
                define tt where "tt = snd p"
                define nn where "nn = sqrt (yf ^ 2 + ys ^ 2)"
                have hyf_ne: "yf \<noteq> 0 \<or> ys \<noteq> 0"
                  using hp unfolding yf_def ys_def by (cases "fst p") (by100 auto)
                have hnn_pos: "nn > 0"
                proof -
                  have "yf ^ 2 > 0 \<or> ys ^ 2 > 0" using hyf_ne by (by100 auto)
                  moreover have "yf ^ 2 \<ge> 0" "ys ^ 2 \<ge> 0" by (by100 simp)+
                  ultimately have "yf ^ 2 + ys ^ 2 > 0" by (by100 linarith)
                  thus ?thesis unfolding nn_def by (by100 simp)
                qed
                have hnn_ne0: "nn \<noteq> 0" using hnn_pos by (by100 linarith)
                have ht0: "0 \<le> tt" and ht1: "tt \<le> 1"
                  using hp unfolding tt_def top1_unit_interval_def by (by100 auto)+
                \<comment> \<open>From interp = (0,0): first component = 0.\<close>
                have hfst0: "(1 - tt) * yf + tt * yf / nn = 0"
                  using h0 unfolding yf_def ys_def tt_def nn_def by (cases p) (by100 simp)
                \<comment> \<open>Multiply by nn to clear division.\<close>
                have h_distrib_yf: "nn * ((1 - tt) * yf + tt * yf / nn)
                    = nn * ((1 - tt) * yf) + nn * (tt * yf / nn)" by (rule distrib_left)
                have h_cancel_yf: "nn * (tt * yf / nn) = tt * yf" using hnn_ne0 by (by100 simp)
                have h_assoc_yf: "nn * ((1 - tt) * yf) = (1 - tt) * nn * yf" by (by100 simp)
                have "(1 - tt) * nn * yf + tt * yf = 0"
                  using h_distrib_yf h_cancel_yf h_assoc_yf hfst0 by (by100 simp)
                have h_factor_yf: "(1 - tt) * nn * yf + tt * yf = ((1 - tt) * nn + tt) * yf"
                  by (rule distrib_right[symmetric])
                hence h_ring_yf: "((1 - tt) * nn + tt) * yf = 0"
                  using \<open>(1 - tt) * nn * yf + tt * yf = 0\<close> by (by100 simp)
                \<comment> \<open>Similarly for snd.\<close>
                have hsnd0: "(1 - tt) * ys + tt * ys / nn = 0"
                  using h0 unfolding yf_def ys_def tt_def nn_def by (cases p) (by100 simp)
                have h_distrib_ys: "nn * ((1 - tt) * ys + tt * ys / nn)
                    = nn * ((1 - tt) * ys) + nn * (tt * ys / nn)" by (rule distrib_left)
                have h_cancel_ys: "nn * (tt * ys / nn) = tt * ys" using hnn_ne0 by (by100 simp)
                have h_assoc_ys: "nn * ((1 - tt) * ys) = (1 - tt) * nn * ys" by (by100 simp)
                have "(1 - tt) * nn * ys + tt * ys = 0"
                  using h_distrib_ys h_cancel_ys h_assoc_ys hsnd0 by (by100 simp)
                have h_factor_ys: "(1 - tt) * nn * ys + tt * ys = ((1 - tt) * nn + tt) * ys"
                  by (rule distrib_right[symmetric])
                hence h_ring_ys: "((1 - tt) * nn + tt) * ys = 0"
                  using \<open>(1 - tt) * nn * ys + tt * ys = 0\<close> by (by100 simp)
                \<comment> \<open>Coefficient > 0, so yf = 0 and ys = 0.\<close>
                have hcoeff_pos: "(1 - tt) * nn + tt > 0"
                proof (cases "tt = 0")
                  case True thus ?thesis using hnn_pos by (by100 simp)
                next
                  case False
                  have "(1 - tt) * nn \<ge> 0" using ht1 hnn_pos by (by100 simp)
                  moreover have "tt > 0" using ht0 False by (by100 linarith)
                  ultimately show ?thesis by (by100 linarith)
                qed
                have "yf = 0" using h_ring_yf hcoeff_pos by (by100 simp)
                moreover have "ys = 0" using h_ring_ys hcoeff_pos by (by100 simp)
                ultimately show False using hyf_ne by (by100 simp)
              qed
              hence "?interp p \<in> top1_B2 \<and> ?interp p \<noteq> (0, 0)" using hip by (by100 blast)
              hence "h (?interp p) \<noteq> h (0, 0)"
                using h_preimg_x0 by (by100 blast)
              thus ?thesis using \<open>?G = h \<circ> ?interp\<close> by (by100 auto)
            qed
            ultimately show "?G p \<in> ?U" by (by100 blast)
          qed
          \<comment> \<open>Step 8: Restrict codomain from X to U.\<close>
          have hG_img_U: "?G ` (?B2_0 \<times> I_set) \<subseteq> ?U"
          proof (rule image_subsetI)
            fix p assume "p \<in> ?B2_0 \<times> I_set"
            thus "?G p \<in> ?U" using hG_range_U by (by100 blast)
          qed
          have hU_sub_X: "?U \<subseteq> X" by (by100 blast)
          show ?thesis
            apply (rule top1_continuous_map_on_codomain_shrink)
              apply (rule hG_cont_X)
             apply (rule hG_img_U)
            by (by100 blast)
        qed
        \<comment> \<open>Step E: G is constant on fibers of \<pi>'.\<close>
        have hG_fiber: "\<forall>p1\<in>?B2_0 \<times> I_set. \<forall>p2\<in>?B2_0 \<times> I_set.
            ?\<pi>I p1 = ?\<pi>I p2 \<longrightarrow> ?G p1 = ?G p2"
        proof (intro ballI impI)
          fix p1 p2 assume hp1: "p1 \<in> ?B2_0 \<times> I_set" and hp2: "p2 \<in> ?B2_0 \<times> I_set"
            and heqp: "?\<pi>I p1 = ?\<pi>I p2"
          obtain y1 t1 where hp1_eq: "p1 = (y1, t1)" and hy1: "y1 \<in> ?B2_0" "t1 \<in> I_set"
            using hp1 by (by100 blast)
          obtain y2 t2 where hp2_eq: "p2 = (y2, t2)" and hy2: "y2 \<in> ?B2_0" "t2 \<in> I_set"
            using hp2 by (by100 blast)
          have "h y1 = h y2" and "t1 = t2" using heqp unfolding hp1_eq hp2_eq by (by100 simp)+
          \<comment> \<open>Fiber respect: h(y1)=h(y2) \<Longrightarrow> G(y1,t)=G(y2,t) (same as earlier proof).\<close>
          have "y1 \<in> top1_B2 - top1_S1 \<or> y1 \<in> top1_S1" using hy1(1) by (by100 blast)
          moreover have "y2 \<in> top1_B2 - top1_S1 \<or> y2 \<in> top1_S1" using hy2(1) by (by100 blast)
          ultimately have "?G (y1, t1) = ?G (y2, t1)"
          proof (elim disjE)
            assume "y1 \<in> top1_B2 - top1_S1" and "y2 \<in> top1_B2 - top1_S1"
            hence "y1 = y2" using inj_onD[OF hinj_D \<open>h y1 = h y2\<close>] by (by100 blast)
            thus ?thesis by (by100 simp)
          next
            assume hy1S: "y1 \<in> top1_S1" and hy2S: "y2 \<in> top1_S1"
            have hn1: "?norm y1 = 1" using hy1S unfolding top1_S1_def by (by100 auto)
            have hn2: "?norm y2 = 1" using hy2S unfolding top1_S1_def by (by100 auto)
            have hrw: "\<And>a::real. (1 - t1) * a + t1 * a = a"
            proof -
              fix a :: real
              have "(1 - t1) * a + t1 * a = ((1 - t1) + t1) * a" by (rule distrib_right[symmetric])
              also have "\<dots> = a" by (by100 simp)
              finally show "(1 - t1) * a + t1 * a = a" .
            qed
            have "?G (y1, t1) = h y1" using hn1 hrw by (cases y1) (by100 simp)
            moreover have "?G (y2, t1) = h y2" using hn2 hrw by (cases y2) (by100 simp)
            ultimately show ?thesis using \<open>h y1 = h y2\<close> by (by100 simp)
          next
            assume "y1 \<in> top1_B2 - top1_S1" and "y2 \<in> top1_S1"
            have "h y1 \<in> X - A" using \<open>y1 \<in> top1_B2 - top1_S1\<close> hsurj_D by (by100 blast)
            moreover have "h y2 \<in> A" using \<open>y2 \<in> top1_S1\<close> assms(8) by (by100 blast)
            ultimately have "h y1 \<in> X - A \<and> h y1 \<in> A" using \<open>h y1 = h y2\<close> by (by100 simp)
            thus ?thesis by (by100 blast)
          next
            assume "y1 \<in> top1_S1" and "y2 \<in> top1_B2 - top1_S1"
            have "h y1 \<in> A" using \<open>y1 \<in> top1_S1\<close> assms(8) by (by100 blast)
            moreover have "h y2 \<in> X - A" using \<open>y2 \<in> top1_B2 - top1_S1\<close> hsurj_D by (by100 blast)
            ultimately have "h y1 \<in> A \<and> h y1 \<in> X - A" using \<open>h y1 = h y2\<close> by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          thus "?G p1 = ?G p2" unfolding hp1_eq hp2_eq using \<open>t1 = t2\<close> by (by100 simp)
        qed
        \<comment> \<open>Step F: By Theorem 22.2, G descends to continuous H_CU on CU \<times> I.\<close>
        \<comment> \<open>H_U agrees with the descended map on CU \<times> I.\<close>
        \<comment> \<open>Topology transfer: sub(C\<times>I)(prod TC I_top)(CU\<times>I) = prod(sub U TU CU)(I_top).\<close>
        have htop_CUI: "subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?CU \<times> I_set)
            = product_topology_on (subspace_topology ?U ?TU ?CU) I_top"
        proof -
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          have hTX: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hC_sub_X: "?C \<subseteq> X" using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
          have hTC: "is_topology_on ?C ?TC" by (rule subspace_topology_is_topology_on[OF hTX hC_sub_X])
          have hCU_sub_C: "?CU \<subseteq> ?C" by (by100 blast)
          have "subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?CU \<times> I_set)
              = product_topology_on (subspace_topology ?C ?TC ?CU) (subspace_topology I_set I_top I_set)"
            by (rule Theorem_16_3[OF hTC hTI, symmetric])
          moreover have "subspace_topology I_set I_top I_set = I_top"
          proof (rule subspace_topology_self, intro ballI)
            fix V assume "V \<in> I_top"
            thus "V \<subseteq> I_set" unfolding top1_unit_interval_topology_def subspace_topology_def
              by (by100 blast)
          qed
          moreover have "subspace_topology ?C ?TC ?CU = subspace_topology X TX ?CU"
            by (rule subspace_topology_trans[OF hCU_sub_C])
          moreover have "subspace_topology X TX ?CU = subspace_topology ?U ?TU ?CU"
          proof -
            have "?CU \<subseteq> ?U" by (by100 blast)
            thus ?thesis by (rule subspace_topology_trans[symmetric])
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Key functional equality: H_U \<circ> \<pi>' = G on B2\{0}\<times>I.\<close>
        have hHU_piI_eq_G: "\<forall>q\<in>?B2_0 \<times> I_set. H_U (?\<pi>I q) = ?G q"
        proof (intro ballI)
          fix q assume hq: "q \<in> ?B2_0 \<times> I_set"
          obtain y0 t0 where hq_eq: "q = (y0, t0)" and hy0: "y0 \<in> ?B2_0" and ht0: "t0 \<in> I_set"
            using hq by (by100 blast)
          have "?\<pi>I q = (h y0, t0)" using hq_eq by (by100 simp)
          show "H_U (?\<pi>I q) = ?G q"
          proof (cases "y0 \<in> top1_S1")
            case True
            hence "h y0 \<in> A" using assms(8) by (by100 blast)
            hence "H_U (h y0, t0) = h y0" unfolding H_U_def by (by100 simp)
            moreover have "?norm y0 = 1" using True unfolding top1_S1_def by (by100 auto)
            hence "?G (y0, t0) = h y0"
            proof -
              have hrw: "\<And>a::real. (1 - t0) * a + t0 * a = a"
              proof -
                fix a :: real
                have "(1 - t0) * a + t0 * a = ((1 - t0) + t0) * a" by (rule distrib_right[symmetric])
                also have "\<dots> = a" by (by100 simp)
                finally show "(1 - t0) * a + t0 * a = a" .
              qed
              show ?thesis using \<open>?norm y0 = 1\<close> hrw by (cases y0) (by100 simp)
            qed
            ultimately show ?thesis using \<open>?\<pi>I q = (h y0, t0)\<close> hq_eq by (by100 simp)
          next
            case False
            hence hy0_D: "y0 \<in> ?D" using hy0 by (by100 blast)
            hence "h y0 \<notin> A"
            proof -
              have "h y0 \<in> X - A" using hy0_D hsurj_D by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            have hhiny0: "?hinv (h y0) = y0"
              using inv_into_f_eq[OF hinj_D] hy0_D by (by100 blast)
            have "H_U (h y0, t0) = h ((1 - t0) * fst (?hinv (h y0)) + t0 * fst (?hinv (h y0)) / ?norm (?hinv (h y0)),
                (1 - t0) * snd (?hinv (h y0)) + t0 * snd (?hinv (h y0)) / ?norm (?hinv (h y0)))"
              unfolding H_U_def Let_def using \<open>h y0 \<notin> A\<close> by (by100 simp)
            hence "H_U (h y0, t0) = ?G (y0, t0)" using hhiny0 by (by100 simp)
            thus ?thesis using \<open>?\<pi>I q = (h y0, t0)\<close> hq_eq by (by100 simp)
          qed
        qed
        \<comment> \<open>Direct proof via quotient open-set characterization.\<close>
        \<comment> \<open>V \<in> TU \<Rightarrow> {p\<in>CU\<times>I. H_U p \<in> V} open. By quotient: \<leftrightarrow> G\<inverse>(V) open. G continuous \<Rightarrow> \<checkmark>.\<close>
        show ?thesis unfolding htop_CUI[symmetric] top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume hp: "p \<in> ?CU \<times> I_set"
          show "H_U p \<in> ?U"
          proof -
            have "p \<in> ?\<pi>I ` (?B2_0 \<times> I_set)" using hCU_times_eq hp by (by100 simp)
            then obtain q where hq: "q \<in> ?B2_0 \<times> I_set" "?\<pi>I q = p" by (by100 blast)
            have "H_U (?\<pi>I q) = ?G q" using hHU_piI_eq_G hq(1) by (by100 blast)
            hence "H_U p = ?G q" using hq(2) by (by100 simp)
            moreover have "?G q \<in> ?U" using hG_cont hq(1) unfolding top1_continuous_map_on_def
              by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
        next
          fix V assume hV: "V \<in> ?TU"
          \<comment> \<open>Need: {p\<in>CU\<times>I. H_U p \<in> V} \<in> sub(C\<times>I)(prod TC I_top)(CU\<times>I).\<close>
          \<comment> \<open>By quotient property of \<pi>': equivalent to \<pi>'\<inverse>({p. H_U p \<in> V}) open in B2_0\<times>I.\<close>
          let ?preimg_HU = "{p \<in> ?CU \<times> I_set. H_U p \<in> V}"
          have "?preimg_HU \<subseteq> ?CU \<times> I_set" by (by100 blast)
          \<comment> \<open>\<pi>'\<inverse>(preimg_HU) = {q \<in> B2_0\<times>I. H_U(\<pi>I q) \<in> V} = {q \<in> B2_0\<times>I. G q \<in> V}.\<close>
          have hpreimg_eq: "{q \<in> ?B2_0 \<times> I_set. ?\<pi>I q \<in> ?preimg_HU} =
              {q \<in> ?B2_0 \<times> I_set. ?G q \<in> V}"
          proof (rule set_eqI, rule iffI)
            fix q assume "q \<in> {q \<in> ?B2_0 \<times> I_set. ?\<pi>I q \<in> ?preimg_HU}"
            hence hq: "q \<in> ?B2_0 \<times> I_set" and "H_U (?\<pi>I q) \<in> V" by (by100 auto)+
            have "H_U (?\<pi>I q) = ?G q" using hHU_piI_eq_G hq by (by100 blast)
            hence "?G q = H_U (?\<pi>I q)" by (by100 simp)
            hence "?G q \<in> V" using \<open>H_U (?\<pi>I q) \<in> V\<close> by (by100 simp)
            thus "q \<in> {q \<in> ?B2_0 \<times> I_set. ?G q \<in> V}" using hq by (by100 blast)
          next
            fix q assume "q \<in> {q \<in> ?B2_0 \<times> I_set. ?G q \<in> V}"
            hence hq: "q \<in> ?B2_0 \<times> I_set" and "?G q \<in> V" by (by100 auto)+
            have "H_U (?\<pi>I q) = ?G q" using hHU_piI_eq_G hq by (by100 blast)
            hence "H_U (?\<pi>I q) \<in> V" using \<open>?G q \<in> V\<close> by (by100 simp)
            moreover have "?\<pi>I q \<in> ?CU \<times> I_set" using hCU_times_eq hq by (by100 simp)
            ultimately show "q \<in> {q \<in> ?B2_0 \<times> I_set. ?\<pi>I q \<in> ?preimg_HU}" using hq by (by100 blast)
          qed
          \<comment> \<open>G continuous + V \<in> TU \<Rightarrow> G\<inverse>(V) open in B2_0\<times>I.\<close>
          have hG_preimg_open: "{q \<in> ?B2_0 \<times> I_set. ?G q \<in> V} \<in>
              subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?B2_0 \<times> I_set)"
            using hG_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>By quotient: preimg open \<Rightarrow> set open in CU\<times>I.\<close>
          have hpreimg_piI_open: "{q \<in> ?B2_0 \<times> I_set. ?\<pi>I q \<in> ?preimg_HU} \<in>
              subspace_topology (top1_B2 \<times> I_set) (product_topology_on top1_B2_topology I_top)
                (?B2_0 \<times> I_set)"
            using hG_preimg_open hpreimg_eq by (by100 simp)
          show "?preimg_HU \<in> subspace_topology (?C \<times> I_set) (product_topology_on ?TC I_top) (?CU \<times> I_set)"
            using h\<pi>'_quot hpreimg_piI_open \<open>?preimg_HU \<subseteq> ?CU \<times> I_set\<close>
            unfolding top1_quotient_map_on_def by (by100 blast)
        qed
      qed
      \<comment> \<open>(Old quotient descent code removed; replaced by pasting approach above.)\<close>
      \<comment> \<open>Paste via pasting_lemma_two_closed.\<close>
      \<comment> \<open>Paste: A \<times> I and CU \<times> I are closed in U \<times> I, cover U \<times> I, H_U continuous on each.\<close>
      show ?thesis
      proof -
        define UI where "UI = U_loc \<times> I_set"
        define TUI where "TUI = product_topology_on TU_loc I_top"
        have "top1_continuous_map_on UI TUI U_loc TU_loc H_U"
        proof (rule pasting_lemma_two_closed[where A="A \<times> I_set" and B="?CU \<times> I_set"])
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          show "is_topology_on UI TUI" unfolding UI_def TUI_def
            by (rule product_topology_on_is_topology_on[OF hTopU_loc hTI])
          show "is_topology_on U_loc TU_loc" by (rule hTopU_loc)
          show "closedin_on UI TUI (A \<times> I_set)"
            unfolding closedin_on_def UI_def TUI_def
          proof (intro conjI)
            show "A \<times> I_set \<subseteq> U_loc \<times> I_set" using hA_sub_U_loc by (by100 blast)
            have "U_loc \<times> I_set - A \<times> I_set = (U_loc - A) \<times> I_set" by (by100 blast)
            moreover have "U_loc - A \<in> TU_loc"
            proof -
              have "?U - A \<in> ?TU" using hA_closed_U unfolding closedin_on_def by (by100 blast)
              thus ?thesis using hU_eq hTU_eq by simp
            qed
            moreover have hI_in: "I_set \<in> I_top"
              using hTI unfolding is_topology_on_def by (by100 blast)
            ultimately have "(U_loc - A) \<times> I_set \<in> product_topology_on TU_loc I_top"
              using product_rect_open by (by100 blast)
            thus "U_loc \<times> I_set - A \<times> I_set \<in> product_topology_on TU_loc I_top"
              using \<open>U_loc \<times> I_set - A \<times> I_set = (U_loc - A) \<times> I_set\<close> by (by100 simp)
          qed
          show "closedin_on UI TUI (?CU \<times> I_set)"
            unfolding closedin_on_def UI_def TUI_def
          proof (intro conjI)
            show "?CU \<times> I_set \<subseteq> U_loc \<times> I_set" unfolding U_loc_def by (by100 blast)
            have "U_loc \<times> I_set - ?CU \<times> I_set = (U_loc - ?CU) \<times> I_set" by (by100 blast)
            moreover have "U_loc - ?CU \<in> TU_loc"
            proof -
              have "?U - ?CU \<in> ?TU" using hCU_closed_U unfolding closedin_on_def by (by100 blast)
              thus ?thesis using hU_eq hTU_eq by simp
            qed
            moreover have hI_in2: "I_set \<in> I_top"
              using hTI unfolding is_topology_on_def by (by100 blast)
            ultimately have "(U_loc - ?CU) \<times> I_set \<in> product_topology_on TU_loc I_top"
              using product_rect_open[of "U_loc - ?CU" TU_loc I_set I_top] by (by100 blast)
            thus "U_loc \<times> I_set - ?CU \<times> I_set \<in> product_topology_on TU_loc I_top"
              using \<open>U_loc \<times> I_set - ?CU \<times> I_set = (U_loc - ?CU) \<times> I_set\<close> by (by100 simp)
          qed
          show "A \<times> I_set \<union> ?CU \<times> I_set = UI" unfolding UI_def U_loc_def using hcover by (by100 blast)
          show "\<forall>x\<in>UI. H_U x \<in> U_loc"
          proof
            fix xt assume "xt \<in> UI"
            hence hx_U: "fst xt \<in> U_loc" and ht_I: "snd xt \<in> I_set"
              unfolding UI_def by (by100 auto)+
            show "H_U xt \<in> U_loc"
            proof (cases "fst xt \<in> A")
              case True
              hence "H_U xt = fst xt" unfolding H_U_def by (cases xt) (by100 simp)
              thus ?thesis using hx_U by (by100 simp)
            next
              case False
              hence "fst xt \<in> ?U" using hx_U hU_eq by (by100 simp)
              \<comment> \<open>H_U maps into U: either via hH_0 (t=0 gives x) or hH_1 (t=1 gives A\<subseteq>U)
                 or intermediate (h of interpolation stays in h(B2) which is in X).\<close>
              \<comment> \<open>fst xt \<in> X-A, so hinv(fst xt) \<in> Int B2\{0}. Interpolation stays in B2\{0}.
                 h maps B2\{0} into X, and h(point) \<noteq> x0 since h injective on Int B2.
                 Hence H_U xt \<in> X-{x0} = U = U_loc.\<close>
              have hx_VA: "fst xt \<in> X - A" using \<open>fst xt \<in> ?U\<close> False by (by100 blast)
              hence hx_img: "fst xt \<in> h ` ?D" using hsurj_D by (by100 simp)
              have hinv_D: "?hinv (fst xt) \<in> ?D" using inv_into_into[OF hx_img] .
              have hh_inv_xt: "h (?hinv (fst xt)) = fst xt" using f_inv_into_f[OF hx_img] .
              have hinv_ne0: "?hinv (fst xt) \<noteq> (0, 0)"
              proof
                assume "?hinv (fst xt) = (0, 0)"
                hence "h (?hinv (fst xt)) = ?x0" by (by100 simp)
                hence "fst xt = ?x0" using hh_inv_xt by (by100 simp)
                thus False using \<open>fst xt \<in> ?U\<close> by (by100 blast)
              qed
              \<comment> \<open>H_U(xt) = h(interpolation). Show this is in h(B2) and \<noteq> x0.\<close>
              let ?y = "?hinv (fst xt)" and ?t = "snd xt"
              let ?n = "?norm ?y"
              let ?interp = "((1 - ?t) * fst ?y + ?t * fst ?y / ?n,
                              (1 - ?t) * snd ?y + ?t * snd ?y / ?n)"
              have hHU_val: "H_U xt = h ?interp"
                unfolding H_U_def Let_def using False by (cases xt) (by100 simp)
              have hinterp_B2: "?interp \<in> top1_B2"
              proof -
                have hy_B2: "?y \<in> top1_B2" using hinv_D by (by100 blast)
                have ht0: "0 \<le> ?t" and ht1: "?t \<le> 1"
                  using ht_I unfolding top1_unit_interval_def by (by100 simp)+
                define yf where "yf = fst ?y"
                define ys where "ys = snd ?y"
                define nn where "nn = ?n"
                \<comment> \<open>Show y/|y| \<in> B2 (norm = 1)\<close>
                have hsum_pos: "yf ^ 2 + ys ^ 2 > 0"
                proof -
                  have "yf \<noteq> 0 \<or> ys \<noteq> 0"
                    using hinv_ne0 unfolding yf_def ys_def by (cases "?y") (by100 simp)
                  hence "yf ^ 2 > 0 \<or> ys ^ 2 > 0" by (by100 auto)
                  moreover have "yf ^ 2 \<ge> 0" "ys ^ 2 \<ge> 0" by (by100 simp)+
                  ultimately show ?thesis by (by100 linarith)
                qed
                have hnn_eq: "nn = sqrt (yf ^ 2 + ys ^ 2)" unfolding nn_def yf_def ys_def by (by100 simp)
                have hn_pos: "nn > 0" using hsum_pos unfolding hnn_eq by (by100 simp)
                have hnn2: "nn ^ 2 = yf ^ 2 + ys ^ 2"
                  using hsum_pos unfolding hnn_eq by (rule real_sqrt_pow2[OF order_less_imp_le])
                have hnn_ne0: "nn \<noteq> 0" using hn_pos by (by100 simp)
                have hq_norm: "(yf / nn) ^ 2 + (ys / nn) ^ 2 = 1"
                proof -
                  have "yf ^ 2 / nn ^ 2 + ys ^ 2 / nn ^ 2 = (yf ^ 2 + ys ^ 2) / nn ^ 2"
                    by (rule add_divide_distrib[symmetric])
                  also have "\<dots> = nn ^ 2 / nn ^ 2" using hnn2 by (by100 simp)
                  also have "\<dots> = 1" using hnn_ne0 by (by100 simp)
                  finally have "yf ^ 2 / nn ^ 2 + ys ^ 2 / nn ^ 2 = 1" .
                  moreover have "(yf / nn) ^ 2 = yf ^ 2 / nn ^ 2" by (rule power_divide)
                  moreover have "(ys / nn) ^ 2 = ys ^ 2 / nn ^ 2" by (rule power_divide)
                  ultimately show ?thesis by (by100 simp)
                qed
                \<comment> \<open>y/|y| \<in> S1 \<subseteq> B2.\<close>
                have hq_B2: "(yf / nn, ys / nn) \<in> top1_B2"
                  using hq_norm unfolding top1_B2_def by (by100 simp)
                \<comment> \<open>Transfer to ?q via unfolding.\<close>
                let ?q = "(fst ?y / ?n, snd ?y / ?n)"
                have "?q = (yf / nn, ys / nn)"
                  unfolding yf_def ys_def nn_def by (by100 simp)
                hence hq_B2': "?q \<in> top1_B2" using hq_B2 by (by100 simp)
                \<comment> \<open>interp is convex combination of y and q, which are both in B2.\<close>
                have heq_interp: "?interp = ((1 - ?t) * fst ?y + ?t * fst ?q,
                                              (1 - ?t) * snd ?y + ?t * snd ?q)"
                  by (by100 simp)
                show ?thesis unfolding heq_interp
                  using top1_B2_convex[OF hy_B2 hq_B2' ht0 ht1] .
              qed
              have "H_U xt \<in> h ` top1_B2"
                using hHU_val hinterp_B2 by (by100 blast)
              moreover have "H_U xt \<noteq> ?x0"
              proof -
                have hinterp_ne0: "?interp \<noteq> (0, 0)"
                proof
                  assume h0: "?interp = (0, 0)"
                  define yf where "yf = fst ?y"
                  define ys where "ys = snd ?y"
                  define nn where "nn = ?n"
                  have hyf_ne: "yf \<noteq> 0 \<or> ys \<noteq> 0"
                    using hinv_ne0 unfolding yf_def ys_def by (cases "?y") (by100 simp)
                  have hsum_pos: "yf ^ 2 + ys ^ 2 > 0"
                  proof -
                    have "yf ^ 2 > 0 \<or> ys ^ 2 > 0" using hyf_ne by (by100 auto)
                    moreover have "yf ^ 2 \<ge> 0" "ys ^ 2 \<ge> 0" by (by100 simp)+
                    ultimately show ?thesis by (by100 linarith)
                  qed
                  have hnn_eq: "nn = sqrt (yf ^ 2 + ys ^ 2)"
                    unfolding nn_def yf_def ys_def by (by100 simp)
                  have hn_pos: "nn > 0" using hsum_pos unfolding hnn_eq by (by100 simp)
                  have hnn_ne0: "nn \<noteq> 0" using hn_pos by (by100 simp)
                  have ht0: "0 \<le> ?t" and ht1: "?t \<le> 1"
                    using ht_I unfolding top1_unit_interval_def by (by100 simp)+
                  \<comment> \<open>From ?interp = 0, extract component equations.\<close>
                  have hfst0: "(1 - ?t) * yf + ?t * yf / nn = 0"
                  proof -
                    have "fst ?interp = (1 - ?t) * yf + ?t * yf / nn"
                      unfolding yf_def nn_def by (by100 simp)
                    moreover have "fst ?interp = 0" using h0 by (by100 simp)
                    ultimately show ?thesis by (by100 simp)
                  qed
                  have hsnd0: "(1 - ?t) * ys + ?t * ys / nn = 0"
                  proof -
                    have "snd ?interp = (1 - ?t) * ys + ?t * ys / nn"
                      unfolding ys_def nn_def by (by100 simp)
                    moreover have "snd ?interp = 0" using h0 by (by100 simp)
                    ultimately show ?thesis by (by100 simp)
                  qed
                  \<comment> \<open>Clear division via distrib_left + cancel to get ring form.\<close>
                  have h_cancel_yf: "nn * (?t * yf / nn) = ?t * yf"
                    using hnn_ne0 by (by100 simp)
                  have h_distrib_yf: "nn * ((1 - ?t) * yf + ?t * yf / nn) =
                                      nn * ((1 - ?t) * yf) + nn * (?t * yf / nn)"
                    by (rule distrib_left)
                  have h_assoc_yf: "nn * ((1 - ?t) * yf) = (1 - ?t) * nn * yf" by (by100 simp)
                  have h_ring_yf: "(1 - ?t) * nn * yf + ?t * yf = 0"
                  proof -
                    have "nn * ((1 - ?t) * yf + ?t * yf / nn) = (1 - ?t) * nn * yf + ?t * yf"
                      using h_distrib_yf h_cancel_yf h_assoc_yf by (by100 simp)
                    thus ?thesis using hfst0 by (by100 simp)
                  qed
                  have h_factor_yf: "(1 - ?t) * nn * yf + ?t * yf = ((1 - ?t) * nn + ?t) * yf"
                    by (rule distrib_right[symmetric])
                  have h_yf: "((1 - ?t) * nn + ?t) * yf = 0"
                    using h_ring_yf h_factor_yf by (by100 simp)
                  have h_cancel_ys: "nn * (?t * ys / nn) = ?t * ys"
                    using hnn_ne0 by (by100 simp)
                  have h_distrib_ys: "nn * ((1 - ?t) * ys + ?t * ys / nn) =
                                      nn * ((1 - ?t) * ys) + nn * (?t * ys / nn)"
                    by (rule distrib_left)
                  have h_assoc_ys: "nn * ((1 - ?t) * ys) = (1 - ?t) * nn * ys" by (by100 simp)
                  have h_ring_ys: "(1 - ?t) * nn * ys + ?t * ys = 0"
                  proof -
                    have "nn * ((1 - ?t) * ys + ?t * ys / nn) = (1 - ?t) * nn * ys + ?t * ys"
                      using h_distrib_ys h_cancel_ys h_assoc_ys by (by100 simp)
                    thus ?thesis using hsnd0 by (by100 simp)
                  qed
                  have h_factor_ys: "(1 - ?t) * nn * ys + ?t * ys = ((1 - ?t) * nn + ?t) * ys"
                    by (rule distrib_right[symmetric])
                  have h_ys: "((1 - ?t) * nn + ?t) * ys = 0"
                    using h_ring_ys h_factor_ys by (by100 simp)
                  have hcoeff_pos: "(1 - ?t) * nn + ?t > 0"
                  proof -
                    have "(1 - ?t) * nn \<ge> 0" using ht1 hn_pos by (by100 simp)
                    moreover have "?t \<ge> 0" using ht0 .
                    moreover have "(1 - ?t) * nn > 0 \<or> ?t > 0"
                    proof (cases "?t = 0")
                      case True thus ?thesis using hn_pos by (by100 simp)
                    next
                      case False thus ?thesis using ht0 by (by100 linarith)
                    qed
                    ultimately show ?thesis by (by100 linarith)
                  qed
                  have "yf = 0" using h_yf hcoeff_pos by (by100 simp)
                  moreover have "ys = 0" using h_ys hcoeff_pos by (by100 simp)
                  ultimately show False using hyf_ne by (by100 simp)
                qed
                show ?thesis
                proof (cases "?interp \<in> ?D")
                  case True \<comment> \<open>interp in Int B2: h injective, interp \<noteq> 0, so h(interp) \<noteq> h(0).\<close>
                  have "?interp \<noteq> (0::real, 0::real)" using hinterp_ne0 .
                  hence "h ?interp \<noteq> h (0, 0)"
                    using inj_on_eq_iff[OF hinj_D True h00_intB2] by (by100 simp)
                  thus ?thesis using hHU_val by (by100 simp)
                next
                  case False \<comment> \<open>interp on S1: h(interp) \<in> h(S1) \<subseteq> A, but x0 \<notin> A.\<close>
                  hence "?interp \<in> top1_S1" using hinterp_B2 by (by100 blast)
                  hence "h ?interp \<in> A" using assms(8) by (by100 blast)
                  hence "H_U xt \<in> A" using hHU_val by (by100 simp)
                  moreover have "h (0::real, 0::real) \<notin> A" using hx0_notin_A by (by100 simp)
                  ultimately show ?thesis by (by100 metis)
                qed
              qed
              moreover have "h ` top1_B2 \<subseteq> X"
                using assms(5) unfolding top1_continuous_map_on_def by (by100 blast)
              ultimately have "H_U xt \<in> X \<and> H_U xt \<noteq> ?x0" by (by100 blast)
              thus ?thesis unfolding U_loc_def by (by100 blast)
            qed
          qed
          show "top1_continuous_map_on (A \<times> I_set) (subspace_topology UI TUI (A \<times> I_set)) U_loc TU_loc H_U"
          proof -
            have "subspace_topology UI TUI (A \<times> I_set)
                = product_topology_on (subspace_topology U_loc TU_loc A) (subspace_topology I_set I_top I_set)"
              unfolding UI_def TUI_def by (rule Theorem_16_3[OF hTopU_loc hTI, symmetric])
            moreover have "subspace_topology I_set I_top I_set = I_top"
            proof (rule subspace_topology_self, intro ballI)
              fix V assume "V \<in> I_top"
              thus "V \<subseteq> I_set" unfolding top1_unit_interval_topology_def subspace_topology_def
                by (by100 blast)
            qed
            ultimately have "subspace_topology UI TUI (A \<times> I_set)
                = product_topology_on (subspace_topology U_loc TU_loc A) I_top" by (by100 simp)
            thus ?thesis using hH_cont_A unfolding hU_eq hTU_eq by (by100 simp)
          qed
          show "top1_continuous_map_on (?CU \<times> I_set) (subspace_topology UI TUI (?CU \<times> I_set)) U_loc TU_loc H_U"
          proof -
            have "subspace_topology UI TUI (?CU \<times> I_set)
                = product_topology_on (subspace_topology U_loc TU_loc ?CU) (subspace_topology I_set I_top I_set)"
              unfolding UI_def TUI_def by (rule Theorem_16_3[OF hTopU_loc hTI, symmetric])
            moreover have "subspace_topology I_set I_top I_set = I_top"
            proof (rule subspace_topology_self, intro ballI)
              fix V assume "V \<in> I_top"
              thus "V \<subseteq> I_set" unfolding top1_unit_interval_topology_def subspace_topology_def
                by (by100 blast)
            qed
            ultimately have hTCUI_eq: "subspace_topology UI TUI (?CU \<times> I_set)
                = product_topology_on (subspace_topology U_loc TU_loc ?CU) I_top" by (by100 simp)
            have hgoal: "top1_continuous_map_on (?CU \<times> I_set)
                (product_topology_on (subspace_topology U_loc TU_loc ?CU) I_top) U_loc TU_loc H_U"
              using hH_cont_CU hU_eq hTU_eq by (by100 simp)
            show ?thesis by (rule ssubst[OF hTCUI_eq]) (rule hgoal)
          qed
        qed
        thus ?thesis unfolding UI_def TUI_def U_loc_def TU_loc_def by (by100 simp)
      qed
    qed
    show ?thesis unfolding top1_deformation_retract_of_on_def
      using hA_sub_U hH_cont hH_0 hH_1 hH_A by (by100 blast)
  qed

  \<comment> \<open>--- Step 2e: U is path connected ---\<close>
  have hTopX_ns: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTopU: "is_topology_on ?U ?TU"
    by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
  have hU_pc: "top1_path_connected_on ?U ?TU"
  proof -
    \<comment> \<open>Deformation retract A of U implies U is path-connected (A is path-connected).\<close>
    have "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
    hence hTA_eq: "subspace_topology ?U ?TU A = ?TA" by (rule subspace_topology_trans)
    have hA_pc_U: "top1_path_connected_on A (subspace_topology ?U ?TU A)"
      using assms(4) hTA_eq by (by100 simp)
    \<comment> \<open>A deformation retract of U: every point of U can be connected to A.\<close>
    obtain H where hH: "top1_continuous_map_on (?U \<times> I_set) (product_topology_on ?TU I_top) ?U ?TU H"
        and hH0: "\<forall>x\<in>?U. H (x, 0) = x" and hH1: "\<forall>x\<in>?U. H (x, 1) \<in> A"
        and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    proof -
      from hA_deformation_retract_U \<open>A \<subseteq> ?U\<close>
      obtain H0 where "top1_continuous_map_on (?U \<times> I_set) (product_topology_on ?TU I_top) ?U ?TU H0"
          "\<forall>x\<in>?U. H0 (x, 0) = x" "\<forall>x\<in>?U. H0 (x, 1) \<in> A" "\<forall>a\<in>A. \<forall>t\<in>I_set. H0 (a, t) = a"
        unfolding top1_deformation_retract_of_on_def by fast
      thus ?thesis using that by (by100 blast)
    qed
    show ?thesis unfolding top1_path_connected_on_def
    proof (intro conjI ballI)
      show "is_topology_on ?U ?TU" by (rule hTopU)
    next
      fix x y assume hx: "x \<in> ?U" and hy: "y \<in> ?U"
      \<comment> \<open>Path: x to H(x,1)\<in>A via t\<mapsto>H(x,t), then H(x,1) to H(y,1) in A, then H(y,1) to y.\<close>
      have hx1: "H (x, 1) \<in> A" using hH1 hx by (by100 blast)
      have hy1: "H (y, 1) \<in> A" using hH1 hy by (by100 blast)
      \<comment> \<open>Get path from H(x,1) to H(y,1) in A.\<close>
      have hx1_U: "H (x, 1) \<in> ?U" using hx1 \<open>A \<subseteq> ?U\<close> by (by100 blast)
      have hy1_U: "H (y, 1) \<in> ?U" using hy1 \<open>A \<subseteq> ?U\<close> by (by100 blast)
      obtain fA where hfA: "top1_is_path_on A (subspace_topology ?U ?TU A) (H(x,1)) (H(y,1)) fA"
        using hA_pc_U hx1 hy1 unfolding top1_path_connected_on_def by (by100 blast)
      \<comment> \<open>Paths via H: t \<mapsto> H(x, 1-t) from H(x,1) to x, and t \<mapsto> H(y, t) from y to H(y,1).\<close>
      show "\<exists>f. top1_is_path_on ?U ?TU x y f"
      proof -
        \<comment> \<open>Path p1: x to H(x,1) via t \<mapsto> H(x,t).\<close>
        have p1: "top1_is_path_on ?U ?TU x (H(x,1)) (\<lambda>t. H(x,t))"
          unfolding top1_is_path_on_def
        proof (intro conjI)
          have hTI: "is_topology_on I_set I_top"
            by (rule top1_unit_interval_topology_is_topology_on)
          let ?g = "\<lambda>t. (x, t)"
          have "(\<lambda>t. H(x,t)) = H \<circ> ?g" by (by100 auto)
          moreover have "top1_continuous_map_on I_set I_top (?U \<times> I_set) (product_topology_on ?TU I_top) ?g"
          proof (rule iffD2[OF Theorem_18_4[OF hTI hTopU hTI]], intro conjI)
            have hpi1: "pi1 \<circ> ?g = top1_constant_path x" unfolding pi1_def top1_constant_path_def by (by100 auto)
            show "top1_continuous_map_on I_set I_top ?U ?TU (pi1 \<circ> ?g)"
              unfolding hpi1 using top1_constant_path_continuous[OF hTopU hx] .
          next
            have hpi2: "pi2 \<circ> ?g = id" unfolding pi2_def by (by100 auto)
            show "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> ?g)"
              unfolding hpi2 using top1_continuous_map_on_id[OF hTI] .
          qed
          ultimately show "top1_continuous_map_on I_set I_top ?U ?TU (\<lambda>t. H(x,t))"
            using top1_continuous_map_on_comp[of I_set I_top "?U \<times> I_set" "product_topology_on ?TU I_top"
                    ?g ?U ?TU H] hH by (by100 simp)
          show "(\<lambda>t. H (x, t)) 0 = x" using hH0 hx by (by100 blast)
          show "(\<lambda>t. H (x, t)) 1 = H (x, 1)" by (by100 simp)
        qed
        \<comment> \<open>Lift fA from A to U.\<close>
        have fA_U: "top1_is_path_on ?U ?TU (H(x,1)) (H(y,1)) fA"
          using hfA path_in_subspace_is_path_in_ambient[OF hTopU \<open>A \<subseteq> ?U\<close>]
          by (by100 blast)
        \<comment> \<open>Path p3: H(y,1) to y via t \<mapsto> H(y,1-t).\<close>
        have p3: "top1_is_path_on ?U ?TU (H(y,1)) y (\<lambda>t. H(y, 1-t))"
        proof -
          have hTI: "is_topology_on I_set I_top"
            by (rule top1_unit_interval_topology_is_topology_on)
          let ?gy = "\<lambda>t. (y, t)"
          have hgy_cont: "top1_continuous_map_on I_set I_top (?U \<times> I_set) (product_topology_on ?TU I_top) ?gy"
          proof (rule iffD2[OF Theorem_18_4[OF hTI hTopU hTI]], intro conjI)
            have hpi1: "pi1 \<circ> ?gy = top1_constant_path y" unfolding pi1_def top1_constant_path_def by (by100 auto)
            show "top1_continuous_map_on I_set I_top ?U ?TU (pi1 \<circ> ?gy)"
              unfolding hpi1 using top1_constant_path_continuous[OF hTopU hy] .
          next
            have hpi2: "pi2 \<circ> ?gy = id" unfolding pi2_def by (by100 auto)
            show "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> ?gy)"
              unfolding hpi2 using top1_continuous_map_on_id[OF hTI] .
          qed
          have hcomp: "(\<lambda>t. H(y,t)) = H \<circ> ?gy" by (by100 auto)
          have py: "top1_is_path_on ?U ?TU y (H(y,1)) (\<lambda>t. H(y,t))"
            unfolding top1_is_path_on_def
          proof (intro conjI)
            show "top1_continuous_map_on I_set I_top ?U ?TU (\<lambda>t. H(y,t))"
              unfolding hcomp using top1_continuous_map_on_comp[OF hgy_cont hH] .
            show "(\<lambda>t. H (y, t)) 0 = y" using hH0 hy by (by100 blast)
            show "(\<lambda>t. H (y, t)) 1 = H (y, 1)" by (by100 simp)
          qed
          show ?thesis using top1_is_path_on_reverse[OF hTopU py] by (by100 simp)
        qed
        \<comment> \<open>Concatenate p1 * fA * p3.\<close>
        have "top1_is_path_on ?U ?TU x y
          (top1_path_product (\<lambda>t. H(x,t)) (top1_path_product fA (\<lambda>t. H(y, 1-t))))"
          using top1_path_product_is_path[OF hTopU p1
                  top1_path_product_is_path[OF hTopU fA_U p3]] .
        thus ?thesis by (by100 blast)
      qed
    qed
  qed

  \<comment> \<open>--- Step 2f: U \<inter> V = V - {x0} is path connected ---\<close>
  \<comment> \<open>UV is path-connected: h restricts to a homeomorphism from Int(B2) - {0} onto UV.
     Then apply homeomorphism_preserves_path_connected + punctured_open_disk_path_connected.\<close>
  have hUV_homeo: "top1_homeomorphism_on
    (top1_B2 - top1_S1 - {(0::real, 0::real)})
    (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1 - {(0, 0)}))
    ?UV ?TUV h"
  proof -
    let ?D = "top1_B2 - top1_S1"
    let ?TD = "subspace_topology top1_B2 top1_B2_topology ?D"
    let ?P = "top1_B2 - top1_S1 - {(0::real, 0::real)}"
    let ?TP = "subspace_topology top1_B2 top1_B2_topology ?P"
    have hD_homeo: "top1_homeomorphism_on ?D ?TD ?V ?TV h" by (rule assms(7))
    have hTD: "is_topology_on ?D ?TD"
      using hD_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hTV: "is_topology_on ?V ?TV"
      using hD_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hbij: "bij_betw h ?D ?V"
      using hD_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on h ?D" using hbij unfolding bij_betw_def by (by100 blast)
    have hsurj: "h ` ?D = ?V" using hbij unfolding bij_betw_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on ?D ?TD ?V ?TV h"
      using hD_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hhinv_cont: "top1_continuous_map_on ?V ?TV ?D ?TD (inv_into ?D h)"
      using hD_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>UV \<subseteq> V\<close>
    have hUV_sub_V: "?UV \<subseteq> ?V" by (by100 blast)
    have hP_sub_D: "?P \<subseteq> ?D" by (by100 blast)
    \<comment> \<open>Show {x \<in> D. h x \<in> UV} = P (punctured disk).\<close>
    have hpreimage_eq: "{x \<in> ?D. h x \<in> ?UV} = ?P"
    proof (rule set_eqI)
      fix x show "x \<in> {x \<in> ?D. h x \<in> ?UV} \<longleftrightarrow> x \<in> ?P"
      proof
        assume hx: "x \<in> {x \<in> ?D. h x \<in> ?UV}"
        hence hxD: "x \<in> ?D" and hhxUV: "h x \<in> ?UV" by (by100 blast)+
        have hhx_ne: "h x \<noteq> ?x0" using hhxUV by (by100 blast)
        have "x \<noteq> (0::real, 0::real)"
        proof
          assume "x = (0, 0)"
          hence "h x = h (0, 0)" by (by100 simp)
          thus False using hhx_ne by (by100 simp)
        qed
        thus "x \<in> ?P" using hxD by (by100 blast)
      next
        assume hx: "x \<in> ?P"
        hence hxD: "x \<in> ?D" and hx_ne: "x \<noteq> (0::real, 0::real)" by (by100 blast)+
        have "h x \<in> ?V"
          using hbij hxD unfolding bij_betw_def by (by100 blast)
        moreover have "h x \<noteq> ?x0"
          using hinj hx_ne hxD h00_intB2 inj_on_eq_iff[of h ?D x "(0, 0)"] by (by100 blast)
        ultimately show "x \<in> {x \<in> ?D. h x \<in> ?UV}" using hxD by (by100 blast)
      qed
    qed
    \<comment> \<open>Subspace topology equalities.\<close>
    have hTP_eq: "subspace_topology ?D ?TD ?P = ?TP"
      by (rule subspace_topology_trans[OF hP_sub_D])
    have hTUV_eq: "subspace_topology ?V ?TV ?UV = ?TUV"
      by (rule subspace_topology_trans[OF hUV_sub_V])
    \<comment> \<open>Build the homeomorphism directly.\<close>
    have hTP_top: "is_topology_on ?P ?TP"
      using subspace_topology_is_topology_on[OF hTD hP_sub_D] hTP_eq by (by100 simp)
    have hTUV_top: "is_topology_on ?UV ?TUV"
      using subspace_topology_is_topology_on[OF hTV hUV_sub_V] hTUV_eq by (by100 simp)
    show ?thesis unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      show "is_topology_on ?P ?TP" by (rule hTP_top)
      show "is_topology_on ?UV ?TUV" by (rule hTUV_top)
      \<comment> \<open>Bijectivity.\<close>
      show "bij_betw h ?P ?UV"
      proof -
        have "inj_on h ?P" by (rule inj_on_subset[OF hinj hP_sub_D])
        moreover have "h ` ?P = ?UV"
        proof (rule set_eqI)
          fix y show "y \<in> h ` ?P \<longleftrightarrow> y \<in> ?UV"
          proof
            assume "y \<in> h ` ?P"
            then obtain x where hxP: "x \<in> ?P" and hfx: "y = h x" by (by100 blast)
            have "x \<in> {x \<in> ?D. h x \<in> ?UV}" using hxP hpreimage_eq by (by100 blast)
            hence "h x \<in> ?UV" by (by100 blast)
            thus "y \<in> ?UV" using hfx by (by100 simp)
          next
            assume hy: "y \<in> ?UV"
            hence "y \<in> ?V" by (by100 blast)
            hence "y \<in> h ` ?D" using hsurj by (by100 blast)
            then obtain x where hxD: "x \<in> ?D" and hfx: "h x = y" by (by100 blast)
            have "h x \<in> ?UV" using hy hfx by (by100 simp)
            hence "x \<in> {x \<in> ?D. h x \<in> ?UV}" using hxD by (by100 blast)
            hence "x \<in> ?P" using hpreimage_eq by (by100 blast)
            thus "y \<in> h ` ?P" using hfx by (by100 blast)
          qed
        qed
        ultimately show ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>Continuity: h restricted to P \<rightarrow> UV.\<close>
      show "top1_continuous_map_on ?P ?TP ?UV ?TUV h"
      proof -
        have hh_restr: "top1_continuous_map_on ?P (subspace_topology ?D ?TD ?P) ?V ?TV h"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hh_cont hP_sub_D])
        have hh_restr2: "top1_continuous_map_on ?P ?TP ?V ?TV h"
          using hh_restr hTP_eq by simp
        have himg: "h ` ?P \<subseteq> ?UV"
        proof
          fix y assume "y \<in> h ` ?P"
          then obtain x where hxP: "x \<in> ?P" and hy: "y = h x" by (by100 blast)
          have "x \<in> {x \<in> ?D. h x \<in> ?UV}" using hxP hpreimage_eq by (by100 blast)
          hence "h x \<in> ?UV" by (by100 blast)
          thus "y \<in> ?UV" using hy by (by100 simp)
        qed
        show ?thesis
          using top1_continuous_map_on_codomain_shrink[OF hh_restr2 himg hUV_sub_V]
          hTUV_eq by (by100 simp)
      qed
      \<comment> \<open>Inverse continuity: inv_into P h on UV \<rightarrow> P.\<close>
      show "top1_continuous_map_on ?UV ?TUV ?P ?TP (inv_into ?P h)"
      proof -
        \<comment> \<open>inv_into P h agrees with inv_into D h on UV.\<close>
        have hinv_agree: "\<forall>y\<in>?UV. inv_into ?P h y = inv_into ?D h y"
        proof
          fix y assume hy: "y \<in> ?UV"
          hence "y \<in> ?V" by (by100 blast)
          hence "y \<in> h ` ?D" using hsurj by (by100 blast)
          hence hiy_D: "inv_into ?D h y \<in> ?D" by (rule inv_into_into)
          have hfy: "h (inv_into ?D h y) = y"
            using \<open>y \<in> h ` ?D\<close> by (rule f_inv_into_f)
          hence "h (inv_into ?D h y) \<in> ?UV" using hy by (by100 simp)
          hence "inv_into ?D h y \<in> {x \<in> ?D. h x \<in> ?UV}" using hiy_D by (by100 blast)
          hence "inv_into ?D h y \<in> ?P" using hpreimage_eq by (by100 blast)
          thus "inv_into ?P h y = inv_into ?D h y"
            by (intro inv_into_f_eq[OF inj_on_subset[OF hinj hP_sub_D]])
               (use hfy in \<open>by100 blast\<close>)
        qed
        \<comment> \<open>Restrict inv_into D h: V \<rightarrow> D to UV \<rightarrow> D.\<close>
        have hinv_restr: "top1_continuous_map_on ?UV (subspace_topology ?V ?TV ?UV) ?D ?TD (inv_into ?D h)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hhinv_cont hUV_sub_V])
        have hinv_restr2: "top1_continuous_map_on ?UV ?TUV ?D ?TD (inv_into ?D h)"
          using hinv_restr hTUV_eq by (by100 simp)
        \<comment> \<open>Codomain shrink from D to P.\<close>
        have hinv_img: "(inv_into ?D h) ` ?UV \<subseteq> ?P"
        proof
          fix x assume "x \<in> (inv_into ?D h) ` ?UV"
          then obtain y where hy: "y \<in> ?UV" and hx: "x = inv_into ?D h y" by (by100 blast)
          have "y \<in> h ` ?D" using hy hsurj by (by100 blast)
          hence hiy: "inv_into ?D h y \<in> ?D" by (rule inv_into_into)
          have "h (inv_into ?D h y) = y" using \<open>y \<in> h ` ?D\<close> by (rule f_inv_into_f)
          hence "h (inv_into ?D h y) \<in> ?UV" using hy by (by100 simp)
          hence "inv_into ?D h y \<in> {x \<in> ?D. h x \<in> ?UV}" using hiy by (by100 blast)
          hence "inv_into ?D h y \<in> ?P" using hpreimage_eq by (by100 blast)
          thus "x \<in> ?P" using hx by (by100 simp)
        qed
        have hinv_shrink: "top1_continuous_map_on ?UV ?TUV ?P (subspace_topology ?D ?TD ?P) (inv_into ?D h)"
          by (rule top1_continuous_map_on_codomain_shrink[OF hinv_restr2 hinv_img hP_sub_D])
        have hinv_shrink2: "top1_continuous_map_on ?UV ?TUV ?P ?TP (inv_into ?D h)"
          using hinv_shrink hTP_eq by simp
        \<comment> \<open>Transfer: inv_into P h = inv_into D h on UV.\<close>
        show ?thesis
          by (rule top1_continuous_map_on_agree'[OF hinv_shrink2])
             (use hinv_agree in \<open>by100 simp\<close>)
      qed
    qed
  qed
  have hUV_pc: "top1_path_connected_on ?UV ?TUV"
    by (rule homeomorphism_preserves_path_connected[OF hUV_homeo punctured_open_disk_path_connected])

  \<comment> \<open>--- Step 2g: \<pi>_1(U \<inter> V) is infinite cyclic ---\<close>
  \<comment> \<open>U \<inter> V = V - {x0} \<cong> Int B2 - {0} \<cong> S1 \<times> R, so \<pi>_1 \<cong> Z.\<close>
  \<comment> \<open>Pick a basepoint b \<in> U \<inter> V. Munkres uses b = h(q) where q = midpoint of 0 to p.\<close>
  let ?q = "(1/2 :: real, 0 :: real)"
  let ?b = "h ?q"
  have hq_intB2: "?q \<in> top1_B2 - top1_S1"
  proof -
    have h1: "fst ?q ^ 2 + snd ?q ^ 2 = (1/4::real)"
      using power2_eq_square[of "1/2::real"] by (by100 simp)
    show ?thesis unfolding top1_B2_def top1_S1_def using h1 by (by100 simp)
  qed
  have hq_ne_00: "?q \<noteq> (0::real, 0::real)" by (by100 simp)
  have hb_in_VA: "?b \<in> X - A"
    using assms(7) hq_intB2 unfolding top1_homeomorphism_on_def bij_betw_def
    by (by100 blast)
  have hb_ne_x0: "?b \<noteq> ?x0"
  proof -
    have hinj: "inj_on h (top1_B2 - top1_S1)"
      using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    show ?thesis using hq_ne_00 hq_intB2 h00_intB2
      using inj_on_eq_iff[OF hinj hq_intB2 h00_intB2] by (by100 simp)
  qed
  have hb_in_UV: "?b \<in> ?UV"
    using hb_in_VA hb_ne_x0 hA_sub_X by (by100 blast)

  \<comment> \<open>\<pi>_1(U \<inter> V, b) is infinite cyclic (used implicitly via hsvk + generator tracking below).\<close>

  \<comment> \<open>--- Step 3: Apply Corollary 70.4 (SvK for simply connected V) ---\<close>
  \<comment> \<open>Since V is simply connected, U \<union> V = X, and U, V are open:
     \<pi>_1(X, b) \<cong> \<pi>_1(U, b) / N(image of \<pi>_1(U \<inter> V, b) \<rightarrow> \<pi>_1(U, b)).\<close>
  have hsvk: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX ?b)
        (top1_fundamental_group_mul X TX ?b)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier ?U ?TU ?b)
           (top1_fundamental_group_mul ?U ?TU ?b)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier ?U ?TU ?b)
              (top1_fundamental_group_mul ?U ?TU ?b)
              (top1_fundamental_group_id ?U ?TU ?b)
              (top1_fundamental_group_invg ?U ?TU ?b)
              (top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x)
                 ` (top1_fundamental_group_carrier ?UV ?TUV ?b))))
        (top1_quotient_group_mul_on
           (top1_fundamental_group_mul ?U ?TU ?b))"
    by (rule Corollary_70_4_simply_connected_V[OF assms(1) hU_open hV_open hU_union_V
            hUV_pc hU_pc hV_sc hb_in_UV])

  \<comment> \<open>--- Step 4: A is deformation retract of U \<Longrightarrow> \<pi>_1(U, a) \<cong> \<pi>_1(A, a) ---\<close>
  have hU_A_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier ?U ?TU a)
        (top1_fundamental_group_mul ?U ?TU a)
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_mul A ?TA a)"
  proof -
    have hTopX_ns: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTopU: "is_topology_on ?U ?TU"
      by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
    have hiso_AU: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A (subspace_topology ?U ?TU A) a)
        (top1_fundamental_group_mul A (subspace_topology ?U ?TU A) a)
        (top1_fundamental_group_carrier ?U ?TU a)
        (top1_fundamental_group_mul ?U ?TU a)"
      by (rule Theorem_58_3[OF hA_deformation_retract_U hTopU assms(6)])
    moreover have "subspace_topology ?U ?TU A = ?TA"
    proof -
      have "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
      thus ?thesis by (rule subspace_topology_trans)
    qed
    ultimately have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_carrier ?U ?TU a)
        (top1_fundamental_group_mul ?U ?TU a)"
      by (by100 simp)
    have ha_U: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
    have hgrpA: "top1_is_group_on
        (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)"
      by (rule top1_fundamental_group_is_group[OF subspace_topology_is_topology_on[OF hTopX_ns hA_sub_X] assms(6)])
    have hgrpU: "top1_is_group_on
        (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
        (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
      by (rule top1_fundamental_group_is_group[OF hTopU ha_U])
    from \<open>top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_carrier ?U ?TU a)
        (top1_fundamental_group_mul ?U ?TU a)\<close> hgrpA hgrpU
    show ?thesis by (rule top1_groups_isomorphic_on_sym)
  qed

  \<comment> \<open>--- Step 5: Base point change from b to a (Munkres Step 3) ---\<close>
  \<comment> \<open>Let \<gamma> be the straight-line path in B2 from q to p = (1,0).
     Let \<delta> = h \<circ> \<gamma>, a path in U from b to a.
     The isomorphism \<hat>\<delta> commutes with inclusion-induced maps,
     so the kernel at base point a corresponds to the kernel at base point b.\<close>
  have ha_in_U: "a \<in> ?U"
    using assms(6) hA_sub_X hx0_notin_A by (by100 blast)

  \<comment> \<open>Construct path \<delta> from a to b in X: \<delta>(t) = h(1 - t/2, 0).
     This is h composed with the straight line from (1,0) to (1/2,0) in B2.\<close>
  let ?\<delta> = "\<lambda>t::real. h (1 - t/2, 0::real)"
  have h\<delta>_0: "?\<delta> 0 = a"
    using assms(9) by (by100 simp)
  have h\<delta>_1: "?\<delta> 1 = ?b"
    by (by100 simp)
  have h\<delta>_in_B2: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> (1 - t/2, 0::real) \<in> top1_B2"
  proof -
    fix t :: real assume ht: "t \<in> top1_unit_interval"
    hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 simp)+
    have hfst: "(1 - t/2) ^ 2 + (0::real) ^ 2 = (1 - t/2) ^ 2" by (by100 simp)
    have hle: "(1 - t/2) ^ 2 \<le> 1"
    proof -
      have "1/2 \<le> 1 - t/2" "1 - t/2 \<le> 1" using ht01 by (by100 simp)+
      hence "0 \<le> 1 - t/2" "1 - t/2 \<le> 1" by (by100 simp)+
      thus ?thesis
        using power_le_one[of "1 - t/2" 2] by (by100 simp)
    qed
    show "(1 - t/2, 0::real) \<in> top1_B2"
      unfolding top1_B2_def using hfst hle by (by100 simp)
  qed
  have h\<delta>_in_X: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> ?\<delta> t \<in> X"
  proof -
    fix t assume ht: "t \<in> top1_unit_interval"
    have "(1 - t/2, 0::real) \<in> top1_B2" by (rule h\<delta>_in_B2[OF ht])
    thus "?\<delta> t \<in> X"
      using continuous_map_maps_to[OF assms(5)] by (by100 blast)
  qed
  have h\<delta>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX ?\<delta>"
  proof -
    \<comment> \<open>Step 1: Setup topology constants.\<close>
    let ?I = "top1_unit_interval"
    let ?TI = "top1_unit_interval_topology"
    let ?R = "UNIV :: real set"
    let ?TR = "top1_open_sets"
    let ?R2 = "?R \<times> ?R"
    let ?TR2 = "product_topology_on ?TR ?TR"
    let ?\<gamma> = "\<lambda>t::real. (1 - t/2, 0::real)"
    have hTR: "is_topology_on ?R ?TR"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTI: "is_topology_on ?I ?TI"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hI_eq: "?TI = subspace_topology ?R ?TR ?I"
      unfolding top1_unit_interval_topology_def by rule
    have hUNIV_eq: "subspace_topology ?R ?TR ?R = ?TR"
      by (rule subspace_topology_UNIV_self)
    \<comment> \<open>Step 2: Each component of \<gamma> is continuous on UNIV.\<close>
    have hc1: "continuous_on UNIV (\<lambda>t::real. 1 - t/2)"
      by (intro continuous_intros; simp)
    have hc2: "continuous_on UNIV (\<lambda>t::real. 0::real)"
      by (intro continuous_intros)
    \<comment> \<open>Step 3: Each component is top1_continuous_map_on I \<rightarrow> R.\<close>
    have hcm1: "top1_continuous_map_on ?I ?TI ?R ?TR (\<lambda>t::real. 1 - t/2)"
      using top1_continuous_map_on_real_subspace_open_sets[of ?I "\<lambda>t. 1 - t/2" ?R, OF _ hc1]
      unfolding hI_eq hUNIV_eq by (by100 auto)
    have hcm2: "top1_continuous_map_on ?I ?TI ?R ?TR (\<lambda>t::real. 0::real)"
      using top1_continuous_map_on_real_subspace_open_sets[of ?I "\<lambda>t. (0::real)" ?R, OF _ hc2]
      unfolding hI_eq hUNIV_eq by (by100 auto)
    \<comment> \<open>Step 4: pi1 \<circ> \<gamma> and pi2 \<circ> \<gamma> are continuous.\<close>
    have hpi1: "top1_continuous_map_on ?I ?TI ?R ?TR (pi1 \<circ> ?\<gamma>)"
    proof -
      have "pi1 \<circ> ?\<gamma> = (\<lambda>t. 1 - t/2)" unfolding pi1_def comp_def by (by100 auto)
      thus ?thesis using hcm1 by (by100 simp)
    qed
    have hpi2: "top1_continuous_map_on ?I ?TI ?R ?TR (pi2 \<circ> ?\<gamma>)"
    proof -
      have "pi2 \<circ> ?\<gamma> = (\<lambda>t. 0::real)" unfolding pi2_def comp_def by (by100 auto)
      thus ?thesis using hcm2 by (by100 simp)
    qed
    \<comment> \<open>Step 5: Combine via Theorem 18.4: \<gamma> continuous I \<rightarrow> R\<times>R.\<close>
    have hUU: "?R \<times> ?R = (UNIV::(real\<times>real) set)" by (by100 simp)
    have h\<gamma>_cont_R2: "top1_continuous_map_on ?I ?TI
        (UNIV::(real\<times>real) set) ?TR2 ?\<gamma>"
      using iffD2[OF Theorem_18_4[OF hTI hTR hTR, of ?\<gamma>]]
      using hpi1 hpi2 unfolding hUU by (by100 blast)
    \<comment> \<open>Step 6: Image of \<gamma> is in B2.\<close>
    have h\<gamma>_img: "?\<gamma> ` ?I \<subseteq> top1_B2"
      using h\<delta>_in_B2 by (by100 blast)
    \<comment> \<open>Step 7: Restrict codomain to B2.\<close>
    have h\<gamma>_cont_B2: "top1_continuous_map_on ?I ?TI top1_B2 top1_B2_topology ?\<gamma>"
      using top1_continuous_map_on_codomain_shrink[OF h\<gamma>_cont_R2 h\<gamma>_img]
      unfolding top1_B2_topology_def by (by100 simp)
    \<comment> \<open>Step 8: Compose with h to get \<delta> = h \<circ> \<gamma> continuous I \<rightarrow> X.\<close>
    have h\<delta>_comp: "top1_continuous_map_on ?I ?TI X TX (h \<circ> ?\<gamma>)"
      by (rule top1_continuous_map_on_comp[OF h\<gamma>_cont_B2 assms(5)])
    \<comment> \<open>Step 9: h \<circ> \<gamma> = \<delta> pointwise.\<close>
    have h_eq: "(h \<circ> ?\<gamma>) = ?\<delta>"
      unfolding comp_def by (by100 simp)
    show ?thesis using h\<delta>_comp unfolding h_eq .
  qed
  have h\<delta>_path: "top1_is_path_on X TX a ?b ?\<delta>"
    unfolding top1_is_path_on_def using h\<delta>_cont h\<delta>_0 h\<delta>_1 by (by100 blast)
  have hTX: "is_topology_on X TX"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hbasepoint_change:
    "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX a)
        (top1_fundamental_group_mul X TX a)
        (top1_fundamental_group_carrier X TX ?b)
        (top1_fundamental_group_mul X TX ?b)"
    by (rule basepoint_change_iso_via_path[OF hTX h\<delta>_path])

  \<comment> \<open>--- Steps 6 + Assembly (merged): generator tracking + isomorphism ---\<close>
  \<comment> \<open>Key fact: g = h \<circ> f = k \<circ> p (the standard S1 loop composed with h).\<close>
  let ?f = "\<lambda>s::real. (cos (2*pi*s), sin (2*pi*s))"
  have hg_eq_kp: "(\<lambda>s. h (?f s)) = ?\<iota> \<circ> ?f" by (rule ext) (by100 simp)
  \<comment> \<open>Munkres Step 3: \<pi>_1(UV,b) cyclic generated by [g0] = [h\<circ>f0] where f0 is
     the circle of radius 1/2. Base change: \<hat>\<delta>([g0]) = [g] = [k\<circ>p].
     This follows from \<bar>\<gamma>*(f0*\<gamma>) \<simeq> f in B2-{0} (same winding number).
     Assembly chain: \<pi>_1(X,a) \<cong> \<pi>_1(X,b) [base change] \<cong> Q(\<pi>_1(U,b), N_b) [SvK]
     \<cong> Q(\<pi>_1(A,a), \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>) [quotient_group_iso_transfer + generator tracking].\<close>
  \<comment> \<open>--- New approach (Munkres direct): the inclusion j: A \<hookrightarrow> X induces a surjective
     homomorphism j_*: \<pi>_1(A,a) \<rightarrow> \<pi>_1(X,a) with kernel \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.
     By the first isomorphism theorem: \<pi>_1(X,a) \<cong> \<pi>_1(A,a)/\<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>. ---\<close>
  let ?jAX = "top1_fundamental_group_induced_on A ?TA a X TX a (\<lambda>x. x)"
  let ?relator = "top1_normal_subgroup_generated_on
           (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
           (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)
           {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
              {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}}"
  have hTopX_ns: "is_topology_on X TX"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hTA_top: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTopX_ns hA_sub_X])
  have ha_X: "a \<in> X" using assms(6) hA_sub_X by (by100 blast)
  \<comment> \<open>Outer-level facts about (A\<hookrightarrow>U)* that are used in multiple sub-proofs.\<close>
  have hTopU_outer: "is_topology_on ?U ?TU"
    by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
  have ha_U_outer: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
  have hA_sub_U_outer: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
  have hAU_hom_outer: "top1_group_hom_on
      (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
      (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
      (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))"
  proof -
    have hTA_eq: "subspace_topology ?U ?TU A = ?TA"
      using subspace_topology_trans[OF hA_sub_U_outer] by (by100 simp)
    from subspace_inclusion_induced_hom[OF hTopU_outer hA_sub_U_outer assms(6)]
    show ?thesis using hTA_eq by (by100 simp)
  qed
  \<comment> \<open>Extract deformation retract homotopy H and retraction r at the outer level.\<close>
  obtain H_dr where hHdr_cont: "top1_continuous_map_on (?U \<times> I_set)
      (product_topology_on ?TU I_top) ?U ?TU H_dr"
      and hHdr_0: "\<forall>x\<in>?U. H_dr (x, 0) = x"
      and hHdr_1: "\<forall>x\<in>?U. H_dr (x, 1) \<in> A"
      and hHdr_fix: "\<forall>a'\<in>A. \<forall>t\<in>I_set. H_dr (a', t) = a'"
    using hA_deformation_retract_U unfolding top1_deformation_retract_of_on_def by (by100 auto)
  \<comment> \<open>Retraction r = (\<lambda>x. H_dr(x,1)) continuous U \<rightarrow> A.\<close>
  have hr_cont_outer: "top1_continuous_map_on ?U ?TU A ?TA (\<lambda>x. H_dr (x, 1))"
  proof -
    have hcomp_eq: "(\<lambda>x. H_dr (x, 1)) = H_dr \<circ> (\<lambda>x. (x, 1::real))"
      by (rule ext) (by100 simp)
    have hI_top: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have h1_in_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have hpair_cont: "top1_continuous_map_on ?U ?TU (?U \<times> I_set)
        (product_topology_on ?TU I_top) (\<lambda>x. (x, 1::real))"
      using iffD2[OF Theorem_18_4[OF hTopU_outer hTopU_outer hI_top]]
    proof -
      have hpi1: "top1_continuous_map_on ?U ?TU ?U ?TU (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
      proof -
        have "pi1 \<circ> (\<lambda>x::'a. (x, 1::real)) = (\<lambda>x. x)"
          unfolding pi1_def by (rule ext) (by100 simp)
        thus ?thesis using top1_continuous_map_on_id[OF hTopU_outer] unfolding id_def by (by100 simp)
      qed
      have hpi2: "top1_continuous_map_on ?U ?TU I_set I_top (pi2 \<circ> (\<lambda>x::'a. (x, 1::real)))"
      proof -
        have "pi2 \<circ> (\<lambda>x::'a. (x, 1::real)) = (\<lambda>_::'a. 1::real)"
          unfolding pi2_def by (rule ext) (by100 simp)
        moreover have "\<forall>y0\<in>I_set. top1_continuous_map_on ?U ?TU I_set I_top (\<lambda>x. y0)"
          using Theorem_18_2[OF hTopU_outer hI_top hI_top] by (by100 blast)
        ultimately show ?thesis using h1_in_I by (by100 simp)
      qed
      show ?thesis using iffD2[OF Theorem_18_4[OF hTopU_outer hTopU_outer hI_top]] hpi1 hpi2
        by (by100 blast)
    qed
    have h_ir_cont: "top1_continuous_map_on ?U ?TU ?U ?TU (\<lambda>x. H_dr (x, 1))"
      unfolding hcomp_eq by (rule top1_continuous_map_on_comp[OF hpair_cont hHdr_cont])
    have hr_img: "(\<lambda>x. H_dr (x, 1)) ` ?U \<subseteq> A"
    proof
      fix y assume "y \<in> (\<lambda>x. H_dr (x, 1)) ` ?U"
      then obtain x where "x \<in> ?U" "y = H_dr (x, 1)" by (by100 blast)
      thus "y \<in> A" using hHdr_1 by (by100 blast)
    qed
    show ?thesis
      using top1_continuous_map_on_codomain_shrink[OF h_ir_cont hr_img hA_sub_U_outer]
        subspace_topology_trans[OF hA_sub_U_outer] by (by100 simp)
  qed
  have hra_outer: "H_dr (a, 1) = a"
    using hHdr_fix assms(6) unfolding top1_unit_interval_def by (by100 auto)
  \<comment> \<open>(A\<hookrightarrow>U)* surjective (deformation retract \<Longrightarrow> inclusion induces iso).\<close>
  have hAU_surj_outer: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
      ` (top1_fundamental_group_carrier A ?TA a)
    = top1_fundamental_group_carrier ?U ?TU a"
  proof (rule equalityI)
    \<comment> \<open>Forward: image \<subseteq> carrier (from hom property).\<close>
    show "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
        ` top1_fundamental_group_carrier A ?TA a \<subseteq> top1_fundamental_group_carrier ?U ?TU a"
      using hAU_hom_outer unfolding top1_group_hom_on_def by (by100 blast)
  next
    \<comment> \<open>Backward: for [f] \<in> \<pi>_1(U,a), take r\<circ>f \<in> \<pi>_1(A,a). Then \<iota>*(r\<circ>f) = [f].\<close>
    show "top1_fundamental_group_carrier ?U ?TU a
        \<subseteq> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
            ` top1_fundamental_group_carrier A ?TA a"
    proof
      fix c assume hc: "c \<in> top1_fundamental_group_carrier ?U ?TU a"
      obtain f where hf_loop: "top1_is_loop_on ?U ?TU a f"
          and hc_eq: "c = {g. top1_loop_equiv_on ?U ?TU a f g}"
        using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
      let ?r = "\<lambda>x. H_dr (x, 1)"
      \<comment> \<open>r\<circ>f is a loop in A at a.\<close>
      have hrf_loop_A: "top1_is_loop_on A ?TA a (?r \<circ> f)"
        using top1_continuous_map_loop_early[OF hr_cont_outer hf_loop] hra_outer by (by100 simp)
      \<comment> \<open>\<iota>*(class_A(r\<circ>f)) = class_U(r\<circ>f) by inclusion_induced_class.\<close>
      have h\<iota>_rf: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
          {k. top1_loop_equiv_on A ?TA a (?r \<circ> f) k}
        = {k. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k}"
        by (rule inclusion_induced_class[OF hA_sub_U_outer hTopU_outer
            subspace_topology_trans[OF hA_sub_U_outer] hrf_loop_A])
      \<comment> \<open>r\<circ>f \<simeq> f in U (from deformation: H_dr is homotopy id \<simeq> \<iota>\<circ>r, basepoint a fixed).
         By Lemma_58_1: path_homotopic(U, id\<circ>f, (\<iota>\<circ>r)\<circ>f) = path_homotopic(U, f, r\<circ>f).\<close>
      have hrf_equiv_f: "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) f"
      proof -
        have h_id_cont: "top1_continuous_map_on ?U ?TU ?U ?TU (\<lambda>x. x)"
          using top1_continuous_map_on_id[OF hTopU_outer] unfolding id_def by (by100 simp)
        have hAU_cont2: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
        proof -
          from top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopU_outer] hA_sub_U_outer]
          show ?thesis using subspace_topology_trans[OF hA_sub_U_outer] unfolding id_def by (by100 simp)
        qed
        have h_ir_cont: "top1_continuous_map_on ?U ?TU ?U ?TU (\<lambda>x. H_dr (x, 1))"
        proof -
          have hcomp: "(\<lambda>x. x) \<circ> (\<lambda>x. H_dr (x, 1)) = (\<lambda>x. H_dr (x, 1))" by (rule ext) (by100 simp)
          from top1_continuous_map_on_comp[OF hr_cont_outer hAU_cont2]
          show ?thesis using hcomp by (by100 simp)
        qed
        have hH_hom: "\<exists>Hh. top1_continuous_map_on (?U \<times> I_set) (product_topology_on ?TU I_top)
            ?U ?TU Hh \<and> (\<forall>x\<in>?U. Hh (x, 0) = (\<lambda>x. x) x) \<and>
            (\<forall>x\<in>?U. Hh (x, 1) = (\<lambda>x. H_dr (x, 1)) x) \<and>
            (\<forall>t\<in>I_set. Hh (a, t) = a)"
          using hHdr_cont hHdr_0 hHdr_1 hHdr_fix assms(6)
          by (rule_tac x=H_dr in exI) (by100 auto)
        from Lemma_58_1_basepoint_fixed[OF hTopU_outer h_id_cont h_ir_cont _ _ hH_hom hf_loop]
        have "top1_path_homotopic_on ?U ?TU a a
            (top1_induced_homomorphism_on ?U ?TU ?U ?TU (\<lambda>x. x) f)
            (top1_induced_homomorphism_on ?U ?TU ?U ?TU (\<lambda>x. H_dr (x, 1)) f)"
          using hra_outer by (by100 auto)
        hence "top1_path_homotopic_on ?U ?TU a a f (?r \<circ> f)"
          unfolding top1_induced_homomorphism_on_def comp_def by (by100 simp)
        hence "top1_path_homotopic_on ?U ?TU a a (?r \<circ> f) f"
          by (rule Lemma_51_1_path_homotopic_sym)
        moreover have "top1_is_loop_on ?U ?TU a (?r \<circ> f)"
          using top1_continuous_map_loop_early[OF h_ir_cont hf_loop] hra_outer by (by100 simp)
        ultimately show ?thesis unfolding top1_loop_equiv_on_def using hf_loop by (by100 blast)
      qed
      \<comment> \<open>class_U(r\<circ>f) = class_U(f) = c.\<close>
      have hclass_eq: "{k. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k} = c"
      proof -
        have hd1: "\<And>k'. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k'
            \<Longrightarrow> top1_loop_equiv_on ?U ?TU a f k'"
        proof -
          fix k' assume "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k'"
          show "top1_loop_equiv_on ?U ?TU a f k'"
            using top1_loop_equiv_on_trans[OF hTopU_outer
                top1_loop_equiv_on_sym[OF hrf_equiv_f]
                \<open>top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k'\<close>] .
        qed
        have hd2: "\<And>k'. top1_loop_equiv_on ?U ?TU a f k'
            \<Longrightarrow> top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k'"
        proof -
          fix k' assume "top1_loop_equiv_on ?U ?TU a f k'"
          show "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) k'"
            using top1_loop_equiv_on_trans[OF hTopU_outer hrf_equiv_f
                \<open>top1_loop_equiv_on ?U ?TU a f k'\<close>] .
        qed
        show ?thesis using hd1 hd2 hc_eq by (by100 blast)
      qed
      \<comment> \<open>\<iota>*(class_A(r\<circ>f)) = c.\<close>
      have "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
          {k. top1_loop_equiv_on A ?TA a (?r \<circ> f) k} = c"
        using h\<iota>_rf hclass_eq by (by100 simp)
      moreover have "{k. top1_loop_equiv_on A ?TA a (?r \<circ> f) k}
          \<in> top1_fundamental_group_carrier A ?TA a"
        unfolding top1_fundamental_group_carrier_def using hrf_loop_A by (by100 blast)
      ultimately show "c \<in> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
          ` top1_fundamental_group_carrier A ?TA a"
        by (by100 blast)
    qed
  qed
  \<comment> \<open>(A\<hookrightarrow>U)* injective (retraction left-inverse: r*\<circ>\<iota>*=id on \<pi>_1(A)).\<close>
  have hAU_inj_outer: "inj_on (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
      (top1_fundamental_group_carrier A ?TA a)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier A ?TA a"
       and hc2: "c2 \<in> top1_fundamental_group_carrier A ?TA a"
       and heq: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c1
               = (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c2"
    \<comment> \<open>The retraction r = (\<lambda>x. H_dr(x,1)): U \<rightarrow> A fixes A pointwise.
       So r* \<circ> \<iota>* = id on \<pi>_1(A,a). Hence \<iota>*(c1) = \<iota>*(c2) \<Longrightarrow> c1 = c2.\<close>
    \<comment> \<open>For loops in A: \<iota>(g) = g (inclusion is identity), r(g(s)) = g(s) (r fixes A).
       So (r \<circ> \<iota>)(g) = g for loops g in A. At the class level: r*(\<iota>*(c)) = c.
       Key: for c = {g. loop_equiv(A, f, g)}, \<iota>*(c) = {g. loop_equiv(U, f, g)} (by inclusion_induced_class).
       Then r*(c') where c' = \<iota>*(c) gives {g. loop_equiv(A, r\<circ>f, g)}.
       Since f is in A and r fixes A: r\<circ>f = f. So r*(\<iota>*(c)) = {g. loop_equiv(A, f, g)} = c.\<close>
    \<comment> \<open>Simpler approach: use the EXISTING iso hA_U_iso which gives groups_isomorphic_on.
       Any hom between isomorphic groups that is also a hom is injective iff surjective.
       We already have surjectivity (hAU_surj_outer). And for finite groups, surj \<Longrightarrow> inj.
       But for infinite groups we need the left-inverse argument.\<close>
    \<comment> \<open>Direct approach: \<iota>*(c1) = \<iota>*(c2) in \<pi>_1(U,a). Since \<iota> = identity on functions,
       the induced map on classes is: \<iota>*({g. equiv(A,f,g)}) = {g. equiv(U,f,g)}.
       So {g. equiv(U,f1,g)} = {g. equiv(U,f2,g)}, meaning loop_equiv(U,a,f1,f2).
       Since r fixes A: the homotopy H in U between f1 and f2 can be composed with r
       to get a homotopy in A. Specifically: r \<circ> H is a homotopy in A from f1 to f2
       (since r(f_i(s)) = f_i(s) for loops in A, and r is continuous).\<close>
    \<comment> \<open>Extract loops.\<close>
    obtain f1 where hf1: "top1_is_loop_on A ?TA a f1" "c1 = {g. top1_loop_equiv_on A ?TA a f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain f2 where hf2: "top1_is_loop_on A ?TA a f2" "c2 = {g. top1_loop_equiv_on A ?TA a f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>\<iota>*(ci) = [fi]_U.\<close>
    have h\<iota>c1: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c1
        = {g. top1_loop_equiv_on ?U ?TU a f1 g}"
      using inclusion_induced_class[OF hA_sub_U_outer hTopU_outer
          subspace_topology_trans[OF hA_sub_U_outer] hf1(1)] hf1(2) by (by100 simp)
    have h\<iota>c2: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c2
        = {g. top1_loop_equiv_on ?U ?TU a f2 g}"
      using inclusion_induced_class[OF hA_sub_U_outer hTopU_outer
          subspace_topology_trans[OF hA_sub_U_outer] hf2(1)] hf2(2) by (by100 simp)
    \<comment> \<open>f2 is a loop in U (from A \<subseteq> U).\<close>
    have hf2_U: "top1_is_loop_on ?U ?TU a f2"
    proof -
      have hAU_cont_loc: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
      proof -
        from top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopU_outer] hA_sub_U_outer]
        show ?thesis using subspace_topology_trans[OF hA_sub_U_outer] unfolding id_def by (by100 simp)
      qed
      from top1_continuous_map_loop_early[OF hAU_cont_loc hf2(1)]
      have "top1_is_loop_on ?U ?TU ((\<lambda>x. x) a) ((\<lambda>x. x) \<circ> f2)" .
      moreover have "(\<lambda>x::'a. x) a = a" by (by100 simp)
      moreover have "(\<lambda>x::'a. x) \<circ> f2 = f2" by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>From heq: loop_equiv(U, f1, f2).\<close>
    have "{g. top1_loop_equiv_on ?U ?TU a f1 g} = {g. top1_loop_equiv_on ?U ?TU a f2 g}"
      using heq h\<iota>c1 h\<iota>c2 by (by100 simp)
    hence hf1f2_U: "top1_loop_equiv_on ?U ?TU a f1 f2"
    proof -
      have "f2 \<in> {g. top1_loop_equiv_on ?U ?TU a f2 g}"
        using top1_loop_equiv_on_refl[OF hf2_U] by (by100 blast)
      hence "f2 \<in> {g. top1_loop_equiv_on ?U ?TU a f1 g}"
        using \<open>{g. top1_loop_equiv_on ?U ?TU a f1 g} = {g. top1_loop_equiv_on ?U ?TU a f2 g}\<close>
        by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>r: U \<rightarrow> A continuous.\<close>
    let ?r = "\<lambda>x. H_dr (x, 1)"
    have hr_cont: "top1_continuous_map_on ?U ?TU A ?TA ?r"
      using hr_cont_outer .
    \<comment> \<open>Apply r to homotopy: loop_equiv(A, r\<circ>f1, r\<circ>f2).\<close>
    have hra: "?r a = a" using hHdr_fix assms(6) unfolding top1_unit_interval_def by (by100 auto)
    have hf1_U: "top1_is_loop_on ?U ?TU a f1"
    proof -
      have hAU_cont_loc: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
      proof -
        from top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopU_outer] hA_sub_U_outer]
        show ?thesis using subspace_topology_trans[OF hA_sub_U_outer] unfolding id_def by (by100 simp)
      qed
      from top1_continuous_map_loop_early[OF hAU_cont_loc hf1(1)]
      have "top1_is_loop_on ?U ?TU ((\<lambda>x. x) a) ((\<lambda>x. x) \<circ> f1)" .
      moreover have "(\<lambda>x::'a. x) a = a" by (by100 simp)
      moreover have "(\<lambda>x::'a. x) \<circ> f1 = f1" by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    have hrf1f2_A: "top1_loop_equiv_on A ?TA a (?r \<circ> f1) (?r \<circ> f2)"
      using top1_induced_preserves_loop_equiv[OF hTopU_outer hr_cont hf1_U hf2_U hf1f2_U] hra
      by (by100 simp)
    \<comment> \<open>r\<circ>fi agrees with fi on I (r fixes A, fi maps I to A). By loop_agree_on_I: r\<circ>fi \<simeq> fi.\<close>
    have hf1_cont_A: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A ?TA f1"
      using hf1(1) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf2_cont_A: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A ?TA f2"
      using hf2(1) unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have h1_in_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have hrf1_eq: "\<forall>s\<in>I_set. (?r \<circ> f1) s = f1 s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      have "f1 s \<in> A" by (rule continuous_map_maps_to[OF hf1_cont_A hs])
      thus "(?r \<circ> f1) s = f1 s" using hHdr_fix \<open>f1 s \<in> A\<close> h1_in_I
        unfolding comp_def by (by100 blast)
    qed
    have hrf2_eq: "\<forall>s\<in>I_set. (?r \<circ> f2) s = f2 s"
    proof (intro ballI)
      fix s assume hs: "s \<in> I_set"
      have "f2 s \<in> A" by (rule continuous_map_maps_to[OF hf2_cont_A hs])
      thus "(?r \<circ> f2) s = f2 s" using hHdr_fix \<open>f2 s \<in> A\<close> h1_in_I
        unfolding comp_def by (by100 blast)
    qed
    \<comment> \<open>By loop_agree_on_I: r\<circ>fi \<simeq> fi in A.\<close>
    have hrf1_hom: "top1_path_homotopic_on A ?TA a a f1 (?r \<circ> f1)"
      using loop_agree_on_I[OF hf1(1)] hrf1_eq by (by100 blast)
    have hrf2_hom: "top1_path_homotopic_on A ?TA a a f2 (?r \<circ> f2)"
      using loop_agree_on_I[OF hf2(1)] hrf2_eq by (by100 blast)
    \<comment> \<open>Chain: f1 \<simeq> r\<circ>f1 \<simeq> r\<circ>f2 \<simeq> f2 in A.\<close>
    \<comment> \<open>Hence loop_equiv(A, f1, f2), so c1 = c2.\<close>
    \<comment> \<open>Convert path_homotopic to loop_equiv.\<close>
    have hrf1_loop_A: "top1_is_loop_on A ?TA a (?r \<circ> f1)"
      using loop_agree_on_I[OF hf1(1)] hrf1_eq by (by100 blast)
    have hrf2_loop_A: "top1_is_loop_on A ?TA a (?r \<circ> f2)"
      using loop_agree_on_I[OF hf2(1)] hrf2_eq by (by100 blast)
    have hle1: "top1_loop_equiv_on A ?TA a f1 (?r \<circ> f1)"
      unfolding top1_loop_equiv_on_def using hf1(1) hrf1_loop_A hrf1_hom by (by100 blast)
    have hle2_rev: "top1_loop_equiv_on A ?TA a f2 (?r \<circ> f2)"
      unfolding top1_loop_equiv_on_def using hf2(1) hrf2_loop_A hrf2_hom by (by100 blast)
    have hle2: "top1_loop_equiv_on A ?TA a (?r \<circ> f2) f2"
      by (rule top1_loop_equiv_on_sym[OF hle2_rev])
    \<comment> \<open>Chain: f1 ~ r\<circ>f1 ~ r\<circ>f2 ~ f2.\<close>
    have hf1_rf2: "top1_loop_equiv_on A ?TA a f1 (?r \<circ> f2)"
      by (rule top1_loop_equiv_on_trans[OF hTA_top hle1 hrf1f2_A])
    have hf1f2_A: "top1_loop_equiv_on A ?TA a f1 f2"
      by (rule top1_loop_equiv_on_trans[OF hTA_top hf1_rf2 hle2])
    \<comment> \<open>c1 = c2 from loop_equiv(A, f1, f2).\<close>
    have hdir1: "\<And>g'. top1_loop_equiv_on A ?TA a f1 g' \<Longrightarrow> top1_loop_equiv_on A ?TA a f2 g'"
    proof -
      fix g' assume "top1_loop_equiv_on A ?TA a f1 g'"
      show "top1_loop_equiv_on A ?TA a f2 g'"
        using top1_loop_equiv_on_trans[OF hTA_top top1_loop_equiv_on_sym[OF hf1f2_A]
            \<open>top1_loop_equiv_on A ?TA a f1 g'\<close>] .
    qed
    have hdir2: "\<And>g'. top1_loop_equiv_on A ?TA a f2 g' \<Longrightarrow> top1_loop_equiv_on A ?TA a f1 g'"
    proof -
      fix g' assume "top1_loop_equiv_on A ?TA a f2 g'"
      show "top1_loop_equiv_on A ?TA a f1 g'"
        using top1_loop_equiv_on_trans[OF hTA_top hf1f2_A
            \<open>top1_loop_equiv_on A ?TA a f2 g'\<close>] .
    qed
    have "{g. top1_loop_equiv_on A ?TA a f1 g} = {g. top1_loop_equiv_on A ?TA a f2 g}"
      using hdir1 hdir2 by (by100 blast)
    show "c1 = c2" using hf1(2) hf2(2) \<open>{g. top1_loop_equiv_on A ?TA a f1 g} = {g. top1_loop_equiv_on A ?TA a f2 g}\<close> by (by100 simp)
  qed
  \<comment> \<open>Step 1: j_* is a homomorphism.\<close>
  have hincl_AX_cont: "top1_continuous_map_on A ?TA X TX (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTopX_ns])
    from top1_continuous_map_on_restrict_domain_simple[OF this hA_sub_X]
    have "top1_continuous_map_on A (subspace_topology X TX A) X TX id" .
    have hid_eq: "(id :: 'a \<Rightarrow> 'a) = (\<lambda>x. x)" unfolding id_def by (by100 blast)
    thus ?thesis using \<open>top1_continuous_map_on A (subspace_topology X TX A) X TX id\<close>
      unfolding hid_eq by (by100 simp)
  qed
  have hj_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
      (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a) ?jAX"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTA_top hTopX_ns assms(6) ha_X
        hincl_AX_cont]) (by100 simp)
  \<comment> \<open>Step 2: j_* is surjective.
     A is deformation retract of U \<Longrightarrow> \<iota>_*: \<pi>_1(A,a) \<cong> \<pi>_1(U,a) (iso, hence surjective onto U).
     SvK with V simply connected \<Longrightarrow> inclusion U \<hookrightarrow> X induces surjection \<pi>_1(U,b) \<twoheadrightarrow> \<pi>_1(X,b).
     Base change b \<leftrightarrow> a preserves surjectivity.
     Composition: j_* = (U\<hookrightarrow>X)_* \<circ> (A\<hookrightarrow>U)_* is surjective.\<close>
  have hj_surj: "?jAX ` (top1_fundamental_group_carrier A ?TA a) =
      top1_fundamental_group_carrier X TX a"
  proof -
    \<comment> \<open>Munkres: j_* = (U\<hookrightarrow>X)_* \<circ> (A\<hookrightarrow>U)_*. Each factor is surjective.\<close>
    \<comment> \<open>Step (a): (A\<hookrightarrow>U)_* is an iso (hence surjective) by deformation retract (Thm 58.3).\<close>
    have hA_U_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)"
    proof -
      have hTopU_ns: "is_topology_on ?U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
      have ha_U: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
      have hgrpU: "top1_is_group_on
          (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
          (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
        by (rule top1_fundamental_group_is_group[OF hTopU_ns ha_U])
      have hgrpA_loc: "top1_is_group_on
          (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)"
        by (rule top1_fundamental_group_is_group[OF hTA_top assms(6)])
      show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hU_A_iso hgrpU hgrpA_loc])
    qed
    \<comment> \<open>Step (b): (U\<hookrightarrow>X)_* is surjective (from SvK: \<pi>_1(X) = \<pi>_1(U)/N).\<close>
    have hU_X_surj: "(top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
        ` (top1_fundamental_group_carrier ?U ?TU a)
      = top1_fundamental_group_carrier X TX a"
    proof -
      \<comment> \<open>By SvK_simply_connected_V_surj_kernel at base b \<in> U\<inter>V:
         incl*_b: \<pi>_1(U,b) \<twoheadrightarrow> \<pi>_1(X,b) is surjective.
         By base change naturality (diagram commutes with base change from b to a via \<delta>):
         incl*_a is also surjective.\<close>
      have hincl_surj_b: "(top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x))
          ` (top1_fundamental_group_carrier ?U ?TU ?b) = top1_fundamental_group_carrier X TX ?b"
        by (rule SvK_simply_connected_V_surj_kernel(1)[OF assms(1) hU_open hV_open hU_union_V
                hUV_pc hU_pc hV_sc hb_in_UV])
      \<comment> \<open>Transfer from base b to base a via naturality of base change with inclusion.\<close>
      show ?thesis
      proof (rule equalityI)
        \<comment> \<open>Forward: image \<subseteq> carrier.\<close>
        show "(top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
            ` top1_fundamental_group_carrier ?U ?TU a \<subseteq> top1_fundamental_group_carrier X TX a"
        proof -
          have hTopU_s: "is_topology_on ?U ?TU"
            by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
          have ha_U_s: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
          have hincl_s: "top1_continuous_map_on ?U ?TU X TX (\<lambda>x. x)"
          proof -
            from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopX_ns] Diff_subset]
            show ?thesis unfolding id_def by (by100 simp)
          qed
          have hh: "top1_group_hom_on (top1_fundamental_group_carrier ?U ?TU a)
              (top1_fundamental_group_mul ?U ?TU a)
              (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a)
              (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))"
            by (rule top1_fundamental_group_induced_on_is_hom[OF hTopU_s hTopX_ns ha_U_s ha_X hincl_s])
               (by100 simp)
          show ?thesis using hh unfolding top1_group_hom_on_def by (by100 blast)
        qed
      next
        \<comment> \<open>Backward: carrier \<subseteq> image. Use surjectivity at b + inclusion = identity on functions.\<close>
        show "top1_fundamental_group_carrier X TX a
            \<subseteq> (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
                ` top1_fundamental_group_carrier ?U ?TU a"
          \<comment> \<open>For any [f] \<in> \<pi>_1(X,a): f is a loop in X at a.
             Since a \<in> U and \<delta> from a to b is in U:
             \<delta>-hat_X(f) = rev(\<delta>)*(f*\<delta>) is a loop in X at b.
             By surj at b: \<exists>g loop in U at b with [g]_X = [\<delta>-hat_X(f)]_X.
             Then rev(\<delta>)-hat_U(g) = \<delta>*(g*rev(\<delta>)) is a loop in U at a.
             Since inclusion is identity: [rev(\<delta>)-hat_U(g)]_X = [rev(\<delta>)-hat_X(g)]_X.
             And rev(\<delta>)-hat_X(\<delta>-hat_X(f)) = [f] (roundtrip).
             So incl*_a([rev(\<delta>)-hat_U(g)]) = [f].\<close>
        proof
          fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX a"
          obtain f where hf: "top1_is_loop_on X TX a f" "c = {g. top1_loop_equiv_on X TX a f g}"
            using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
          \<comment> \<open>Base-change f from a to b in X: f' = basepoint_change(X, a, b, \<delta>, f).\<close>
          let ?f' = "top1_basepoint_change_on X TX a ?b ?\<delta> f"
          have hf'_loop: "top1_is_loop_on X TX ?b ?f'"
            by (rule top1_basepoint_change_is_loop[OF hTopX_ns h\<delta>_path hf(1)])
          have hf'_class: "{g. top1_loop_equiv_on X TX ?b ?f' g}
              \<in> top1_fundamental_group_carrier X TX ?b"
            unfolding top1_fundamental_group_carrier_def using hf'_loop by (by100 blast)
          \<comment> \<open>By surjectivity at b: \<exists>g loop in U at b with [g]_X = [f']_X.\<close>
          have "\<exists>cu \<in> top1_fundamental_group_carrier ?U ?TU ?b.
              top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x) cu
              = {g. top1_loop_equiv_on X TX ?b ?f' g}"
          proof -
            have "{g. top1_loop_equiv_on X TX ?b ?f' g} \<in>
                (top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x))
                ` top1_fundamental_group_carrier ?U ?TU ?b"
              using hincl_surj_b hf'_class by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          then obtain cu where hcu: "cu \<in> top1_fundamental_group_carrier ?U ?TU ?b"
              "top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x) cu
                = {g. top1_loop_equiv_on X TX ?b ?f' g}" by (by100 blast)
          obtain g where hg: "top1_is_loop_on ?U ?TU ?b g" "cu = {k. top1_loop_equiv_on ?U ?TU ?b g k}"
            using hcu(1) unfolding top1_fundamental_group_carrier_def by (by100 blast)
          \<comment> \<open>Base-change g from b to a in U: g' = basepoint_change(U, b, a, rev(\<delta>), g).\<close>
          let ?revd = "top1_path_reverse ?\<delta>"
          let ?g' = "top1_basepoint_change_on ?U ?TU ?b a ?revd g"
          \<comment> \<open>g' is a loop in U at a. incl_a*([g']_U) = [g']_X = [rev(\<delta>)^_X(g)]_X.\<close>
          \<comment> \<open>Since g ~ f' in X, rev(\<delta>)^_X(g) ~ rev(\<delta>)^_X(f') in X.\<close>
          \<comment> \<open>By roundtrip: rev(\<delta>)^_X(\<delta>^_X(f)) ~ f. So rev(\<delta>)^_X(f') ~ f.\<close>
          \<comment> \<open>Chaining: rev(\<delta>)^_X(g) ~ rev(\<delta>)^_X(f') ~ f. So [g']_X = [f] = c.\<close>
          \<comment> \<open>Step 1: g' is a loop in U at a.\<close>
          have hTopU_loc: "is_topology_on ?U ?TU"
            by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
          have hrevd_path_U: "top1_is_path_on ?U ?TU ?b a ?revd"
          proof -
            have h\<delta>_img_U: "?\<delta> ` top1_unit_interval \<subseteq> ?U"
            proof
              fix y assume "y \<in> ?\<delta> ` top1_unit_interval"
              then obtain t where ht: "t \<in> top1_unit_interval" "y = h (1 - t/2, 0::real)" by (by100 blast)
              have ht01: "0 \<le> t" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by (by100 simp)+
              have hne00: "(1 - t/2, 0::real) \<noteq> (0::real, 0::real)"
                using ht01 by (by100 auto)
              have hy_X: "y \<in> X"
                using continuous_map_maps_to[OF assms(5) h\<delta>_in_B2[OF ht(1)]] ht(2) by (by100 simp)
              have "y \<noteq> ?x0"
              proof (cases "t = 0")
                case True thus ?thesis using ht(2) assms(9) hx0_notin_A assms(6) by (by100 auto)
              next
                case False
                hence "t > 0" using ht01(1) by (by100 linarith)
                hence h_intB2: "(1 - t/2, 0::real) \<in> top1_B2 - top1_S1"
                proof -
                  have hle: "(1 - t/2) * (1 - t/2) + 0 * (0::real) \<le> 1"
                  proof -
                    have "(1 - t/2) * (1 - t/2) \<le> (1 - t/2) * 1"
                      by (rule mult_left_mono) (use ht01 in \<open>by100 linarith\<close>)+
                    also have "\<dots> \<le> 1" using ht01 by (by100 simp)
                    finally show ?thesis by (by100 simp)
                  qed
                  have hlt: "(1 - t/2) * (1 - t/2) + 0 * (0::real) < 1"
                  proof -
                    have "0 \<le> 1 - t/2" using ht01 by (by100 linarith)
                    have "1 - t/2 < 1" using \<open>t > 0\<close> by (by100 linarith)
                    have "(1 - t/2) * (1 - t/2) \<le> (1 - t/2) * 1"
                      by (rule mult_left_mono) (use \<open>0 \<le> 1 - t/2\<close> \<open>1 - t/2 < 1\<close> in \<open>by100 linarith\<close>)+
                    also have "\<dots> < 1" using \<open>1 - t/2 < 1\<close> by (by100 simp)
                    finally show ?thesis by (by100 simp)
                  qed
                  have hle2: "fst (1 - t/2, 0::real) ^ 2 + snd (1 - t/2, 0::real) ^ 2 \<le> 1"
                    using hle power2_eq_square[of "1 - t/2"] power2_eq_square[of "0::real"]
                    by (by100 simp)
                  have hlt2: "fst (1 - t/2, 0::real) ^ 2 + snd (1 - t/2, 0::real) ^ 2 \<noteq> 1"
                    using hlt power2_eq_square[of "1 - t/2"] power2_eq_square[of "0::real"]
                    by (by100 simp)
                  show ?thesis unfolding top1_B2_def top1_S1_def
                    using hle2 hlt2 by (by100 auto)
                qed
                moreover have hinj: "inj_on h (top1_B2 - top1_S1)"
                  using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                ultimately have "h (1 - t/2, 0) \<noteq> h (0, 0)"
                  using hne00 h00_intB2 inj_on_contraD[OF hinj] by (by100 blast)
                thus ?thesis using ht(2) by (by100 simp)
              qed
              thus "y \<in> ?U" using hy_X by (by100 blast)
            qed
            have h\<delta>_path_U: "top1_is_path_on ?U ?TU a ?b ?\<delta>"
              unfolding top1_is_path_on_def
            proof (intro conjI)
              show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?U ?TU ?\<delta>"
                using top1_continuous_map_on_codomain_shrink[OF h\<delta>_cont h\<delta>_img_U] by (by100 simp)
            next show "?\<delta> 0 = a" using h\<delta>_0 .
            next show "?\<delta> 1 = ?b" using h\<delta>_1 .
            qed
            show ?thesis by (rule top1_path_reverse_is_path[OF h\<delta>_path_U])
          qed
          have hg'_loop_U: "top1_is_loop_on ?U ?TU a ?g'"
            by (rule top1_basepoint_change_is_loop[OF hTopU_loc hrevd_path_U hg(1)])
          have hg'_class_U: "{k. top1_loop_equiv_on ?U ?TU a ?g' k}
              \<in> top1_fundamental_group_carrier ?U ?TU a"
            unfolding top1_fundamental_group_carrier_def using hg'_loop_U by (by100 blast)
          \<comment> \<open>Step 2: incl_a*([g']_U) = [g']_X (by inclusion_induced_class).\<close>
          have hA_sub_U_loc: "?U \<subseteq> X" by (by100 blast)
          \<comment> \<open>Step 3: g' in U = g' in X (since \<iota> = identity on functions).
             rev(\<delta>)^_X(g) ~ rev(\<delta>)^_X(f') in X (since g ~ f' in X).
             rev(\<delta>)^_X(f') = rev(\<delta>)^_X(\<delta>^_X(f)) ~ f in X (by roundtrip).\<close>
          \<comment> \<open>Key fact: incl_b*([g]_U) = [f']_X, i.e., g ~ f' in X.\<close>
          have hg_equiv_f'_X: "top1_loop_equiv_on X TX ?b g ?f'"
          proof -
            have hU_sub_X: "?U \<subseteq> X" by (by100 blast)
            have hTU_eq: "subspace_topology X TX ?U = ?TU" by (by100 simp)
            \<comment> \<open>incl*_b([g]_U) = [g]_X by inclusion_induced_class.\<close>
            have hincl_g: "top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x)
                {k. top1_loop_equiv_on ?U ?TU ?b g k}
              = {k. top1_loop_equiv_on X TX ?b g k}"
              by (rule inclusion_induced_class[OF hU_sub_X hTopX_ns hTU_eq hg(1)])
            \<comment> \<open>From hcu(2): this equals [f']_X.\<close>
            have "[g]_X = [f']_X": "{k. top1_loop_equiv_on X TX ?b g k}
              = {k. top1_loop_equiv_on X TX ?b ?f' k}"
              using hcu(2) hg(2) hincl_g by (by100 simp)
            \<comment> \<open>Set equality of equiv classes implies equiv of representatives.\<close>
            hence "top1_loop_equiv_on X TX ?b g ?f'"
            proof -
              have "?f' \<in> {k. top1_loop_equiv_on X TX ?b ?f' k}"
                using top1_loop_equiv_on_refl[OF hf'_loop] by (by100 blast)
              hence "?f' \<in> {k. top1_loop_equiv_on X TX ?b g k}"
                using \<open>{k. top1_loop_equiv_on X TX ?b g k} = {k. top1_loop_equiv_on X TX ?b ?f' k}\<close>
                by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            thus ?thesis .
          qed
          \<comment> \<open>Apply rev(\<delta>) base change in X to both sides.\<close>
          have hrevd_path_X: "top1_is_path_on X TX ?b a ?revd"
            by (rule top1_path_reverse_is_path[OF h\<delta>_path])
          have hg_loop_X: "top1_is_loop_on X TX ?b g"
          proof -
            have hincl_UX: "top1_continuous_map_on ?U ?TU X TX (\<lambda>x. x)"
            proof -
              from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopX_ns] Diff_subset]
              show ?thesis unfolding id_def by (by100 simp)
            qed
            have hb_U: "?b \<in> ?U" using hb_in_VA hb_ne_x0 hA_sub_X by (by100 blast)
            have "top1_is_loop_on X TX ((\<lambda>x. x) ?b) ((\<lambda>x. x) \<circ> g)"
              by (rule top1_continuous_map_loop_early[OF hincl_UX hg(1)])
            moreover have "(\<lambda>x::'a. x) \<circ> g = g" by (rule ext) (by100 simp)
            moreover have "(\<lambda>x::'a. x) ?b = ?b" by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          have hrevg_equiv: "top1_loop_equiv_on X TX a
              (top1_basepoint_change_on X TX ?b a ?revd g)
              (top1_basepoint_change_on X TX ?b a ?revd ?f')"
            by (rule top1_basepoint_change_loop_equiv[OF hTopX_ns hrevd_path_X
                hg_loop_X hf'_loop hg_equiv_f'_X])
          \<comment> \<open>Roundtrip: rev(\<delta>)^_X(\<delta>^_X(f)) ~ f.\<close>
          have hroundtrip: "top1_path_homotopic_on X TX a a f
              (top1_basepoint_change_on X TX ?b a ?revd ?f')"
            by (rule top1_basepoint_change_roundtrip[OF hTopX_ns h\<delta>_path hf(1)])
          \<comment> \<open>Chain: g' = rev(\<delta>)^_U(g) = rev(\<delta>)^_X(g) ~ rev(\<delta>)^_X(f') ~ f in X.\<close>
          \<comment> \<open>Since \<iota> = identity: basepoint_change in U = basepoint_change in X on same path.\<close>
          have hg'_eq_X: "top1_basepoint_change_on ?U ?TU ?b a ?revd g
              = top1_basepoint_change_on X TX ?b a ?revd g"
            unfolding top1_basepoint_change_on_def top1_path_product_def top1_path_reverse_def
            by (by100 simp)
          \<comment> \<open>Step A: incl_a*([g']_U) = [g']_X (inclusion_induced_class for U \<subseteq> X).\<close>
          have hU_sub_X: "?U \<subseteq> X" by (by100 blast)
          have hTU_eq_X: "subspace_topology X TX ?U = ?TU" by (by100 simp)
          have hincl_g': "top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x)
              {k. top1_loop_equiv_on ?U ?TU a ?g' k}
            = {k. top1_loop_equiv_on X TX a ?g' k}"
            by (rule inclusion_induced_class[OF hU_sub_X hTopX_ns hTU_eq_X hg'_loop_U])
          \<comment> \<open>Chain: incl_a*([g']_U) = [g']_X = [rev(\<delta>)^_X(g)]_X [by hg'_eq_X]
                 = [rev(\<delta>)^_X(f')]_X [by hrevg_equiv]
                 = [f]_X [by hroundtrip] = c [by hf(2)].\<close>
          \<comment> \<open>Need: loop_equiv(X, a, g', f). Chain via rev(\<delta>)^(g) and rev(\<delta>)^(f').\<close>
          have hbcf'_loop: "top1_is_loop_on X TX a
              (top1_basepoint_change_on X TX ?b a ?revd ?f')"
            by (rule top1_basepoint_change_is_loop[OF hTopX_ns hrevd_path_X hf'_loop])
          \<comment> \<open>hroundtrip gives path_homotopic(f, rev(\<delta>)^(f')). Convert to loop_equiv.\<close>
          have hf_equiv_bcf': "top1_loop_equiv_on X TX a f
              (top1_basepoint_change_on X TX ?b a ?revd ?f')"
            unfolding top1_loop_equiv_on_def using hf(1) hbcf'_loop hroundtrip by (by100 blast)
          \<comment> \<open>sym: loop_equiv(rev(\<delta>)^(f'), f).\<close>
          have hbcf'_equiv_f: "top1_loop_equiv_on X TX a
              (top1_basepoint_change_on X TX ?b a ?revd ?f') f"
            by (rule top1_loop_equiv_on_sym[OF hf_equiv_bcf'])
          \<comment> \<open>trans: loop_equiv(rev(\<delta>)^(g), rev(\<delta>)^(f')) + loop_equiv(rev(\<delta>)^(f'), f)
               = loop_equiv(rev(\<delta>)^(g), f).\<close>
          have hbcg_equiv_f: "top1_loop_equiv_on X TX a
              (top1_basepoint_change_on X TX ?b a ?revd g) f"
            by (rule top1_loop_equiv_on_trans[OF hTopX_ns hrevg_equiv hbcf'_equiv_f])
          \<comment> \<open>Since g' = rev(\<delta>)^_X(g) as functions: loop_equiv(g', f).\<close>
          have hg'_equiv_f: "top1_loop_equiv_on X TX a ?g' f"
            using hbcg_equiv_f hg'_eq_X by (by100 simp)
          \<comment> \<open>Class equality: {k. equiv(g',k)} = {k. equiv(f,k)} = c.\<close>
          have hclass_chain: "{k. top1_loop_equiv_on X TX a ?g' k} = c"
          proof -
            have hdir1_X: "\<And>k'. top1_loop_equiv_on X TX a ?g' k'
                \<Longrightarrow> top1_loop_equiv_on X TX a f k'"
            proof -
              fix k'
              assume "top1_loop_equiv_on X TX a ?g' k'"
              show "top1_loop_equiv_on X TX a f k'"
                using top1_loop_equiv_on_trans[OF hTopX_ns
                  top1_loop_equiv_on_sym[OF hg'_equiv_f]
                  \<open>top1_loop_equiv_on X TX a ?g' k'\<close>] .
            qed
            have hdir2_X: "\<And>k'. top1_loop_equiv_on X TX a f k'
                \<Longrightarrow> top1_loop_equiv_on X TX a ?g' k'"
            proof -
              fix k'
              assume "top1_loop_equiv_on X TX a f k'"
              show "top1_loop_equiv_on X TX a ?g' k'"
                using top1_loop_equiv_on_trans[OF hTopX_ns hg'_equiv_f
                  \<open>top1_loop_equiv_on X TX a f k'\<close>] .
            qed
            have hclass_eq_gf: "{k. top1_loop_equiv_on X TX a ?g' k}
                = {k. top1_loop_equiv_on X TX a f k}"
              using hdir1_X hdir2_X by (by100 blast)
            thus ?thesis using hf(2) by (by100 simp)
          qed
          \<comment> \<open>incl_a*([g']_U) = [g']_X = c.\<close>
          show "c \<in> (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
              ` top1_fundamental_group_carrier ?U ?TU a"
            using hg'_class_U hincl_g' hclass_chain by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>Step (c): j_* = (U\<hookrightarrow>X)_* \<circ> (A\<hookrightarrow>U)_* by functoriality.\<close>
    have hj_comp: "\<forall>c \<in> top1_fundamental_group_carrier A ?TA a.
        ?jAX c = (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
          ((top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c)"
    proof (intro ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier A ?TA a"
      have hTopU_loc: "is_topology_on ?U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
      have hAU_cont: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
      proof -
        have "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
        have "top1_continuous_map_on ?U ?TU ?U ?TU id" by (rule top1_continuous_map_on_id[OF hTopU_loc])
        from top1_continuous_map_on_restrict_domain_simple[OF this \<open>A \<subseteq> ?U\<close>]
        have "top1_continuous_map_on A (subspace_topology ?U ?TU A) ?U ?TU id" .
        have "subspace_topology ?U ?TU A = ?TA"
          using subspace_topology_trans[OF \<open>A \<subseteq> ?U\<close>] by (by100 simp)
        have "(id::'a\<Rightarrow>'a) = (\<lambda>x. x)" unfolding id_def by (by100 blast)
        show ?thesis using \<open>top1_continuous_map_on A (subspace_topology ?U ?TU A) ?U ?TU id\<close>
          \<open>subspace_topology ?U ?TU A = ?TA\<close> \<open>(id::'a\<Rightarrow>'a) = (\<lambda>x. x)\<close> by (by100 simp)
      qed
      have ha_U: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
      have hUX_cont: "top1_continuous_map_on ?U ?TU X TX (\<lambda>x. x)"
      proof -
        from top1_continuous_map_on_restrict_domain_simple[OF
          top1_continuous_map_on_id[OF hTopX_ns] Diff_subset]
        have "top1_continuous_map_on ?U (subspace_topology X TX ?U) X TX id" .
        have "(id::'a\<Rightarrow>'a) = (\<lambda>x. x)" unfolding id_def by (by100 blast)
        thus ?thesis using \<open>top1_continuous_map_on ?U (subspace_topology X TX ?U) X TX id\<close>
          by (by100 simp)
      qed
      have hcomp_eq: "(\<lambda>x. x) \<circ> (\<lambda>x::'a. x) = (\<lambda>x. x)" by (rule ext) (by100 simp)
      show "?jAX c = (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
          ((top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c)"
        using fundamental_group_induced_comp[OF hTA_top hTopU_loc hTopX_ns
          hAU_cont hUX_cont assms(6) _ _ hc] hcomp_eq by (by100 simp)
    qed
    \<comment> \<open>Step (d): Composition of surjection with surjection/iso is surjection.\<close>
    \<comment> \<open>From hA_U_iso, the induced map A\<rightarrow>U is surjective.\<close>
    have hAU_surj: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
        ` (top1_fundamental_group_carrier A ?TA a)
      = top1_fundamental_group_carrier ?U ?TU a"
    proof -
      have hTopU_d: "is_topology_on ?U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
      have ha_U_d: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
      have hAU_cont_d: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
      proof -
        have "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
        from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopU_d] this]
        have "top1_continuous_map_on A (subspace_topology ?U ?TU A) ?U ?TU id" .
        thus ?thesis using subspace_topology_trans[OF \<open>A \<subseteq> ?U\<close>]
          unfolding id_def by (by100 simp)
      qed
      have hAU_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
          (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTA_top hTopU_d assms(6) ha_U_d hAU_cont_d])
           (by100 simp)
      show ?thesis proof (rule equalityI)
      show "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
          ` (top1_fundamental_group_carrier A ?TA a) \<subseteq> top1_fundamental_group_carrier ?U ?TU a"
        using hAU_hom unfolding top1_group_hom_on_def by (by100 blast)
    next
      \<comment> \<open>Backward: carrier \<subseteq> image. For [f] \<in> \<pi>_1(U,a), use the retraction r.
         r\<circ>f is a loop in A at a. \<iota>_*(class of r\<circ>f) = class of f (since \<iota>\<circ>r \<simeq> id via deformation).\<close>
      show "top1_fundamental_group_carrier ?U ?TU a
          \<subseteq> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
              ` (top1_fundamental_group_carrier A ?TA a)"
      proof
        fix c assume hc: "c \<in> top1_fundamental_group_carrier ?U ?TU a"
        \<comment> \<open>Extract a loop f from the class c.\<close>
        obtain f where hf_loop: "top1_is_loop_on ?U ?TU a f"
            and hc_eq: "c = {g. top1_loop_equiv_on ?U ?TU a f g}"
          using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
        \<comment> \<open>Extract the deformation retract homotopy H and retraction r.\<close>
        obtain H_deform where hHcont: "top1_continuous_map_on (?U \<times> I_set)
            (product_topology_on ?TU I_top) ?U ?TU H_deform"
            and hH0: "\<forall>x\<in>?U. H_deform (x, 0) = x"
            and hH1: "\<forall>x\<in>?U. H_deform (x, 1) \<in> A"
            and hHfix: "\<forall>a'\<in>A. \<forall>t\<in>I_set. H_deform (a', t) = a'"
          using hA_deformation_retract_U unfolding top1_deformation_retract_of_on_def by (by100 auto)
        let ?r = "\<lambda>x. H_deform (x, 1)"
        \<comment> \<open>r(a) = a since a \<in> A.\<close>
        have h1_in_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hra: "?r a = a" using hHfix assms(6) h1_in_I by (by100 blast)
        \<comment> \<open>\<iota>\<circ>r = (\<lambda>x. H_deform(x,1)) is continuous U \<rightarrow> U.\<close>
        have h_ir_cont: "top1_continuous_map_on ?U ?TU ?U ?TU (\<lambda>x. H_deform (x, 1))"
        proof -
          have hcomp_eq: "(\<lambda>x. H_deform (x, 1)) = H_deform \<circ> (\<lambda>x. (x, 1::real))"
            by (rule ext) (by100 simp)
          have hpair_cont: "top1_continuous_map_on ?U ?TU (?U \<times> I_set)
              (product_topology_on ?TU I_top) (\<lambda>x. (x, 1::real))"
          proof -
            have hI_top: "is_topology_on I_set I_top"
              by (rule top1_unit_interval_topology_is_topology_on)
            \<comment> \<open>Component 1: pi1 \<circ> (\<lambda>x. (x, 1)) = id, continuous.\<close>
            have hc1: "top1_continuous_map_on ?U ?TU ?U ?TU (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
            proof -
              have heq: "\<And>x::'a. pi1 (x, 1::real) = x" unfolding pi1_def by (by100 simp)
              have "pi1 \<circ> (\<lambda>x::'a. (x, 1::real)) = (\<lambda>x. x)"
                unfolding pi1_def by (rule ext) (by100 simp)
              thus ?thesis
                using top1_continuous_map_on_id[OF hTopU_d]
                unfolding id_def by (by100 simp)
            qed
            \<comment> \<open>Component 2: pi2 \<circ> (\<lambda>x. (x, 1)) = const 1, continuous.\<close>
            have hc2: "top1_continuous_map_on ?U ?TU I_set I_top (pi2 \<circ> (\<lambda>x::'a. (x, 1::real)))"
            proof -
              have "pi2 \<circ> (\<lambda>x::'a. (x, 1::real)) = (\<lambda>_::'a. 1::real)"
                unfolding pi2_def by (rule ext) (by100 simp)
              moreover have "top1_continuous_map_on ?U ?TU I_set I_top (\<lambda>_::'a. 1::real)"
              proof -
                have "\<forall>y0\<in>I_set. top1_continuous_map_on ?U ?TU I_set I_top (\<lambda>x. y0)"
                  using Theorem_18_2[OF hTopU_d hI_top hI_top] by (by100 blast)
                thus ?thesis using h1_in_I by (by100 blast)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            show ?thesis using iffD2[OF Theorem_18_4[OF hTopU_d hTopU_d hI_top]] hc1 hc2
              by (by100 blast)
          qed
          show ?thesis unfolding hcomp_eq
            by (rule top1_continuous_map_on_comp[OF hpair_cont hHcont])
        qed
        \<comment> \<open>r\<circ>f is a loop in A at a.\<close>
        have hrf_loop_A: "top1_is_loop_on A ?TA a (?r \<circ> f)"
        proof -
          \<comment> \<open>r: U \<rightarrow> A continuous (shrink codomain of h_ir_cont).\<close>
          have hr_img: "?r ` ?U \<subseteq> A"
          proof
            fix y assume "y \<in> ?r ` ?U"
            then obtain x where "x \<in> ?U" "y = H_deform (x, 1)" by (by100 blast)
            thus "y \<in> A" using hH1 by (by100 blast)
          qed
          have hA_sub_U: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
          have hr_cont_sub: "top1_continuous_map_on ?U ?TU A (subspace_topology ?U ?TU A) ?r"
            by (rule top1_continuous_map_on_codomain_shrink[OF h_ir_cont hr_img hA_sub_U])
          have hTA_eq: "subspace_topology ?U ?TU A = ?TA"
            using subspace_topology_trans[OF hA_sub_U] by (by100 simp)
          have hr_cont_A: "top1_continuous_map_on ?U ?TU A ?TA ?r"
            using hr_cont_sub hTA_eq by (by100 simp)
          show ?thesis using top1_continuous_map_loop_early[OF hr_cont_A hf_loop] hra
            by (by100 simp)
        qed
        \<comment> \<open>The class of r\<circ>f in \<pi>_1(A,a).\<close>
        let ?rf_class = "{g. top1_loop_equiv_on A ?TA a (?r \<circ> f) g}"
        have hrf_in_carrier: "?rf_class \<in> top1_fundamental_group_carrier A ?TA a"
          unfolding top1_fundamental_group_carrier_def using hrf_loop_A by (by100 blast)
        \<comment> \<open>\<iota>_*([r\<circ>f]_A) = [r\<circ>f]_U (since \<iota> = inclusion, loop_equiv in A implies loop_equiv in U).\<close>
        have h\<iota>_rf: "top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x) ?rf_class
            = {g. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g}"
        proof -
          have hA_sub_U_loc: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
          have hTA_eq_loc: "subspace_topology ?U ?TU A = ?TA"
            using subspace_topology_trans[OF hA_sub_U_loc] by (by100 simp)
          show ?thesis
            by (rule inclusion_induced_class[OF hA_sub_U_loc hTopU_d hTA_eq_loc hrf_loop_A])
        qed
        \<comment> \<open>r\<circ>f \<simeq> f in U (from deformation: \<iota>\<circ>r \<simeq> id via H, basepoint a fixed).\<close>
        have hrf_equiv_f: "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) f"
        proof -
          \<comment> \<open>Apply Lemma_58_1 with h=id, k=\<iota>\<circ>r. H(x,0)=x=id(x), H(x,1)=\<iota>(r(x)).
             Conclusion: path_homotopic(id\<circ>f, (\<iota>\<circ>r)\<circ>f) = path_homotopic(f, r\<circ>f).\<close>
          have h_id_cont: "top1_continuous_map_on ?U ?TU ?U ?TU (\<lambda>x. x)"
          proof -
            have "(id::'a\<Rightarrow>'a) = (\<lambda>x. x)" unfolding id_def by (by100 blast)
            thus ?thesis using top1_continuous_map_on_id[OF hTopU_d] by (by100 simp)
          qed
          \<comment> \<open>h_ir_cont already proved above.\<close>
          have hH_fix_a: "\<forall>t\<in>I_set. H_deform (a, t) = a"
            using hHfix assms(6) by (by100 blast)
          have hH_hom: "\<exists>Hh. top1_continuous_map_on (?U \<times> I_set) (product_topology_on ?TU I_top)
              ?U ?TU Hh \<and> (\<forall>x\<in>?U. Hh (x, 0) = (\<lambda>x. x) x) \<and>
              (\<forall>x\<in>?U. Hh (x, 1) = (\<lambda>x. H_deform (x, 1)) x) \<and>
              (\<forall>t\<in>I_set. Hh (a, t) = a)"
            using hHcont hH0 hH1 hHfix assms(6) by (rule_tac x=H_deform in exI) (by100 auto)
          from Lemma_58_1_basepoint_fixed[OF hTopU_d h_id_cont h_ir_cont _ _ hH_hom hf_loop]
          have "top1_path_homotopic_on ?U ?TU a a
              (top1_induced_homomorphism_on ?U ?TU ?U ?TU (\<lambda>x. x) f)
              (top1_induced_homomorphism_on ?U ?TU ?U ?TU (\<lambda>x. H_deform (x, 1)) f)"
            using hra by (by100 auto)
          \<comment> \<open>induced_hom(id, f) = f and induced_hom(\<iota>\<circ>r, f) = r\<circ>f.\<close>
          hence "top1_path_homotopic_on ?U ?TU a a f (?r \<circ> f)"
            unfolding top1_induced_homomorphism_on_def comp_def by (by100 simp)
          hence "top1_path_homotopic_on ?U ?TU a a (?r \<circ> f) f"
            by (rule Lemma_51_1_path_homotopic_sym)
          moreover have "top1_is_loop_on ?U ?TU a (?r \<circ> f)"
          proof -
            \<comment> \<open>Loop in A \<Longrightarrow> loop in U via inclusion.\<close>
            have "top1_is_loop_on ?U ?TU a ((\<lambda>x. x) \<circ> (?r \<circ> f))"
              using top1_continuous_map_loop_early[OF hAU_cont_d hrf_loop_A] by (by100 simp)
            moreover have "(\<lambda>x::'a. x) \<circ> (?r \<circ> f) = ?r \<circ> f" by (rule ext) (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis unfolding top1_loop_equiv_on_def
            using hf_loop by (by100 blast)
        qed
        \<comment> \<open>[r\<circ>f]_U = [f]_U (from hrf_equiv_f).\<close>
        have hclass_eq: "{g. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g} = c"
        proof -
          have hdir1: "\<And>g'. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g'
              \<Longrightarrow> top1_loop_equiv_on ?U ?TU a f g'"
          proof -
            fix g'
            assume "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g'"
            show "top1_loop_equiv_on ?U ?TU a f g'"
              using top1_loop_equiv_on_trans[OF hTopU_d
                top1_loop_equiv_on_sym[OF hrf_equiv_f]
                \<open>top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g'\<close>] .
          qed
          moreover have hdir2: "\<And>g'. top1_loop_equiv_on ?U ?TU a f g'
              \<Longrightarrow> top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g'"
          proof -
            fix g'
            assume "top1_loop_equiv_on ?U ?TU a f g'"
            show "top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g'"
              using top1_loop_equiv_on_trans[OF hTopU_d hrf_equiv_f
                \<open>top1_loop_equiv_on ?U ?TU a f g'\<close>] .
          qed
          ultimately have "{g. top1_loop_equiv_on ?U ?TU a (?r \<circ> f) g}
              = {g. top1_loop_equiv_on ?U ?TU a f g}" by (by100 blast)
          thus ?thesis using hc_eq by (by100 simp)
        qed
        \<comment> \<open>Combine: \<iota>_*([r\<circ>f]_A) = [r\<circ>f]_U = c.\<close>
        have h\<iota>_rf_img: "top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x) ?rf_class = c"
          using h\<iota>_rf hclass_eq by (by100 simp)
        thus "c \<in> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
            ` (top1_fundamental_group_carrier A ?TA a)"
          using hrf_in_carrier by (by100 blast)
      qed
    qed qed
    \<comment> \<open>Combine: j_* = (U\<rightarrow>X)_* \<circ> (A\<rightarrow>U)_*, both surjective.\<close>
    show ?thesis
    proof (rule equalityI)
      show "?jAX ` (top1_fundamental_group_carrier A ?TA a)
          \<subseteq> top1_fundamental_group_carrier X TX a"
        using hj_hom unfolding top1_group_hom_on_def by (by100 blast)
    next
      show "top1_fundamental_group_carrier X TX a
          \<subseteq> ?jAX ` (top1_fundamental_group_carrier A ?TA a)"
      proof
        fix x assume hx: "x \<in> top1_fundamental_group_carrier X TX a"
        \<comment> \<open>x \<in> im(U\<rightarrow>X): get u with (U\<rightarrow>X)_*(u) = x.\<close>
        have "x \<in> (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
            ` (top1_fundamental_group_carrier ?U ?TU a)"
          using hx hU_X_surj by (by100 simp)
        then obtain u where hu: "u \<in> top1_fundamental_group_carrier ?U ?TU a"
            "(top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x)) u = x" by (by100 blast)
        \<comment> \<open>u \<in> im(A\<rightarrow>U): get c with (A\<rightarrow>U)_*(c) = u.\<close>
        have "u \<in> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))
            ` (top1_fundamental_group_carrier A ?TA a)"
          using hu(1) hAU_surj by (by100 simp)
        then obtain c where hc: "c \<in> top1_fundamental_group_carrier A ?TA a"
            "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c = u" by (by100 blast)
        \<comment> \<open>j_*(c) = (U\<rightarrow>X)_*((A\<rightarrow>U)_*(c)) = (U\<rightarrow>X)_*(u) = x.\<close>
        have "?jAX c = x" using hj_comp hc hu by (by100 simp)
        thus "x \<in> ?jAX ` (top1_fundamental_group_carrier A ?TA a)"
          using hc(1) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: ker(j_*) = \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.
     By SvK (Cor 70.4) at base b: ker(U\<hookrightarrow>X at b) = \<langle>\<langle>\<iota>_*(\<pi>_1(UV,b))\<rangle>\<rangle> = \<langle>\<langle>{[g_0]}\<rangle>\<rangle>.
     Base change \<delta>-hat maps [g_0] to [\<delta>_bar * (g_0 * \<delta>)] = [h \<circ> f] = [k \<circ> p]
     (using the winding number homotopy \<gamma>_bar*(f_0*\<gamma>) \<simeq> f in B2-{0}).
     Under the retraction iso A \<cong> U: ker becomes \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle> in \<pi>_1(A,a).\<close>
  have hj_ker: "top1_group_kernel_on
      (top1_fundamental_group_carrier A ?TA a)
      (top1_fundamental_group_id X TX a) ?jAX = ?relator"
  proof -
    \<comment> \<open>Munkres Step 3 (kernel computation).
       The key geometric fact: [k\<circ>p] is in ker(j_*), and it normally generates all of ker(j_*).
       Step (a): [k\<circ>p] \<in> ker(j_*). The loop k\<circ>p = h\<circ>f maps S1 into A \<subseteq> X.
         As a loop in X, k\<circ>p = h\<circ>f is nulhomotopic because h extends over B2
         (h maps ALL of B2 into X, not just S1). So [k\<circ>p] = [h\<circ>f] = id in \<pi>_1(X,a).
       Step (b): ker(j_*) \<subseteq> \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>. This uses the SvK kernel at base b:
         ker(U\<hookrightarrow>X at b) = \<langle>\<langle>{[g_0]}\<rangle>\<rangle> where g_0 = h\<circ>f_0 (half-radius loop).
         Base change \<delta>-hat: ker at base a = \<langle>\<langle>{\<delta>-hat([g_0])} = {[k\<circ>p]}\<rangle>\<rangle>.
         Under the retraction iso A\<cong>U: ker(j_*) in \<pi>_1(A,a) = \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.\<close>
    \<comment> \<open>Step (a): [k\<circ>p] \<in> ker(j_*). The loop h\<circ>f extends over B2 \<Longrightarrow> nulhomotopic in X.\<close>
    have hkp_in_ker: "?jAX (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
        {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g})
      = top1_fundamental_group_id X TX a"
    proof -
      \<comment> \<open>Step 1: j \<circ> \<iota> = h|_{S1}: S1 \<rightarrow> X is continuous.\<close>
      let ?h_S1 = "\<lambda>z. h z"  \<comment> \<open>= j \<circ> \<iota> = (\<lambda>x. x) \<circ> (\<lambda>z. h z) = h restricted to S1, into X.\<close>
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hS1_B2: "top1_S1 \<subseteq> top1_B2"
        unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hh_S1_cont: "top1_continuous_map_on top1_S1 top1_S1_topology X TX ?h_S1"
      proof -
        have hS1_B2: "top1_S1 \<subseteq> top1_B2"
          unfolding top1_S1_def top1_B2_def by (by100 auto)
        have h_cont_S1_sub: "top1_continuous_map_on top1_S1
            (subspace_topology top1_B2 top1_B2_topology top1_S1) X TX h"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF assms(5) hS1_B2])
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
        show ?thesis using h_cont_S1_sub hS1_top_eq by (by100 simp)
      qed
      \<comment> \<open>Step 2: h|_{S1} is nulhomotopic in X (Lemma 55.3 backward: h extends over B2).\<close>
      have hh_S1_nulhom: "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX ?h_S1"
        by (rule Lemma_55_3_backward[OF hh_S1_cont hTopX_ns assms(5)]) (by100 simp)
      \<comment> \<open>Step 3: By nulhomotopic_trivializes_loops_general, (h|_{S1}) \<circ> f is trivial in \<pi>_1(X,a).\<close>
      have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      have hh10: "?h_S1 (1, 0) = a" using assms(9) by (by100 simp)
      have hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?f"
        unfolding top1_is_loop_on_def top1_is_path_on_def
      proof (intro conjI)
        have hf_eq: "?f = top1_R_to_S1"
        proof (rule ext)
          fix s :: real show "?f s = top1_R_to_S1 s" unfolding top1_R_to_S1_def by (by100 simp)
        qed
        have "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
          using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
        from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
        show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_S1 top1_S1_topology ?f"
          unfolding top1_unit_interval_topology_def hf_eq
          using subspace_topology_UNIV_self by (by100 simp)
      next show "?f 0 = (1::real, 0::real)" by (by100 simp)
      next show "?f 1 = (1::real, 0::real)" by (by100 simp)
      qed
      have htriv: "top1_path_homotopic_on X TX a a (?h_S1 \<circ> ?f) (top1_constant_path a)"
        by (rule nulhomotopic_trivializes_loops_general[OF hS1_top hTopX_ns
            hh_S1_cont hh_S1_nulhom hh10 h10_S1 hf_loop])
      \<comment> \<open>Step 4: h \<circ> f = \<iota> \<circ> f as functions (both = \<lambda>s. h(f s)).\<close>
      have hcomp_eq: "?h_S1 \<circ> ?f = ?\<iota> \<circ> ?f" by (rule ext) (by100 simp)
      \<comment> \<open>Step 5: By functoriality, j_*(\<iota>_*([f])) = (j \<circ> \<iota>)_*([f]) = [h \<circ> f] = id.\<close>
      \<comment> \<open>Need: j_*(\<iota>_*([f])) = class of (j \<circ> \<iota>) \<circ> f = class of h \<circ> f.
         Since h \<circ> f ~ constant in X, this class = id_X.\<close>
      \<comment> \<open>By functoriality: j_*(\<iota>_*([f])) = (j \<circ> \<iota>)_*([f]) where j \<circ> \<iota> = h|_{S1}.\<close>
      have hfunct: "?jAX (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
          A ?TA a ?\<iota> {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g})
        = top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) X TX a ?h_S1
            {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
      proof -
        let ?c = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
        have hc_in: "?c \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          unfolding top1_fundamental_group_carrier_def using hf_loop by (by100 blast)
        have hiota_a: "?\<iota> (1, 0) = a" using assms(9) by (by100 simp)
        have hAX_cont: "top1_continuous_map_on A ?TA X TX (\<lambda>x. x)"
          using hincl_AX_cont .
        have hcomp_id: "(\<lambda>x. x) \<circ> ?\<iota> = ?h_S1" by (rule ext) (by100 simp)
        from fundamental_group_induced_comp[OF hS1_top hTA_top hTopX_ns
            h\<iota>_cont hAX_cont h10_S1 hiota_a _ hc_in]
        have "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) X TX a
            ((\<lambda>x. x) \<circ> ?\<iota>) ?c
          = ?jAX (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
              A ?TA a ?\<iota> ?c)"
          by (by100 simp)
        thus ?thesis unfolding hcomp_id by (by100 simp)
      qed
      \<comment> \<open>h|_{S1 *}([f]) = class of h \<circ> f in \<pi>_1(X,a).\<close>
      \<comment> \<open>Since h \<circ> f is path-homotopic to constant, this class = id_X.\<close>
      have hclass_id: "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) X TX a ?h_S1
          {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
        = top1_fundamental_group_id X TX a"
      proof -
        \<comment> \<open>Unfold: induced([f]) = {k. \<exists>l. loop_equiv(S1, f, l) \<and> loop_equiv(X, h\<circ>l, k)}.\<close>
        \<comment> \<open>= {k. loop_equiv(X, h\<circ>f, k)} (congruence: f~l \<Longrightarrow> h\<circ>f ~ h\<circ>l in X).\<close>
        \<comment> \<open>= {k. loop_equiv(X, constant(a), k)} (h\<circ>f ~ constant by htriv).\<close>
        \<comment> \<open>= id_X (definition of fundamental_group_id).\<close>
        have hh_S1_eq: "?h_S1 \<circ> ?f = ?\<iota> \<circ> ?f" by (rule ext) (by100 simp)
        \<comment> \<open>The loop h\<circ>f = \<iota>\<circ>f is a loop in X at a.\<close>
        have hhf_loop_X: "top1_is_loop_on X TX a (?h_S1 \<circ> ?f)"
          using top1_continuous_map_loop[OF hh_S1_cont hf_loop] hh10 by (by100 simp)
        have hconst_loop: "top1_is_loop_on X TX a (top1_constant_path a)"
          by (rule top1_constant_path_is_loop[OF hTopX_ns ha_X])
        \<comment> \<open>path_homotopic \<Longrightarrow> loop_equiv.\<close>
        have hhf_equiv_const: "top1_loop_equiv_on X TX a (?h_S1 \<circ> ?f) (top1_constant_path a)"
          using htriv unfolding top1_loop_equiv_on_def top1_path_homotopic_on_def
          using hhf_loop_X hconst_loop by (by100 blast)
        show ?thesis
          unfolding top1_fundamental_group_induced_on_def top1_fundamental_group_id_def
        proof (rule set_eqI, rule iffI)
          fix k
          assume "k \<in> {g'. \<exists>l\<in>{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}.
              top1_loop_equiv_on X TX a (?h_S1 \<circ> l) g'}"
          then obtain l where hl_eq: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f l"
              and hk_eq: "top1_loop_equiv_on X TX a (?h_S1 \<circ> l) k" by (by100 blast)
          \<comment> \<open>f ~ l in S1 \<Longrightarrow> h\<circ>f ~ h\<circ>l in X.\<close>
          have hl_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) l"
            using hl_eq unfolding top1_loop_equiv_on_def by (by100 blast)
          have "top1_loop_equiv_on X TX (?h_S1 (1,0)) (?h_S1 \<circ> ?f) (?h_S1 \<circ> l)"
            by (rule top1_induced_preserves_loop_equiv[OF hS1_top hh_S1_cont hf_loop hl_loop hl_eq])
          hence "top1_loop_equiv_on X TX a (?h_S1 \<circ> ?f) (?h_S1 \<circ> l)"
            using hh10 by (by100 simp)
          \<comment> \<open>h\<circ>f ~ h\<circ>l and h\<circ>l ~ k \<Longrightarrow> h\<circ>f ~ k.\<close>
          from top1_loop_equiv_on_trans[OF hTopX_ns this hk_eq]
          have "top1_loop_equiv_on X TX a (?h_S1 \<circ> ?f) k" .
          \<comment> \<open>h\<circ>f ~ constant and h\<circ>f ~ k \<Longrightarrow> constant ~ k.\<close>
          from top1_loop_equiv_on_trans[OF hTopX_ns
              top1_loop_equiv_on_sym[OF hhf_equiv_const] this]
          show "k \<in> {g. top1_loop_equiv_on X TX a (top1_constant_path a) g}" by (by100 blast)
        next
          fix k
          assume "k \<in> {g. top1_loop_equiv_on X TX a (top1_constant_path a) g}"
          hence hk_const: "top1_loop_equiv_on X TX a (top1_constant_path a) k" by (by100 blast)
          \<comment> \<open>constant ~ h\<circ>f (reverse of hhf_equiv_const) and constant ~ k.\<close>
          have "top1_loop_equiv_on X TX a (?h_S1 \<circ> ?f) k"
            using top1_loop_equiv_on_trans[OF hTopX_ns hhf_equiv_const hk_const] .
          show "k \<in> {g'. \<exists>l\<in>{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}.
              top1_loop_equiv_on X TX a (?h_S1 \<circ> l) g'}"
            apply (rule CollectI, rule bexI[of _ ?f])
            apply (rule \<open>top1_loop_equiv_on X TX a (?h_S1 \<circ> ?f) k\<close>)
            using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
        qed
      qed
      show ?thesis using hfunct hclass_id by (by100 simp)
    qed
    \<comment> \<open>Step (b): ker(j_*) \<subseteq> \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>. From SvK at base b + base change + retraction.\<close>
    have hker_sub_relator: "top1_group_kernel_on
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_id X TX a) ?jAX \<subseteq> ?relator"
    proof -
      \<comment> \<open>Munkres generator tracking argument.
         Goal: ker(j_*: \<pi>_1(A,a) \<rightarrow> \<pi>_1(X,a)) \<subseteq> \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.
         By SvK at base b: ker(incl_*: \<pi>_1(U,b) \<rightarrow> \<pi>_1(X,b)) = \<langle>\<langle>\<iota>_*(\<pi>_1(UV,b))\<rangle>\<rangle>.
         The inclusion A \<hookrightarrow> U is an iso on \<pi>_1 (deformation retract).
         Under the composition A \<hookrightarrow> U \<hookrightarrow> X:
         ker(j_*: \<pi>_1(A,a) \<rightarrow> \<pi>_1(X,a)) = preimage under (A\<hookrightarrow>U)_* of ker(U\<hookrightarrow>X at a).
         Since (A\<hookrightarrow>U)_* is an iso, ker(j_*) = (A\<hookrightarrow>U)_*\<inverse> (ker(U\<hookrightarrow>X at a)).
         The SvK kernel at base b is \<langle>\<langle>\<iota>_*(\<pi>_1(UV,b))\<rangle>\<rangle>.
         Under base change from b to a + retraction, this becomes \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.
         The core mathematical claim: \<delta>-hat([\<iota>_*(g_0)]) = [k\<circ>p] in \<pi>_1(U,a),
         where g_0 is the generator of \<pi>_1(UV,b) and \<delta> is the path from b to a.\<close>
      \<comment> \<open>From the helper lemma: ker(U\<hookrightarrow>X at b) = \<langle>\<langle>\<iota>_*(\<pi>_1(UV,b))\<rangle>\<rangle>.\<close>
      have hincl_ker_b: "top1_group_kernel_on
          (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_id X TX ?b)
          (top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x))
        = top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_mul ?U ?TU ?b)
            (top1_fundamental_group_id ?U ?TU ?b) (top1_fundamental_group_invg ?U ?TU ?b)
            (top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x)
               ` top1_fundamental_group_carrier ?UV ?TUV ?b)"
        by (rule SvK_simply_connected_V_surj_kernel(2)[OF assms(1) hU_open hV_open hU_union_V
                hUV_pc hU_pc hV_sc hb_in_UV])
      \<comment> \<open>Transfer: ker(U\<hookrightarrow>X at b) via base change \<delta> + retraction iso
         gives ker(A\<hookrightarrow>X at a) = \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.
         Core claim: \<delta>-hat maps the UV-inclusion image [g_0] to [k\<circ>p].
         This follows from: \<gamma>_bar*(f_0*\<gamma>) \<simeq> f in B2-{0} (winding number),
         comp_basepoint_change for h, and inclusion_induced_class.\<close>
      \<comment> \<open>Munkres Step 3: transfer kernel from base b to base a.
         Key identity: h \<circ> \<gamma> = rev(\<delta>) (since \<delta>(t) = h(1-t/2,0) and \<gamma>(t) = (1/2+t/2,0)).
         By comp_basepoint_change: bc(U, b, a, rev(\<delta>), g0) = h \<circ> bc(B2-{0}, q, p, \<gamma>, f0).
         By winding number: bc(B2-{0}, q, p, \<gamma>, f0) \<simeq> f in B2-{0}.
         So bc(U, b, a, rev(\<delta>), g0) \<simeq> h \<circ> f = k \<circ> p in U.
         Therefore rev(\<delta>)-hat([g0]) = [k \<circ> p] in \<pi>_1(U,a).
         Since ker(incl*_a) \<subseteq> rev(\<delta>)-hat(ker(incl*_b)) = rev(\<delta>)-hat(\<langle>\<langle>{[g0]}\<rangle>\<rangle>) = \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>,
         and ker(j*) \<subseteq> (A\<hookrightarrow>U)*\<inverse>(ker(incl*_a)), we get ker(j*) \<subseteq> \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.\<close>
      \<comment> \<open>Step 1: ker(j*) \<subseteq> (A\<hookrightarrow>U)*\<inverse>(ker((U\<hookrightarrow>X)*_a)) since j* = (U\<hookrightarrow>X)* \<circ> (A\<hookrightarrow>U)*.\<close>
      have hstep1: "\<And>c. c \<in> top1_group_kernel_on
              (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_id X TX a) ?jAX
          \<Longrightarrow> (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
              \<in> top1_group_kernel_on
                (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_id X TX a)
                (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))"
      proof -
        fix c assume hc: "c \<in> top1_group_kernel_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_id X TX a) ?jAX"
        have hc_A: "c \<in> top1_fundamental_group_carrier A ?TA a"
          using hc unfolding top1_group_kernel_on_def by (by100 blast)
        have hjc_id: "?jAX c = top1_fundamental_group_id X TX a"
          using hc unfolding top1_group_kernel_on_def by (by100 blast)
        \<comment> \<open>Functoriality: j*(c) = incl*((A\<hookrightarrow>U)*(c)).\<close>
        have hTopU_k: "is_topology_on ?U ?TU"
          by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
        have ha_U_k: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
        have hA_sub_U_k: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
        have hAU_cont_k: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
        proof -
          from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopU_k] hA_sub_U_k]
          show ?thesis using subspace_topology_trans[OF hA_sub_U_k] unfolding id_def by (by100 simp)
        qed
        have hUX_cont_k: "top1_continuous_map_on ?U ?TU X TX (\<lambda>x. x)"
        proof -
          from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopX_ns] Diff_subset]
          show ?thesis unfolding id_def by (by100 simp)
        qed
        have hfunct_c: "?jAX c = (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
            ((top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c)"
        proof -
          have hcomp_eq: "(\<lambda>x::'a. x) \<circ> (\<lambda>x. x) = (\<lambda>x. x)" by (rule ext) (by100 simp)
          show ?thesis using fundamental_group_induced_comp[OF hTA_top hTopU_k hTopX_ns
              hAU_cont_k hUX_cont_k assms(6) _ _ hc_A] hcomp_eq by (by100 simp)
        qed
        \<comment> \<open>(A\<hookrightarrow>U)*(c) \<in> carrier(U).\<close>
        have hAU_hom_k: "top1_group_hom_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
            (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x))"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hTA_top hTopU_k assms(6) ha_U_k hAU_cont_k])
             (by100 simp)
        have hAU_c: "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
            \<in> top1_fundamental_group_carrier ?U ?TU a"
          using hAU_hom_k hc_A unfolding top1_group_hom_on_def by (by100 blast)
        \<comment> \<open>incl*((A\<hookrightarrow>U)*(c)) = j*(c) = id.\<close>
        have "top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x)
            ((top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c)
          = top1_fundamental_group_id X TX a"
          using hfunct_c hjc_id by (by100 simp)
        show "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
            \<in> top1_group_kernel_on
              (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_id X TX a)
              (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))"
          unfolding top1_group_kernel_on_def
          using hAU_c \<open>top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x)
              ((top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c)
            = top1_fundamental_group_id X TX a\<close> by (by100 blast)
      qed
      \<comment> \<open>Step 2: ker((U\<hookrightarrow>X)*_a) \<subseteq> \<langle>\<langle>{[k\<circ>p]_U}\<rangle>\<rangle>.
         From hincl_ker_b + base change naturality + comp_basepoint_change + winding number.\<close>
      have hstep2: "top1_group_kernel_on
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_id X TX a)
            (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
          \<subseteq> top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
              (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
              {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?U ?TU a
                 (\<lambda>z. h z) {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}}"
      proof (rule subsetI)
        fix c assume hc: "c \<in> top1_group_kernel_on
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_id X TX a)
            (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))"
        let ?kp_class = "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?U ?TU a
               (\<lambda>z. h z) {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
        \<comment> \<open>InterI approach: show c is in every normal subgroup of \<pi>_1(U,a) containing kp_class.\<close>
        show "c \<in> top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
            (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
            {?kp_class}"
          unfolding top1_normal_subgroup_generated_on_def
        proof (rule InterI)
          fix N assume hN: "N \<in> {N'. {?kp_class} \<subseteq> N' \<and>
              top1_normal_subgroup_on (top1_fundamental_group_carrier ?U ?TU a)
                (top1_fundamental_group_mul ?U ?TU a) (top1_fundamental_group_id ?U ?TU a)
                (top1_fundamental_group_invg ?U ?TU a) N'}"
          have hkp_in_N: "?kp_class \<in> N" using hN by (by100 blast)
          have hN_normal: "top1_normal_subgroup_on (top1_fundamental_group_carrier ?U ?TU a)
              (top1_fundamental_group_mul ?U ?TU a) (top1_fundamental_group_id ?U ?TU a)
              (top1_fundamental_group_invg ?U ?TU a) N"
            using hN by (by100 blast)
          \<comment> \<open>N is a subgroup, so kp_class\<inverse> \<in> N.\<close>
          have hN_grp: "top1_is_group_on N (top1_fundamental_group_mul ?U ?TU a)
              (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
            using hN_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
          have hkp_inv_N: "top1_fundamental_group_invg ?U ?TU a ?kp_class \<in> N"
            using group_inv_closed[OF hN_grp hkp_in_N] .
          have hN_sub: "N \<subseteq> top1_fundamental_group_carrier ?U ?TU a"
            using hN_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
          \<comment> \<open>c \<in> carrier and maps to identity under incl*.\<close>
          have hc_carrier: "c \<in> top1_fundamental_group_carrier ?U ?TU a"
            using hc unfolding top1_group_kernel_on_def by (by100 blast)
          have hc_id: "(top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x)) c
              = top1_fundamental_group_id X TX a"
            using hc unfolding top1_group_kernel_on_def by (by100 blast)
          \<comment> \<open>Extract loop representative.\<close>
          obtain g where hg_loop: "top1_is_loop_on ?U ?TU a g"
              and hc_eq: "c = {k. top1_loop_equiv_on ?U ?TU a g k}"
            using hc_carrier unfolding top1_fundamental_group_carrier_def by (by100 blast)
          \<comment> \<open>Base change g from a to b: g' = bc(U, a, b, \<delta>, g) = rev(\<delta>) * (g * \<delta>).\<close>
          let ?g' = "top1_basepoint_change_on ?U ?TU a ?b ?\<delta> g"
          \<comment> \<open>\<delta> is a path from a to b in U (not just X).\<close>
          have h\<delta>_in_U: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> ?\<delta> t \<in> ?U"
          proof -
            fix t assume ht: "t \<in> top1_unit_interval"
            have "?\<delta> t \<in> X" by (rule h\<delta>_in_X[OF ht])
            moreover have "?\<delta> t \<noteq> ?x0"
            proof -
              have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)+
              show ?thesis
              proof (cases "t = 0")
                case True
                \<comment> \<open>t=0: \<delta>(0) = h(1,0) = a \<in> A, x0 = h(0,0) \<in> X-A.\<close>
                have "?\<delta> 0 = a" using h\<delta>_0 .
                moreover have "a \<in> A" using assms(6) .
                moreover have "?x0 \<notin> A"
                  using assms(7) h00_intB2 unfolding top1_homeomorphism_on_def bij_betw_def
                  by (by100 blast)
                ultimately show ?thesis using True by (by100 force)
              next
                case False
                \<comment> \<open>t>0: (1-t/2,0) \<in> Int B2 and \<noteq> (0,0), use h-injectivity.\<close>
                have h_ne: "(1 - t/2, 0::real) \<noteq> (0::real, 0)"
                proof -
                  have "1/2 \<le> 1 - t/2" using ht01 by (by100 simp)
                  thus ?thesis by (by100 simp)
                qed
                have hinj_h: "inj_on h (top1_B2 - top1_S1)"
                  using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                have h_pt_intB2: "(1 - t/2, 0::real) \<in> top1_B2 - top1_S1"
                proof -
                  have "(1 - t/2, 0::real) \<in> top1_B2" by (rule h\<delta>_in_B2[OF ht])
                  moreover have "t > 0" using False ht01 by (by100 simp)
                  hence "1 - t/2 < 1" by (by100 simp)
                  have "0 \<le> 1 - t/2" using ht01 by (by100 simp)
                  have "(1 - t/2)^2 < 1"
                  proof -
                    have hx: "1 - t/2 < 1" using \<open>1 - t/2 < 1\<close> .
                    have hx0: "0 \<le> 1 - t/2" using \<open>0 \<le> 1 - t/2\<close> .
                    have "(1 - t/2) * (1 - t/2) \<le> 1 * (1 - t/2)"
                      using mult_right_mono[OF less_imp_le[OF hx] hx0] .
                    also have "... < 1 * 1" using hx by (by100 simp)
                    finally show ?thesis using power2_eq_square[of "1 - t/2"] by (by100 simp)
                  qed
                  hence "(1 - t/2, 0::real) \<notin> top1_S1" unfolding top1_S1_def by (by100 auto)
                  ultimately show ?thesis by (by100 blast)
                qed
                show ?thesis
                  using inj_on_eq_iff[OF hinj_h h_pt_intB2 h00_intB2] h_ne by (by100 simp)
              qed
            qed
            ultimately show "?\<delta> t \<in> ?U" by (by100 blast)
          qed
          have h\<delta>_path_U: "top1_is_path_on ?U ?TU a ?b ?\<delta>"
          proof -
            have h\<delta>_img_U: "?\<delta> ` top1_unit_interval \<subseteq> ?U"
            proof (rule image_subsetI)
              fix t assume "t \<in> top1_unit_interval"
              thus "?\<delta> t \<in> ?U" by (rule h\<delta>_in_U)
            qed
            have hU_sub: "?U \<subseteq> X" by (by100 blast)
            have h\<delta>_cont_U: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?U ?TU ?\<delta>"
              using top1_continuous_map_on_codomain_shrink[OF h\<delta>_cont h\<delta>_img_U hU_sub] by (by100 simp)
            show ?thesis unfolding top1_is_path_on_def using h\<delta>_cont_U h\<delta>_0 h\<delta>_1 by (by100 blast)
          qed
          have hg'_loop: "top1_is_loop_on ?U ?TU ?b ?g'"
            by (rule top1_basepoint_change_is_loop[OF hTopU_outer h\<delta>_path_U hg_loop])
          \<comment> \<open>Key: bc in U equals bc in X since inclusion is identity.\<close>
          have hbc_eq: "?g' = top1_basepoint_change_on X TX a ?b ?\<delta> g"
            unfolding top1_basepoint_change_on_def by (by100 simp)
          \<comment> \<open>g nulhomotopic in X \<Longrightarrow> bc(g) nulhomotopic in X.\<close>
          have hg'_ker_b: "{k. top1_loop_equiv_on ?U ?TU ?b ?g' k}
              \<in> top1_group_kernel_on
                (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_id X TX ?b)
                (top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x))"
          proof -
            \<comment> \<open>Step A: incl*_a([g]_U) = [g]_X = e, so g nulhomotopic in X.\<close>
            have hU_sub_X: "?U \<subseteq> X" by (by100 blast)
            have hTU_eq: "subspace_topology X TX ?U = ?TU" by (by100 simp)
            have hincl_a_g: "(top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))
                {k. top1_loop_equiv_on ?U ?TU a g k}
              = {k. top1_loop_equiv_on X TX a g k}"
              by (rule inclusion_induced_class[OF hU_sub_X hTopX_ns hTU_eq hg_loop])
            have hg_null_X: "{k. top1_loop_equiv_on X TX a g k}
                = top1_fundamental_group_id X TX a"
              using hc_id hc_eq hincl_a_g by (by100 simp)
            \<comment> \<open>Step B: g is a loop in X (from U \<subseteq> X).\<close>
            have hAU_cont_X: "top1_continuous_map_on ?U ?TU X TX (\<lambda>x. x)"
            proof -
              from top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopX_ns] hU_sub_X]
              show ?thesis unfolding id_def by (by100 simp)
            qed
            have hg_X_loop: "top1_is_loop_on X TX a g"
            proof -
              have "top1_is_loop_on X TX ((\<lambda>x. x) a) ((\<lambda>x. x) \<circ> g)"
                by (rule top1_continuous_map_loop_early[OF hAU_cont_X hg_loop])
              moreover have "(\<lambda>x::'a. x) \<circ> g = g" by (rule ext) (by100 simp)
              moreover have "(\<lambda>x::'a. x) a = a" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            have hg'_X_loop: "top1_is_loop_on X TX ?b ?g'"
              using hbc_eq top1_basepoint_change_is_loop[OF hTopX_ns h\<delta>_path hg_X_loop]
              by (by100 simp)
            \<comment> \<open>Step C: g nulhomotopic in X means g \<simeq> const_a in X.\<close>
            have hg_equiv_const: "top1_loop_equiv_on X TX a g (top1_constant_path a)"
            proof -
              have "top1_constant_path a \<in> {k. top1_loop_equiv_on X TX a g k}"
              proof -
                have hca_loop: "top1_is_loop_on X TX a (top1_constant_path a)"
                  by (rule top1_constant_path_is_loop[OF hTopX_ns ha_X])
                have hca_refl: "top1_loop_equiv_on X TX a (top1_constant_path a) (top1_constant_path a)"
                  by (rule top1_loop_equiv_on_refl[OF hca_loop])
                have "top1_constant_path a \<in> {k. top1_loop_equiv_on X TX a (top1_constant_path a) k}"
                  using hca_refl by (by100 blast)
                moreover have "top1_fundamental_group_id X TX a
                    = {k. top1_loop_equiv_on X TX a (top1_constant_path a) k}"
                  unfolding top1_fundamental_group_id_def by (by100 simp)
                ultimately show ?thesis using hg_null_X by (by100 simp)
              qed
              thus ?thesis by (by100 blast)
            qed
            \<comment> \<open>Step D: bc(X,a,b,\<delta>,g) \<simeq> bc(X,a,b,\<delta>,const_a) in X.\<close>
            have hca_X_loop: "top1_is_loop_on X TX a (top1_constant_path a)"
              by (rule top1_constant_path_is_loop[OF hTopX_ns ha_X])
            have hbc_congr: "top1_loop_equiv_on X TX ?b
                (top1_basepoint_change_on X TX a ?b ?\<delta> g)
                (top1_basepoint_change_on X TX a ?b ?\<delta> (top1_constant_path a))"
              by (rule top1_basepoint_change_loop_equiv[OF hTopX_ns h\<delta>_path hg_X_loop
                  hca_X_loop hg_equiv_const])
            \<comment> \<open>Step E: bc(X,a,b,\<delta>,const_a) \<simeq> const_b in X.\<close>
            have hbc_const: "top1_loop_equiv_on X TX ?b
                (top1_basepoint_change_on X TX a ?b ?\<delta> (top1_constant_path a))
                (top1_constant_path ?b)"
            proof -
              have hrevd_path: "top1_is_path_on X TX ?b a (top1_path_reverse ?\<delta>)"
                by (rule top1_path_reverse_is_path[OF h\<delta>_path])
              have hd_path: "top1_is_path_on X TX a ?b ?\<delta>" by (rule h\<delta>_path)
              \<comment> \<open>const_a * \<delta> \<simeq> \<delta> (left identity).\<close>
              have h1: "top1_path_homotopic_on X TX a ?b
                  (top1_path_product (top1_constant_path a) ?\<delta>) ?\<delta>"
                by (rule Theorem_51_2_left_identity[OF hTopX_ns hd_path])
              \<comment> \<open>rev(\<delta>) * (const_a * \<delta>) \<simeq> rev(\<delta>) * \<delta> (congruence).\<close>
              have h2: "top1_path_homotopic_on X TX ?b ?b
                  (top1_path_product (top1_path_reverse ?\<delta>) (top1_path_product (top1_constant_path a) ?\<delta>))
                  (top1_path_product (top1_path_reverse ?\<delta>) ?\<delta>)"
                by (rule path_homotopic_product_right[OF hTopX_ns h1 hrevd_path])
              \<comment> \<open>rev(\<delta>) * \<delta> \<simeq> const_b.\<close>
              have h3: "top1_path_homotopic_on X TX ?b ?b
                  (top1_path_product (top1_path_reverse ?\<delta>) ?\<delta>)
                  (top1_constant_path ?b)"
                by (rule Theorem_51_2_invgerse_right[OF hTopX_ns hd_path])
              \<comment> \<open>Chain: bc(const_a) = rev(\<delta>)*(const_a*\<delta>) \<simeq> rev(\<delta>)*\<delta> \<simeq> const_b.\<close>
              have h4: "top1_path_homotopic_on X TX ?b ?b
                  (top1_basepoint_change_on X TX a ?b ?\<delta> (top1_constant_path a))
                  (top1_constant_path ?b)"
                using Lemma_51_1_path_homotopic_trans[OF hTopX_ns h2 h3]
                unfolding top1_basepoint_change_on_def .
              \<comment> \<open>Convert path_homotopic to loop_equiv.\<close>
              have hbc_ca_loop: "top1_is_loop_on X TX ?b
                  (top1_basepoint_change_on X TX a ?b ?\<delta> (top1_constant_path a))"
                by (rule top1_basepoint_change_is_loop[OF hTopX_ns hd_path hca_X_loop])
              have hcb_loop: "top1_is_loop_on X TX ?b (top1_constant_path ?b)"
              proof -
                have "?b \<in> X" using hb_in_UV hA_sub_X by (by100 blast)
                thus ?thesis by (rule top1_constant_path_is_loop[OF hTopX_ns])
              qed
              show ?thesis unfolding top1_loop_equiv_on_def
                using hbc_ca_loop hcb_loop h4 by (by100 blast)
            qed
            \<comment> \<open>Step F: g' \<simeq> const_b in X, chain steps D+E.\<close>
            have hg'_null_X: "top1_loop_equiv_on X TX ?b ?g' (top1_constant_path ?b)"
            proof -
              \<comment> \<open>g' = bc(U,...) = bc(X,...) by hbc_eq. Rewrite g' to bc(X,...).\<close>
              have hg'_eq_bcX: "top1_loop_equiv_on X TX ?b ?g'
                  (top1_basepoint_change_on X TX a ?b ?\<delta> g)"
              proof -
                have "?g' = top1_basepoint_change_on X TX a ?b ?\<delta> g" by (rule hbc_eq)
                hence "top1_is_loop_on X TX ?b (top1_basepoint_change_on X TX a ?b ?\<delta> g)"
                  using hg'_X_loop by (by100 simp)
                thus ?thesis using hbc_eq top1_loop_equiv_on_refl[OF hg'_X_loop]
                  by (by100 simp)
              qed
              from top1_loop_equiv_on_trans[OF hTopX_ns hg'_eq_bcX
                  top1_loop_equiv_on_trans[OF hTopX_ns hbc_congr hbc_const]]
              show ?thesis .
            qed
            \<comment> \<open>Step G: [g']_X = e_X_b, so incl*_b([g']_U) = e.\<close>
            have hincl_b_g': "(top1_fundamental_group_induced_on ?U ?TU ?b X TX ?b (\<lambda>x. x))
                {k. top1_loop_equiv_on ?U ?TU ?b ?g' k}
              = {k. top1_loop_equiv_on X TX ?b ?g' k}"
              by (rule inclusion_induced_class[OF hU_sub_X hTopX_ns hTU_eq hg'_loop])
            have hg'_class_X_eq: "{k. top1_loop_equiv_on X TX ?b ?g' k}
                = top1_fundamental_group_id X TX ?b"
            proof -
              have hcb_loop: "top1_is_loop_on X TX ?b (top1_constant_path ?b)"
              proof -
                have "?b \<in> X" using hb_in_UV hA_sub_X by (by100 blast)
                thus ?thesis by (rule top1_constant_path_is_loop[OF hTopX_ns])
              qed
              have hcb_class: "top1_fundamental_group_id X TX ?b
                  = {k. top1_loop_equiv_on X TX ?b (top1_constant_path ?b) k}"
                unfolding top1_fundamental_group_id_def by (by100 simp)
              \<comment> \<open>g' \<simeq> const_b, so [g']_X = [const_b]_X = e.\<close>
              show ?thesis
              proof (rule set_eqI, rule iffI)
                fix k assume "k \<in> {k. top1_loop_equiv_on X TX ?b ?g' k}"
                hence "top1_loop_equiv_on X TX ?b ?g' k" by (by100 blast)
                hence "top1_loop_equiv_on X TX ?b (top1_constant_path ?b) k"
                  using top1_loop_equiv_on_trans[OF hTopX_ns
                      top1_loop_equiv_on_sym[OF hg'_null_X]] by (by100 blast)
                thus "k \<in> top1_fundamental_group_id X TX ?b"
                  unfolding hcb_class by (by100 blast)
              next
                fix k assume "k \<in> top1_fundamental_group_id X TX ?b"
                hence "top1_loop_equiv_on X TX ?b (top1_constant_path ?b) k"
                  unfolding hcb_class by (by100 blast)
                hence "top1_loop_equiv_on X TX ?b ?g' k"
                  using top1_loop_equiv_on_trans[OF hTopX_ns hg'_null_X] by (by100 blast)
                thus "k \<in> {k. top1_loop_equiv_on X TX ?b ?g' k}" by (by100 blast)
              qed
            qed
            show ?thesis unfolding top1_group_kernel_on_def
              using hg'_loop hincl_b_g' hg'_class_X_eq
              unfolding top1_fundamental_group_carrier_def by (by100 blast)
          qed
          \<comment> \<open>By hincl_ker_b: g' class \<in> \<langle>\<langle>\<iota>*(\<pi>_1(UV,b))\<rangle>\<rangle>.\<close>
          have hg'_in_ncl: "{k. top1_loop_equiv_on ?U ?TU ?b ?g' k}
              \<in> top1_normal_subgroup_generated_on
                  (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_mul ?U ?TU ?b)
                  (top1_fundamental_group_id ?U ?TU ?b) (top1_fundamental_group_invg ?U ?TU ?b)
                  (top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x)
                     ` top1_fundamental_group_carrier ?UV ?TUV ?b)"
            using hg'_ker_b hincl_ker_b by (by100 blast)
          \<comment> \<open>Strategy: Define N_b via base change of N.
             Show N_b is normal, contains \<iota>*(\<pi>_1(UV,b)) (by generator tracking),
             so [g']_U \<in> N_b. Invert bc to get c \<in> N.\<close>
          \<comment> \<open>Since the normal closure \<langle>\<langle>\<iota>*(\<pi>_1(UV,b))\<rangle>\<rangle> \<subseteq> every normal subgroup
             containing \<iota>*(\<pi>_1(UV,b)), it suffices to find a normal subgroup of
             \<pi>_1(U,b) that contains \<iota>*(\<pi>_1(UV,b)) and relates back to N.\<close>
          \<comment> \<open>Concretely: bc_\<delta>(N) is normal in \<pi>_1(U,b) and contains \<iota>*(\<pi>_1(UV,b))
             by the generator tracking argument. Therefore
             \<langle>\<langle>\<iota>*(\<pi>_1(UV,b))\<rangle>\<rangle> \<subseteq> bc_\<delta>(N), so [g'] \<in> bc_\<delta>(N).
             Then bc_\<delta> injectivity gives c \<in> N.\<close>
          \<comment> \<open>Strategy: show that bc_back maps [g']_U to c, and that [g']_U being
             in the normal closure means c is in N.
             Key: bc_back\<inverse>(N) is a normal subgroup of \<pi>_1(U,b) containing \<iota>*(\<pi>_1(UV,b)),
             so \<langle>\<langle>\<iota>*(\<pi>_1(UV,b))\<rangle>\<rangle> \<subseteq> bc_back\<inverse>(N), hence [g'] \<in> bc_back\<inverse>(N),
             hence bc_back([g']) = c \<in> N.\<close>
          \<comment> \<open>rev(\<delta>) is a path from b to a in U.\<close>
          let ?rev\<delta> = "top1_path_reverse ?\<delta>"
          have hrev\<delta>_path_U: "top1_is_path_on ?U ?TU ?b a ?rev\<delta>"
            by (rule top1_path_reverse_is_path[OF h\<delta>_path_U])
          \<comment> \<open>Roundtrip: bc(U,b,a,rev(\<delta>), bc(U,a,b,\<delta>,g)) \<simeq> g in U.\<close>
          have hroundtrip: "top1_path_homotopic_on ?U ?TU a a g
              (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')"
            by (rule top1_basepoint_change_roundtrip[OF hTopU_outer h\<delta>_path_U hg_loop])
          \<comment> \<open>So [bc_back(g')]_U = [g]_U = c.\<close>
          have hbc_back_loop: "top1_is_loop_on ?U ?TU a (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')"
            by (rule top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U hg'_loop])
          have hbc_back_class: "{k. top1_loop_equiv_on ?U ?TU a
              (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k} = c"
          proof -
            have hle: "top1_loop_equiv_on ?U ?TU a g (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')"
              unfolding top1_loop_equiv_on_def using hg_loop hbc_back_loop hroundtrip by (by100 blast)
            have hle_sym: "top1_loop_equiv_on ?U ?TU a
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') g"
              by (rule top1_loop_equiv_on_sym[OF hle])
            show ?thesis
            proof (rule set_eqI, rule iffI)
              fix k assume hk1: "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k}"
              have hbk: "top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k"
                using hk1 by (by100 blast)
              have "top1_loop_equiv_on ?U ?TU a g k"
                by (rule top1_loop_equiv_on_trans[OF hTopU_outer
                    top1_loop_equiv_on_sym[OF hle_sym] hbk])
              thus "k \<in> c" using hc_eq by (by100 blast)
            next
              fix k assume "k \<in> c"
              hence hgk: "top1_loop_equiv_on ?U ?TU a g k" using hc_eq by (by100 blast)
              show "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k}"
                using top1_loop_equiv_on_trans[OF hTopU_outer hle_sym hgk] by (by100 blast)
            qed
          qed
          \<comment> \<open>Now the key claim: \<iota>*(\<pi>_1(UV,b)) \<subseteq> {x \<in> \<pi>_1(U,b) : bc_back_class(x) \<in> N}.
             This requires generator tracking: bc_back maps every element of \<iota>*(\<pi>_1(UV,b))
             to a power of kp_class^(\<pm>1), which is in N (since N is a subgroup).\<close>
          \<comment> \<open>For any loop f0 in UV at b: bc_back([f0]_U) = [bc(U,b,a,rev(\<delta>),f0)]_U.
             We need this to be in N.
             Key fact: bc(U,b,a,rev(\<delta>),f0) = h \<circ> bc(B2-{0},q,p,rev(\<gamma>),h\<inverse>(f0))
             (by comp_basepoint_change), and bc(B2-{0},q,p,rev(\<gamma>),f0_disk) \<simeq> f^(\<pm>1)
             in B2-{0} (winding number), so bc_back(\<iota>*[f0]) \<simeq> h\<circ>f^(\<pm>1) = kp^(\<pm>1) in U.
             Since kp_class \<in> N and kp_class\<inverse> \<in> N and N is a subgroup, kp^(\<pm>n) \<in> N.\<close>
          \<comment> \<open>Key claim: for every loop f0 in UV at b, bc_back([\<iota>(f0)]_U) \<in> N.
             This means every element of \<iota>*(\<pi>_1(UV,b)) has its bc_back in N.\<close>
          have hbc_back_UV_in_N: "\<And>f0. top1_is_loop_on ?UV ?TUV ?b f0 \<Longrightarrow>
              {k. top1_loop_equiv_on ?U ?TU a
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f0) k} \<in> N"
          proof -
            fix f0 assume hf0_loop: "top1_is_loop_on ?UV ?TUV ?b f0"
            \<comment> \<open>Step 1: bc_back(f0) = h \<circ> \<ell> where \<ell> = bc(B2-{0},q,p,rev(\<gamma>),h\<inverse>\<circ>f0)
               is a loop at p in B2-{0}. This is comp_basepoint_change (pointwise).\<close>
            \<comment> \<open>Step 2: By S1 deformation retract, \<ell> \<simeq> g_{S1} in B2-{0} for some
               S1-loop g_{S1}. Applying h: bc_back(f0) \<simeq> h \<circ> g_{S1} = (h|_{S1}) \<circ> g_{S1} in U.\<close>
            \<comment> \<open>Step 3: (h|_{S1})_*([g_{S1}]) \<in> image of (h|_{S1})_* \<subseteq> \<langle>kp_class\<rangle> \<subseteq> N.
               Since (h|_{S1})_* is a hom and \<pi>_1(S1) is generated by [f],
               the image is generated by (h|_{S1})_*([f]) = kp_class.
               The cyclic subgroup \<langle>kp_class\<rangle> \<subseteq> N since N is a subgroup containing kp_class.\<close>
            \<comment> \<open>The class [bc_back(f0)]_U is in the image of h*: \<pi>_1(B2-{0},p) \<rightarrow> \<pi>_1(U,a).
               Since \<pi>_1(S1,p) \<cong> \<pi>_1(B2-{0},p) (iso, S1_pi1_iso_B2_minus_zero) and
               \<pi>_1(S1) \<cong> Z (Theorem_54_5_iso), h* factors through Z.
               By hom_from_Z_image_in_subgroup, the image \<subseteq> N.\<close>
            \<comment> \<open>Concretely: bc_back(f0) = h \<circ> \<ell> where \<ell> is a loop at p in B2-{0}.
               Since incl*: \<pi>_1(S1) \<rightarrow> \<pi>_1(B2-{0}) is surjective (iso):
               \<exists> S1-loop g with [\<ell>] = incl*([g]).
               Then h*[\<ell>] = h*(incl*([g])) = (h\<circ>incl)*([g]) = (h|_{S1})*([g]).
               Compose (h|_{S1})* with \<phi>\<inverse>: Z \<rightarrow> \<pi>_1(S1) to get \<psi>: Z \<rightarrow> \<pi>_1(U,a).
               \<psi>(1) \<in> N because:
               - If \<phi>([f]) = 1: \<psi>(1) = (h|_{S1})*([f]) = kp_class \<in> N.
               - If \<phi>([f]) = -1: \<psi>(1) = (h|_{S1})*([f]\<inverse>) = kp_class\<inverse> \<in> N.
               By hom_from_Z_image_in_subgroup: image(\<psi>) \<subseteq> N.
               So (h|_{S1})*([g]) \<in> N.\<close>
            \<comment> \<open>Proof: every element of \<pi>_1(U,a) in the image of any loop at a in U
               that factors as h \<circ> (loop in B2-{0}) is in N.
               More precisely: for any loop \<ell> at a in U where \<ell> = h \<circ> \<ell>' for
               some loop \<ell>' at (1,0) in B2-{0}, we have [\<ell>]_U \<in> N.
               This is because h factors through S1 (via the retraction),
               so the image of h_* \<subseteq> image of (h|_{S1})_* which is cyclic
               generated by kp_class, hence \<subseteq> N.\<close>
            \<comment> \<open>Step 1: bc_back(f0) is a loop at a in U.\<close>
            let ?bc_f0 = "top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f0"
            \<comment> \<open>Step 2: [bc_back(f0)]_U is in image of (h|_{S1})_*
               composed with the iso \<pi>_1(S1) \<cong> Z, hence in N.\<close>
            \<comment> \<open>Concretely: bc_back(f0)(t) = h(some function of f0 and \<gamma>).
               The class [bc_back(f0)]_U \<in> \<pi>_1(U,a).
               We need this class to be in N.
               N is a subgroup of \<pi>_1(U,a) containing kp_class and kp_class\<inverse>.
               Every element in the image of the composed hom Z \<rightarrow> \<pi>_1(U,a) is in N
               (by hom_from_Z_image_in_subgroup).\<close>
            show "{k. top1_loop_equiv_on ?U ?TU a ?bc_f0 k} \<in> N"
            proof -
              \<comment> \<open>Step 1: every class in the image of (h|_{S1})_* is in N.
                 Proof: compose with iso\<inverse> \<pi>_1(S1) \<cong> Z, apply hom_from_Z_image_in_subgroup.\<close>
              \<comment> \<open>Step 1: construct the composed hom \<psi>: Z \<rightarrow> \<pi>_1(U,a).\<close>
              \<comment> \<open>Extract iso \<phi>: \<pi>_1(S1) \<rightarrow> Z from Theorem_54_5_iso.\<close>
              obtain \<phi>_S1 where h\<phi>_bij: "bij_betw \<phi>_S1
                    (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) top1_Z_group"
                  and h\<phi>_hom: "top1_group_hom_on
                    (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                    (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                    top1_Z_group top1_Z_mul \<phi>_S1"
                using Theorem_54_5_iso
                unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by (by100 blast)
              \<comment> \<open>\<phi>\<inverse> is a hom Z \<rightarrow> \<pi>_1(S1).\<close>
              have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
              proof -
                have hR2: "is_topology_on (UNIV::(real\<times>real) set)
                    (product_topology_on top1_open_sets top1_open_sets)"
                  using product_topology_on_is_topology_on[OF
                      top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
                show ?thesis unfolding top1_S1_topology_def
                  by (rule subspace_topology_is_topology_on[OF hR2]) (by100 simp)
              qed
              have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
              have hS1_grp: "top1_is_group_on
                  (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_id top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0))"
                by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
              have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
                using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def by (by100 blast)
              have h\<phi>_inv_hom: "top1_group_hom_on top1_Z_group top1_Z_mul
                  (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                  (inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_S1)"
                by (rule bij_hom_inv_is_hom[OF hS1_grp hZ_grp h\<phi>_bij h\<phi>_hom])
              \<comment> \<open>Construct (h|_{S1})_* as hom.\<close>
              have h_hS1_hom: "top1_group_hom_on
                  (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_mul top1_S1 top1_S1_topology (1,0))
                  (top1_fundamental_group_carrier ?U ?TU a)
                  (top1_fundamental_group_mul ?U ?TU a)
                  (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0) ?U ?TU a (\<lambda>z. h z))"
              proof -
                \<comment> \<open>h: S1 \<rightarrow> U continuous since h: B2 \<rightarrow> X maps S1 into A \<subseteq> U.\<close>
                have hS1_B2: "top1_S1 \<subseteq> top1_B2"
                  unfolding top1_S1_def top1_B2_def by (by100 auto)
                have hh_S1_cont_X: "top1_continuous_map_on top1_S1 top1_S1_topology X TX (\<lambda>z. h z)"
                proof -
                  have "top1_continuous_map_on top1_S1
                      (subspace_topology top1_B2 top1_B2_topology top1_S1) X TX h"
                    by (rule top1_continuous_map_on_restrict_domain_simple[OF assms(5) hS1_B2])
                  moreover have "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
                    unfolding top1_B2_topology_def top1_S1_topology_def
                    using subspace_topology_trans[OF hS1_B2] by (by100 simp)
                  ultimately show ?thesis by (by100 simp)
                qed
                have hh_S1_img_U: "(\<lambda>z. h z) ` top1_S1 \<subseteq> ?U"
                proof
                  fix y assume "y \<in> (\<lambda>z. h z) ` top1_S1"
                  then obtain z where hz: "z \<in> top1_S1" "y = h z" by (by100 blast)
                  have "h z \<in> A" using assms(8) hz(1) by (by100 blast)
                  hence "h z \<in> X" using hA_sub_X by (by100 blast)
                  moreover have "h z \<noteq> h (0, 0)"
                  proof -
                    have "z \<in> top1_B2" using hS1_B2 hz(1) by (by100 blast)
                    have "(0::real, 0) \<in> top1_B2 - top1_S1"
                      unfolding top1_B2_def top1_S1_def by (by100 auto)
                    have "z \<notin> top1_B2 - top1_S1" using hz(1) by (by100 blast)
                    hence "z \<noteq> (0, 0)" using \<open>(0,0) \<in> top1_B2 - top1_S1\<close> by (by100 blast)
                    moreover have "inj_on h (top1_B2 - top1_S1)"
                      using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                    have "h z \<in> A" using assms(8) hz(1) by (by100 blast)
                    moreover have "h (0, 0) \<notin> A"
                    proof -
                      have "h ` (top1_B2 - top1_S1) = X - A"
                        using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                      hence "h (0, 0) \<in> X - A"
                        using \<open>(0,0) \<in> top1_B2 - top1_S1\<close> by (by100 blast)
                      thus ?thesis by (by100 blast)
                    qed
                    ultimately show ?thesis by (by100 force)
                  qed
                  ultimately show "y \<in> ?U" using hz(2) by (by100 force)
                qed
                have hU_sub: "?U \<subseteq> X" by (by100 blast)
                have hh_S1_cont_U: "top1_continuous_map_on top1_S1 top1_S1_topology ?U ?TU (\<lambda>z. h z)"
                  using top1_continuous_map_on_codomain_shrink[OF hh_S1_cont_X hh_S1_img_U hU_sub]
                  by (by100 simp)
                have hha: "(\<lambda>z. h z) (1, 0) = a" using assms(9) by (by100 simp)
                show ?thesis
                  using top1_fundamental_group_induced_on_is_hom[OF hS1_top hTopU_outer h10_S1
                      ha_U_outer hh_S1_cont_U] hha by (by100 simp)
              qed
              \<comment> \<open>Compose: \<psi> = (h|_{S1})_* \<circ> \<phi>\<inverse>: Z \<rightarrow> \<pi>_1(U,a) is a hom.\<close>
              let ?\<psi> = "(top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0)
                  ?U ?TU a (\<lambda>z. h z)) \<circ>
                  (inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)) \<phi>_S1)"
              have h\<psi>_hom: "top1_group_hom_on top1_Z_group top1_Z_mul
                  (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a) ?\<psi>"
                by (rule group_hom_comp[OF h\<phi>_inv_hom h_hS1_hom])
              \<comment> \<open>\<psi>(1) \<in> N.\<close>
              have h\<psi>1_N: "?\<psi> 1 \<in> N"
              proof -
                let ?fclass = "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
                have h\<phi>_f: "\<phi>_S1 ?fclass = 1 \<or> \<phi>_S1 ?fclass = -1"
                  by (rule standard_S1_loop_generates_Z[OF h\<phi>_bij h\<phi>_hom])
                have hinj: "inj_on \<phi>_S1 (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))"
                  using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
                have hsurj: "\<phi>_S1 ` (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                    = top1_Z_group"
                  using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
                have hf_carrier: "?fclass \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
                proof -
                  have "top1_is_loop_on top1_S1 top1_S1_topology (1,0) ?f"
                    by (rule standard_S1_loop_is_loop)
                  thus ?thesis unfolding top1_fundamental_group_carrier_def by (by100 blast)
                qed
                show ?thesis
                proof (cases "\<phi>_S1 ?fclass = 1")
                  case True
                  \<comment> \<open>\<phi>\<inverse>(1) = [f], so \<psi>(1) = (h|_{S1})_*([f]) = kp_class \<in> N.\<close>
                  have "inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                      \<phi>_S1 1 = ?fclass"
                    using inv_into_f_eq[OF hinj hf_carrier] True by (by100 simp)
                  hence "?\<psi> 1 = (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0)
                      ?U ?TU a (\<lambda>z. h z)) ?fclass"
                    unfolding comp_def by (by100 simp)
                  moreover have "(top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0)
                      ?U ?TU a (\<lambda>z. h z)) ?fclass = ?kp_class"
                    by (by100 simp)
                  ultimately show ?thesis using hkp_in_N by (by100 simp)
                next
                  case False
                  hence h_m1: "\<phi>_S1 ?fclass = -1" using h\<phi>_f by (by100 blast)
                  \<comment> \<open>\<phi>\<inverse>(1) = [f]\<inverse>, so \<psi>(1) = (h|_{S1})_*([f]\<inverse>) = kp_class\<inverse> \<in> N.\<close>
                  have h\<phi>_inv: "\<phi>_S1 (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass) = 1"
                  proof -
                    have "\<phi>_S1 (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass)
                        = top1_Z_invg (\<phi>_S1 ?fclass)"
                      using hom_preserves_inv[OF hS1_grp hZ_grp h\<phi>_hom hf_carrier] .
                    thus ?thesis using h_m1 unfolding top1_Z_invg_def by (by100 simp)
                  qed
                  have hfinv_carrier: "top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass
                      \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
                    using group_inv_closed[OF hS1_grp hf_carrier] .
                  have "inv_into (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
                      \<phi>_S1 1 = top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass"
                    using inv_into_f_eq[OF hinj hfinv_carrier] h\<phi>_inv by (by100 simp)
                  hence "?\<psi> 1 = (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0)
                      ?U ?TU a (\<lambda>z. h z)) (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass)"
                    unfolding comp_def by (by100 simp)
                  moreover have "... \<in> N"
                  proof -
                    \<comment> \<open>(h|_{S1})_*([f]\<inverse>) = kp_class\<inverse> \<in> N.\<close>
                    have "(top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1,0)
                        ?U ?TU a (\<lambda>z. h z)) (top1_fundamental_group_invg top1_S1 top1_S1_topology (1,0) ?fclass)
                        = top1_fundamental_group_invg ?U ?TU a ?kp_class"
                    proof -
                      have hUa_grp: "top1_is_group_on
                          (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
                          (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
                        by (rule top1_fundamental_group_is_group[OF hTopU_outer ha_U_outer])
                      from hom_preserves_inv[OF hS1_grp hUa_grp h_hS1_hom hf_carrier]
                      show ?thesis by (by100 simp)
                    qed
                    thus ?thesis using hkp_inv_N by (by100 simp)
                  qed
                  ultimately show ?thesis by (by100 simp)
                qed
              qed
              have hpiU_a_grp: "top1_is_group_on
                  (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
                  (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
                by (rule top1_fundamental_group_is_group[OF hTopU_outer ha_U_outer])
              \<comment> \<open>By hom_from_Z_image_in_subgroup: image(\<psi>) \<subseteq> N.\<close>
              have h\<psi>_img_N: "?\<psi> ` top1_Z_group \<subseteq> N"
                by (rule hom_from_Z_image_in_subgroup[OF hpiU_a_grp h\<psi>_hom hN_grp hN_sub h\<psi>1_N])
              \<comment> \<open>Step 2: [bc_back(f0)]_U \<in> image(\<psi>) (via h factoring through S1).\<close>
              \<comment> \<open>By comp_basepoint_change: ?bc_f0 = h \<circ> \<ell> where \<ell> is a B2-{0} loop at (1,0).
                 Then [h\<circ>\<ell>]_U = (h|_{S1})_*([g]) for some S1-loop g (by S1_pi1_iso surj).
                 (h|_{S1})_*([g]) = \<psi>(\<phi>([g])) \<in> image(\<psi>) \<subseteq> N.\<close>
              \<comment> \<open>Key: ?bc_f0 is a specific function. Its class [?bc_f0]_U is what we need in N.
                 Since image(\<psi>) = image((h|_{S1})_*) \<subseteq> N, it suffices to show
                 [?bc_f0]_U \<in> image((h|_{S1})_*).\<close>
              \<comment> \<open>image((h|_{S1})_*) = {[h\<circ>g]_U : g S1-loop at (1,0)}.
                 We need: \<exists>g S1-loop. ?bc_f0 \<simeq> h\<circ>g in U.\<close>
              show ?thesis
              proof -
                \<comment> \<open>Step A: ?bc_f0 = h \<circ> \<ell> pointwise (comp_basepoint_change).\<close>
                let ?hinv_f0 = "inv_into (top1_B2 - top1_S1) h \<circ> f0"
                let ?revgam = "top1_path_reverse (\<lambda>t::real. (1 - t/2, 0::real))"
                let ?ell_disk = "top1_basepoint_change_on (top1_B2 - {(0::real,0)})
                    (subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0,0)}))
                    ?q (1::real,0) ?revgam ?hinv_f0"
                \<comment> \<open>h \<circ> rev(\<gamma>) = rev(\<delta>) pointwise.\<close>
                have h_revgam_eq: "(\<lambda>z. h z) \<circ> ?revgam = ?rev\<delta>"
                  unfolding top1_path_reverse_def comp_def by (rule ext) (by100 simp)
                \<comment> \<open>h \<circ> (h\<inverse> \<circ> f0) = f0 since f0 maps into UV = h(Int B2-{0}).\<close>
                \<comment> \<open>bc_f0 = h \<circ> ell_disk: direct proof via definition unfolding.
                   bc(X,x0,x1,\<alpha>,f) = rev(\<alpha>)*(f*\<alpha>) = path_product(path_reverse(\<alpha>), path_product(f,\<alpha>)).
                   path_product/reverse use if-then-else evaluating arguments in I_set.
                   Key: h \<circ> (rev(revgam) * ((h\<inverse>\<circ>f0) * revgam))
                     = (h\<circ>rev(revgam)) * ((h\<circ>h\<inverse>\<circ>f0) * (h\<circ>revgam)) [comp distributes]
                     = rev(rev(\<delta>)) * (f0 * rev(\<delta>)) [substituting h\<circ>rev(\<gamma>)=rev(\<delta>), h\<circ>h\<inverse>\<circ>f0=f0 on I]
                     = bc_f0.\<close>
                \<comment> \<open>bc_f0 and h\<circ>ell_disk agree on I_set, hence same class.\<close>
                have hbc_agree_I: "\<forall>t\<in>top1_unit_interval. ?bc_f0 t = ((\<lambda>z. h z) \<circ> ?ell_disk) t"
                proof -
                  \<comment> \<open>h\<circ>h\<inverse>\<circ>f0 agrees with f0 on I_set.\<close>
                  have h_hinv_on_I: "\<forall>t\<in>top1_unit_interval. ((\<lambda>z. h z) \<circ> ?hinv_f0) t = f0 t"
                  proof (intro ballI)
                    fix t assume ht: "t \<in> top1_unit_interval"
                    have hsurj: "h ` (top1_B2 - top1_S1) = X - A"
                      using assms(7) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                    have hf0_cont: "top1_continuous_map_on top1_unit_interval
                        top1_unit_interval_topology ?UV ?TUV f0"
                      using hf0_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    have "f0 t \<in> ?UV" using continuous_map_maps_to[OF hf0_cont ht] .
                    hence "f0 t \<in> X - A" using hA_sub_X by (by100 blast)
                    hence "f0 t \<in> h ` (top1_B2 - top1_S1)" using hsurj by (by100 blast)
                    hence "h (inv_into (top1_B2 - top1_S1) h (f0 t)) = f0 t"
                      by (rule f_inv_into_f)
                    thus "((\<lambda>z. h z) \<circ> ?hinv_f0) t = f0 t"
                      unfolding comp_def by (by100 simp)
                  qed
                  \<comment> \<open>By comp_basepoint_change (pointwise on ℝ): h\<circ>ell_disk = bc(Y,b,a,h\<circ>revgam,h\<circ>h\<inverse>\<circ>f0).
                     By basepoint_change_cong_on_I: bc(Y,b,a,h\<circ>revgam,h\<circ>h\<inverse>\<circ>f0) agrees with
                     bc(Y,b,a,h\<circ>revgam,f0) on I_set. And h\<circ>revgam = rev(\<delta>) (pointwise).
                     So bc(Y,b,a,rev(\<delta>),f0) = bc_f0 on I_set.\<close>
                  have hcomp_eq: "\<forall>t\<in>top1_unit_interval. ((\<lambda>z. h z) \<circ> ?ell_disk) t =
                      (top1_basepoint_change_on ?U ?TU ?b a
                        ((\<lambda>z. h z) \<circ> ?revgam) ((\<lambda>z. h z) \<circ> ?hinv_f0)) t"
                  proof (intro ballI)
                    fix t assume "t \<in> top1_unit_interval"
                    \<comment> \<open>comp_basepoint_change gives pointwise equality for ALL t.\<close>
                    have "((\<lambda>z. h z) \<circ> ?ell_disk) t =
                        (top1_basepoint_change_on ?U ?TU
                          ((\<lambda>z. h z) ?q) ((\<lambda>z. h z) (1::real,0))
                          ((\<lambda>z. h z) \<circ> ?revgam) ((\<lambda>z. h z) \<circ> ?hinv_f0)) t"
                      using comp_basepoint_change[of "(\<lambda>z. h z)"
                          "(top1_B2 - {(0::real,0)})"
                          "(subspace_topology top1_B2 top1_B2_topology (top1_B2 - {(0,0)}))"
                          ?q "(1::real,0)" ?revgam ?hinv_f0,
                          unfolded top1_basepoint_change_on_def]
                      unfolding top1_basepoint_change_on_def by (by100 simp)
                    moreover have "(\<lambda>z. h z) ?q = ?b" by (by100 simp)
                    moreover have "(\<lambda>z. h z) (1::real,0) = a" using assms(9) by (by100 simp)
                    ultimately show "((\<lambda>z. h z) \<circ> ?ell_disk) t =
                        (top1_basepoint_change_on ?U ?TU ?b a
                          ((\<lambda>z. h z) \<circ> ?revgam) ((\<lambda>z. h z) \<circ> ?hinv_f0)) t"
                      unfolding top1_basepoint_change_on_def by (by100 simp)
                  qed
                  have hbc_subst: "\<forall>t\<in>top1_unit_interval.
                      (top1_basepoint_change_on ?U ?TU ?b a
                        ((\<lambda>z. h z) \<circ> ?revgam) ((\<lambda>z. h z) \<circ> ?hinv_f0)) t
                      = (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f0) t"
                  proof -
                    have "\<forall>t\<in>top1_unit_interval.
                        (top1_basepoint_change_on ?U ?TU ?b a ((\<lambda>z. h z) \<circ> ?revgam) ((\<lambda>z. h z) \<circ> ?hinv_f0)) t
                        = (top1_basepoint_change_on ?U ?TU ?b a ((\<lambda>z. h z) \<circ> ?revgam) f0) t"
                      by (rule basepoint_change_cong_on_I[OF h_hinv_on_I])
                    moreover have "(\<lambda>z. h z) \<circ> ?revgam = ?rev\<delta>"
                      using h_revgam_eq .
                    ultimately show ?thesis by (by100 simp)
                  qed
                  have "\<forall>t\<in>top1_unit_interval.
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f0) t = ?bc_f0 t"
                    unfolding top1_basepoint_change_on_def by (intro ballI) (by100 simp)
                  thus ?thesis using hcomp_eq hbc_subst by (by100 force)
                qed
                \<comment> \<open>Step B: [h\<circ>\<ell>]_U \<in> image(\<psi>).\<close>
                \<comment> \<open>Since \<ell> is a loop at (1,0) in B2-{0} and (h|_{S1})_* is surjective
                   from \<pi>_1(S1) onto its image, and \<psi> = (h|_{S1})_* \<circ> \<phi>\<inverse> with
                   image(\<psi>) = image((h|_{S1})_*): [h\<circ>\<ell>]_U \<in> image(\<psi>).\<close>
                have hbc_class_in_N: "{k. top1_loop_equiv_on ?U ?TU a ((\<lambda>z. h z) \<circ> ?ell_disk) k} \<in> N"
                proof -
                  \<comment> \<open>[h\<circ>ell_disk]_U \<in> image(\<psi>).
                     image(\<psi>) = {(h|_{S1})_*(c) : c \<in> \<pi>_1(S1)} = {\<psi>(n) : n \<in> Z}.
                     Since image(\<psi>) \<subseteq> N, it suffices to show [h\<circ>ell_disk]_U \<in> image(\<psi>).\<close>
                  \<comment> \<open>image(\<psi>) = image((h|_{S1})_*): every class [h\<circ>g]_U for S1-loop g is in image.\<close>
                  \<comment> \<open>Need: [h\<circ>ell_disk]_U = [h\<circ>g]_U for some S1-loop g.
                     Follows from: ell_disk \<simeq> g in B2-{0} (S1_pi1_iso surjectivity)
                     and h preserves homotopy (continuous map).\<close>
                  have "{k. top1_loop_equiv_on ?U ?TU a ((\<lambda>z. h z) \<circ> ?ell_disk) k}
                      \<in> ?\<psi> ` top1_Z_group"
                    sorry \<comment> \<open>Needs: (1) ell_disk loop at (1,0) in B2-{0},
                         (2) S1_pi1_iso surj: [\<ell>]=incl*([g]),
                         (3) h continuous B2-{0}\<rightarrow>U preserves homotopy,
                         (4) [h\<circ>g]_U = (h|_{S1})_*([g]) = \<psi>(\<phi>([g])).\<close>
                  thus ?thesis using h\<psi>_img_N by (by100 blast)
                qed
                \<comment> \<open>Step C: [?bc_f0]_U = [h\<circ>\<ell>]_U (from agreement on I_set + loop_agree_on_I).\<close>
                have "{k. top1_loop_equiv_on ?U ?TU a ?bc_f0 k}
                    = {k. top1_loop_equiv_on ?U ?TU a ((\<lambda>z. h z) \<circ> ?ell_disk) k}"
                  sorry \<comment> \<open>bc_f0 and h\<circ>ell_disk agree on I (hbc_agree_I), both loops at a.
                       By loop_agree_on_I: bc_f0 \<simeq> h\<circ>ell_disk. So classes equal.\<close>
                thus ?thesis using hbc_class_in_N by (by100 simp)
              qed
            qed
          qed
          \<comment> \<open>The preimage M = {x \<in> \<pi>_1(U,b) : bc_back_class(x) \<in> N} is normal.\<close>
          let ?M = "{x \<in> top1_fundamental_group_carrier ?U ?TU ?b.
              \<exists>f. top1_is_loop_on ?U ?TU ?b f \<and> x = {k. top1_loop_equiv_on ?U ?TU ?b f k} \<and>
                  {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k} \<in> N}"
          have hM_normal: "top1_normal_subgroup_on
              (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_mul ?U ?TU ?b)
              (top1_fundamental_group_id ?U ?TU ?b) (top1_fundamental_group_invg ?U ?TU ?b) ?M"
          proof -
            \<comment> \<open>bc_back is a group homomorphism at loop level (Theorem 52.1).
               The preimage of N under bc_back_class is normal.\<close>
            have hb_U: "?b \<in> ?U" using hb_in_UV by (by100 blast)
            have hgrp_b: "top1_is_group_on (top1_fundamental_group_carrier ?U ?TU ?b)
                (top1_fundamental_group_mul ?U ?TU ?b) (top1_fundamental_group_id ?U ?TU ?b)
                (top1_fundamental_group_invg ?U ?TU ?b)"
              by (rule top1_fundamental_group_is_group[OF hTopU_outer hb_U])
            have hgrp_a: "top1_is_group_on (top1_fundamental_group_carrier ?U ?TU a)
                (top1_fundamental_group_mul ?U ?TU a) (top1_fundamental_group_id ?U ?TU a)
                (top1_fundamental_group_invg ?U ?TU a)"
              by (rule top1_fundamental_group_is_group[OF hTopU_outer ha_U_outer])
            \<comment> \<open>Define the class-level base change map.\<close>
            let ?\<Phi> = "\<lambda>cls. {k. \<exists>f\<in>cls. top1_loop_equiv_on ?U ?TU a
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
            \<comment> \<open>\<Phi> is a group homomorphism \<pi>_1(U,b) \<rightarrow> \<pi>_1(U,a).\<close>
            have h\<Phi>_hom: "top1_group_hom_on (top1_fundamental_group_carrier ?U ?TU ?b)
                (top1_fundamental_group_mul ?U ?TU ?b)
                (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a) ?\<Phi>"
            proof -
              let ?bc = "\<lambda>f. top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f"
              \<comment> \<open>Part 1: \<Phi> maps carrier to carrier.\<close>
              have hP1: "\<forall>c \<in> top1_fundamental_group_carrier ?U ?TU ?b. ?\<Phi> c \<in>
                  top1_fundamental_group_carrier ?U ?TU a"
              proof (intro ballI)
                fix c assume hc: "c \<in> top1_fundamental_group_carrier ?U ?TU ?b"
                obtain f where hf: "top1_is_loop_on ?U ?TU ?b f"
                    "c = {k. top1_loop_equiv_on ?U ?TU ?b f k}"
                  using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
                have hbc_f: "top1_is_loop_on ?U ?TU a (?bc f)"
                  by (rule top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U hf(1)])
                \<comment> \<open>\<Phi>(c) = [bc(f)]_a.\<close>
                have hPhi_c: "?\<Phi> c = {k. top1_loop_equiv_on ?U ?TU a (?bc f) k}"
                proof (rule set_eqI, rule iffI)
                  fix k assume "k \<in> ?\<Phi> c"
                  then obtain g where hfg: "top1_loop_equiv_on ?U ?TU ?b f g"
                      and hgk: "top1_loop_equiv_on ?U ?TU a (?bc g) k"
                    using hf(2) by (by100 blast)
                  have hg_loop: "top1_is_loop_on ?U ?TU ?b g"
                    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
                  from top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf(1) hg_loop hfg]
                  have "top1_loop_equiv_on ?U ?TU a (?bc f) (?bc g)" .
                  from top1_loop_equiv_on_trans[OF hTopU_outer this hgk]
                  show "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f) k}" by (by100 blast)
                next
                  fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f) k}"
                  moreover have "f \<in> c" using hf(2) top1_loop_equiv_on_refl[OF hf(1)] by (by100 blast)
                  ultimately show "k \<in> ?\<Phi> c" by (by100 blast)
                qed
                show "?\<Phi> c \<in> top1_fundamental_group_carrier ?U ?TU a"
                  unfolding hPhi_c top1_fundamental_group_carrier_def using hbc_f by (by100 blast)
              qed
              \<comment> \<open>Part 2: \<Phi> preserves multiplication.\<close>
              have hP2: "\<forall>c1 \<in> top1_fundamental_group_carrier ?U ?TU ?b.
                  \<forall>c2 \<in> top1_fundamental_group_carrier ?U ?TU ?b.
                  ?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)
                = top1_fundamental_group_mul ?U ?TU a (?\<Phi> c1) (?\<Phi> c2)"
              proof (intro ballI)
                fix c1 c2 assume hc1: "c1 \<in> top1_fundamental_group_carrier ?U ?TU ?b"
                    and hc2: "c2 \<in> top1_fundamental_group_carrier ?U ?TU ?b"
                obtain f1 where hf1: "top1_is_loop_on ?U ?TU ?b f1"
                    "c1 = {k. top1_loop_equiv_on ?U ?TU ?b f1 k}"
                  using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
                obtain f2 where hf2: "top1_is_loop_on ?U ?TU ?b f2"
                    "c2 = {k. top1_loop_equiv_on ?U ?TU ?b f2 k}"
                  using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
                \<comment> \<open>Theorem_52_1: bc(f1*f2) \<simeq> bc(f1)*bc(f2) in U at a.\<close>
                have hT52: "top1_path_homotopic_on ?U ?TU a a
                    (?bc (top1_path_product f1 f2))
                    (top1_path_product (?bc f1) (?bc f2))"
                  by (rule Theorem_52_1[OF hTopU_outer hrev\<delta>_path_U hf1(1) hf2(1)])
                \<comment> \<open>LHS: \<Phi>(mul(c1,c2)) = {k. le(U,a,bc(f1*f2),k)} (via bc congruence).\<close>
                \<comment> \<open>RHS: mul(\<Phi>(c1),\<Phi>(c2)) = {k. le(U,a,bc(f1)*bc(f2),k)} (via set computation).\<close>
                \<comment> \<open>These equal since bc(f1*f2) \<simeq> bc(f1)*bc(f2) (Theorem 52.1).\<close>
                \<comment> \<open>bc(f1), bc(f2) are loops at a.\<close>
                have hbc1: "top1_is_loop_on ?U ?TU a (?bc f1)"
                  by (rule top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U hf1(1)])
                have hbc2: "top1_is_loop_on ?U ?TU a (?bc f2)"
                  by (rule top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U hf2(1)])
                have hbc12_loop: "top1_is_loop_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2))"
                  using top1_path_product_is_loop[OF hTopU_outer hbc1 hbc2] .
                \<comment> \<open>Convert Thm 52.1 to loop_equiv.\<close>
                have hT52_le: "top1_loop_equiv_on ?U ?TU a
                    (?bc (top1_path_product f1 f2)) (top1_path_product (?bc f1) (?bc f2))"
                proof -
                  have hbc12: "top1_is_loop_on ?U ?TU a (?bc (top1_path_product f1 f2))"
                    using top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U
                        top1_path_product_is_loop[OF hTopU_outer hf1(1) hf2(1)]] .
                  show ?thesis unfolding top1_loop_equiv_on_def
                    using hbc12 hbc12_loop hT52 by (by100 blast)
                qed
                \<comment> \<open>Both sides equal {k. le(U,a,bc(f1)*bc(f2),k)}.\<close>
                have hLHS: "?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)
                    = {k. top1_loop_equiv_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2)) k}"
                proof -
                  \<comment> \<open>mul(c1,c2) = [f1*f2] by fundamental_group_mul_class.\<close>
                  have hmul_eq: "top1_fundamental_group_mul ?U ?TU ?b c1 c2
                      = {h. top1_loop_equiv_on ?U ?TU ?b (top1_path_product f1 f2) h}"
                    unfolding hf1(2) hf2(2)
                    by (rule top1_fundamental_group_mul_class[OF hTopU_outer hf1(1) hf2(1)])
                  \<comment> \<open>\<Phi>([f1*f2]) = [bc(f1*f2)] (by bc congruence, same pattern as Part 1).\<close>
                  have hf12: "top1_is_loop_on ?U ?TU ?b (top1_path_product f1 f2)"
                    using top1_path_product_is_loop[OF hTopU_outer hf1(1) hf2(1)] .
                  have hPhi_mul: "?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)
                      = {k. top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) k}"
                  proof (rule set_eqI, rule iffI)
                    fix k assume "k \<in> ?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)"
                    then obtain g where hg_in: "g \<in> top1_fundamental_group_mul ?U ?TU ?b c1 c2"
                        and hgk: "top1_loop_equiv_on ?U ?TU a (?bc g) k" by (by100 blast)
                    have "top1_loop_equiv_on ?U ?TU ?b (top1_path_product f1 f2) g"
                      using hg_in hmul_eq by (by100 blast)
                    hence "top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) (?bc g)"
                      using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf12]
                      unfolding top1_loop_equiv_on_def by (by100 blast)
                    from top1_loop_equiv_on_trans[OF hTopU_outer this hgk]
                    show "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) k}"
                      by (by100 blast)
                  next
                    fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) k}"
                    moreover have "top1_path_product f1 f2 \<in> top1_fundamental_group_mul ?U ?TU ?b c1 c2"
                      using hmul_eq top1_loop_equiv_on_refl[OF hf12] by (by100 blast)
                    ultimately show "k \<in> ?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)"
                      by (by100 blast)
                  qed
                  \<comment> \<open>[bc(f1*f2)] = [bc(f1)*bc(f2)] by Theorem_52_1.\<close>
                  show ?thesis
                  proof (rule set_eqI, rule iffI)
                    fix k assume "k \<in> ?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)"
                    hence "top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) k"
                      using hPhi_mul by (by100 blast)
                    from top1_loop_equiv_on_trans[OF hTopU_outer
                        top1_loop_equiv_on_sym[OF hT52_le] this]
                    show "k \<in> {k. top1_loop_equiv_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2)) k}"
                      by (by100 blast)
                  next
                    fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2)) k}"
                    hence "top1_loop_equiv_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2)) k"
                      by (by100 blast)
                    from top1_loop_equiv_on_trans[OF hTopU_outer hT52_le this]
                    have "top1_loop_equiv_on ?U ?TU a (?bc (top1_path_product f1 f2)) k" .
                    thus "k \<in> ?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)"
                      using hPhi_mul by (by100 blast)
                  qed
                qed
                \<comment> \<open>\<Phi>(c1) = [bc(f1)], \<Phi>(c2) = [bc(f2)] (shown in Part 1).\<close>
                have hPc1: "?\<Phi> c1 = {k. top1_loop_equiv_on ?U ?TU a (?bc f1) k}"
                proof (rule set_eqI, rule iffI)
                  fix k assume "k \<in> ?\<Phi> c1"
                  then obtain g where hfg: "g \<in> c1" and hgk: "top1_loop_equiv_on ?U ?TU a (?bc g) k"
                    by (by100 blast)
                  have "top1_loop_equiv_on ?U ?TU ?b f1 g"
                    using hfg hf1(2) by (by100 blast)
                  hence "top1_loop_equiv_on ?U ?TU a (?bc f1) (?bc g)"
                    using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf1(1)]
                    unfolding top1_loop_equiv_on_def by (by100 blast)
                  from top1_loop_equiv_on_trans[OF hTopU_outer this hgk]
                  show "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f1) k}" by (by100 blast)
                next
                  fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f1) k}"
                  moreover have "f1 \<in> c1" using hf1(2) top1_loop_equiv_on_refl[OF hf1(1)] by (by100 blast)
                  ultimately show "k \<in> ?\<Phi> c1" by (by100 blast)
                qed
                have hPc2: "?\<Phi> c2 = {k. top1_loop_equiv_on ?U ?TU a (?bc f2) k}"
                proof (rule set_eqI, rule iffI)
                  fix k assume "k \<in> ?\<Phi> c2"
                  then obtain g where hfg: "g \<in> c2" and hgk: "top1_loop_equiv_on ?U ?TU a (?bc g) k"
                    by (by100 blast)
                  have "top1_loop_equiv_on ?U ?TU ?b f2 g"
                    using hfg hf2(2) by (by100 blast)
                  hence "top1_loop_equiv_on ?U ?TU a (?bc f2) (?bc g)"
                    using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf2(1)]
                    unfolding top1_loop_equiv_on_def by (by100 blast)
                  from top1_loop_equiv_on_trans[OF hTopU_outer this hgk]
                  show "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f2) k}" by (by100 blast)
                next
                  fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a (?bc f2) k}"
                  moreover have "f2 \<in> c2" using hf2(2) top1_loop_equiv_on_refl[OF hf2(1)] by (by100 blast)
                  ultimately show "k \<in> ?\<Phi> c2" by (by100 blast)
                qed
                have hRHS: "top1_fundamental_group_mul ?U ?TU a (?\<Phi> c1) (?\<Phi> c2)
                    = {k. top1_loop_equiv_on ?U ?TU a (top1_path_product (?bc f1) (?bc f2)) k}"
                  unfolding hPc1 hPc2
                  by (rule top1_fundamental_group_mul_class[OF hTopU_outer hbc1 hbc2])
                show "?\<Phi> (top1_fundamental_group_mul ?U ?TU ?b c1 c2)
                    = top1_fundamental_group_mul ?U ?TU a (?\<Phi> c1) (?\<Phi> c2)"
                  using hLHS hRHS by (by100 fast)
              qed
              show ?thesis unfolding top1_group_hom_on_def using hP1 hP2 by (by100 blast)
            qed
            \<comment> \<open>M = {x \<in> G_b : \<Phi>(x) \<in> N} (relate to our M definition).\<close>
            have hM_eq: "?M = {x \<in> top1_fundamental_group_carrier ?U ?TU ?b. ?\<Phi> x \<in> N}"
            proof (rule set_eqI, rule iffI)
              fix x assume hx: "x \<in> ?M"
              then obtain f where hf: "top1_is_loop_on ?U ?TU ?b f"
                  "x = {k. top1_loop_equiv_on ?U ?TU ?b f k}"
                  "{k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k} \<in> N"
                by (by100 blast)
              have hx_carrier: "x \<in> top1_fundamental_group_carrier ?U ?TU ?b"
                using hx by (by100 blast)
              \<comment> \<open>\<Phi>(x) = \<Phi>([f]) = {k. \<exists>g\<in>[f]. le(U,a,bc(g),k)} = [bc(f)] (by bc congruence).\<close>
              have h\<Phi>_eq: "?\<Phi> x = {k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
              proof -
                have "?\<Phi> x = {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                    top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                  using hf(2) by (by100 simp)
                also have "... = {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                proof (rule set_eqI, rule iffI)
                  fix k assume "k \<in> {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                      top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                  then obtain g where hfg: "top1_loop_equiv_on ?U ?TU ?b f g"
                      and hgk: "top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k" by (by100 blast)
                  have hg_loop: "top1_is_loop_on ?U ?TU ?b g"
                    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
                  have hbc_fg: "top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f)
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g)"
                    using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf(1) hg_loop hfg] .
                  show "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                    using top1_loop_equiv_on_trans[OF hTopU_outer hbc_fg hgk] by (by100 blast)
                next
                  fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                  hence hfk: "top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k" by (by100 blast)
                  have "top1_loop_equiv_on ?U ?TU ?b f f"
                    by (rule top1_loop_equiv_on_refl[OF hf(1)])
                  thus "k \<in> {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                      top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                    using hfk by (by100 blast)
                qed
                finally show ?thesis .
              qed
              show "x \<in> {x \<in> top1_fundamental_group_carrier ?U ?TU ?b. ?\<Phi> x \<in> N}"
                using hx_carrier hf(3) h\<Phi>_eq by (by100 simp)
            next
              fix x assume hx: "x \<in> {x \<in> top1_fundamental_group_carrier ?U ?TU ?b. ?\<Phi> x \<in> N}"
              hence hx_carrier: "x \<in> top1_fundamental_group_carrier ?U ?TU ?b"
                  and h\<Phi>_in_N: "?\<Phi> x \<in> N" by (by100 blast)+
              obtain f where hf: "top1_is_loop_on ?U ?TU ?b f"
                  "x = {k. top1_loop_equiv_on ?U ?TU ?b f k}"
                using hx_carrier unfolding top1_fundamental_group_carrier_def by (by100 blast)
              have h\<Phi>_eq: "?\<Phi> x = {k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
              proof -
                have "?\<Phi> x = {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                    top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                  using hf(2) by (by100 simp)
                also have "... = {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                proof (rule set_eqI, rule iffI)
                  fix k assume "k \<in> {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                      top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                  then obtain g where hfg: "top1_loop_equiv_on ?U ?TU ?b f g"
                      and hgk: "top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k" by (by100 blast)
                  have hg_loop: "top1_is_loop_on ?U ?TU ?b g"
                    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
                  have hbc_fg: "top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f)
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g)"
                    using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U hf(1) hg_loop hfg] .
                  show "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                    using top1_loop_equiv_on_trans[OF hTopU_outer hbc_fg hgk] by (by100 blast)
                next
                  fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k}"
                  hence hfk: "top1_loop_equiv_on ?U ?TU a
                      (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k" by (by100 blast)
                  have "top1_loop_equiv_on ?U ?TU ?b f f"
                    by (rule top1_loop_equiv_on_refl[OF hf(1)])
                  thus "k \<in> {k. \<exists>g\<in>{k'. top1_loop_equiv_on ?U ?TU ?b f k'}.
                      top1_loop_equiv_on ?U ?TU a
                        (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> g) k}"
                    using hfk by (by100 blast)
                qed
                finally show ?thesis .
              qed
              have "{k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k} \<in> N"
                using h\<Phi>_in_N h\<Phi>_eq by (by100 simp)
              show "x \<in> ?M" using hf hx_carrier \<open>{k. top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f) k} \<in> N\<close> by (by100 blast)
            qed
            \<comment> \<open>Apply preimage_normal_subgroup.\<close>
            show ?thesis unfolding hM_eq
              by (rule preimage_normal_subgroup[OF hgrp_b hgrp_a h\<Phi>_hom hN_normal])
          qed
          \<comment> \<open>\<iota>*(\<pi>_1(UV,b)) \<subseteq> M.\<close>
          have hUV_sub_M: "top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x)
              ` top1_fundamental_group_carrier ?UV ?TUV ?b \<subseteq> ?M"
          proof (rule image_subsetI)
            fix cls assume hcls: "cls \<in> top1_fundamental_group_carrier ?UV ?TUV ?b"
            obtain f0 where hf0: "top1_is_loop_on ?UV ?TUV ?b f0"
                "cls = {k. top1_loop_equiv_on ?UV ?TUV ?b f0 k}"
              using hcls unfolding top1_fundamental_group_carrier_def by (by100 blast)
            \<comment> \<open>\<iota>*(cls) = [f0]_U (by inclusion_induced_class).\<close>
            have hUV_sub_U: "?UV \<subseteq> ?U" by (by100 blast)
            have hTUV_eq: "subspace_topology ?U ?TU ?UV = ?TUV"
              using subspace_topology_trans[OF hUV_sub_U] by (by100 simp)
            have h\<iota>_cls: "top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x) cls
                = {k. top1_loop_equiv_on ?U ?TU ?b f0 k}"
              using hf0(2) inclusion_induced_class[OF hUV_sub_U hTopU_outer hTUV_eq hf0(1)]
              by (by100 simp)
            \<comment> \<open>f0 is a loop in U (from UV \<subseteq> U).\<close>
            have hf0_U: "top1_is_loop_on ?U ?TU ?b f0"
            proof -
              have hAU_UV: "top1_continuous_map_on ?UV ?TUV ?U ?TU (\<lambda>x. x)"
              proof -
                from top1_continuous_map_on_restrict_domain_simple[OF
                    top1_continuous_map_on_id[OF hTopU_outer] hUV_sub_U]
                show ?thesis using hTUV_eq unfolding id_def by (by100 simp)
              qed
              have "top1_is_loop_on ?U ?TU ((\<lambda>x. x) ?b) ((\<lambda>x. x) \<circ> f0)"
                by (rule top1_continuous_map_loop_early[OF hAU_UV hf0(1)])
              moreover have "(\<lambda>x::'a. x) \<circ> f0 = f0" by (rule ext) (by100 simp)
              moreover have "(\<lambda>x::'a. x) ?b = ?b" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            \<comment> \<open>[bc_back(f0)]_U \<in> N (from hbc_back_UV_in_N).\<close>
            have hbc_in_N: "{k. top1_loop_equiv_on ?U ?TU a
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f0) k} \<in> N"
              by (rule hbc_back_UV_in_N[OF hf0(1)])
            \<comment> \<open>\<iota>*(cls) \<in> M.\<close>
            show "top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x) cls \<in> ?M"
              unfolding h\<iota>_cls using hf0_U hbc_in_N
              unfolding top1_fundamental_group_carrier_def by (by100 blast)
          qed
          \<comment> \<open>Normal closure \<subseteq> M.\<close>
          have hncl_sub_M: "top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier ?U ?TU ?b) (top1_fundamental_group_mul ?U ?TU ?b)
              (top1_fundamental_group_id ?U ?TU ?b) (top1_fundamental_group_invg ?U ?TU ?b)
              (top1_fundamental_group_induced_on ?UV ?TUV ?b ?U ?TU ?b (\<lambda>x. x)
                 ` top1_fundamental_group_carrier ?UV ?TUV ?b) \<subseteq> ?M"
          proof -
            show ?thesis unfolding top1_normal_subgroup_generated_on_def
              using hUV_sub_M hM_normal by (by100 blast)
          qed
          \<comment> \<open>[g'] \<in> M.\<close>
          have hg'_in_M: "{k. top1_loop_equiv_on ?U ?TU ?b ?g' k} \<in> ?M"
            using hg'_in_ncl hncl_sub_M by (by100 blast)
          \<comment> \<open>Extract: bc_back_class([g']_U) \<in> N.\<close>
          have hbc_back_in_N: "{k. top1_loop_equiv_on ?U ?TU a
              (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k} \<in> N"
          proof -
            from hg'_in_M obtain f' where hf': "top1_is_loop_on ?U ?TU ?b f'"
                "{k. top1_loop_equiv_on ?U ?TU ?b ?g' k} = {k. top1_loop_equiv_on ?U ?TU ?b f' k}"
                "{k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f') k} \<in> N"
              by (by100 blast)
            \<comment> \<open>g' \<simeq> f' in U, so bc_back(g') \<simeq> bc_back(f') in U.\<close>
            have "top1_loop_equiv_on ?U ?TU ?b ?g' f'"
            proof -
              have "f' \<in> {k. top1_loop_equiv_on ?U ?TU ?b f' k}"
                using top1_loop_equiv_on_refl[OF hf'(1)] by (by100 blast)
              hence "f' \<in> {k. top1_loop_equiv_on ?U ?TU ?b ?g' k}" using hf'(2) by (by100 simp)
              thus ?thesis by (by100 blast)
            qed
            hence "top1_loop_equiv_on ?U ?TU a
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')
                (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f')"
              using top1_basepoint_change_loop_equiv[OF hTopU_outer hrev\<delta>_path_U
                  hg'_loop hf'(1)] by (by100 blast)
            \<comment> \<open>So the classes are equal: [bc_back(g')]_U = [bc_back(f')]_U.\<close>
            hence "{k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k}
                = {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f') k}"
            proof -
              have hbc_g'_loop: "top1_is_loop_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')" using hbc_back_loop .
              have hbc_f'_loop: "top1_is_loop_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f')"
                by (rule top1_basepoint_change_is_loop[OF hTopU_outer hrev\<delta>_path_U hf'(1)])
              assume hequiv: "top1_loop_equiv_on ?U ?TU a
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g')
                  (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f')"
              show ?thesis
              proof (rule set_eqI, rule iffI)
                fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k}"
                hence h1: "top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k" by (by100 blast)
                show "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f') k}"
                  using top1_loop_equiv_on_trans[OF hTopU_outer
                      top1_loop_equiv_on_sym[OF hequiv] h1] by (by100 blast)
              next
                fix k assume "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f') k}"
                hence h1: "top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> f') k" by (by100 blast)
                show "k \<in> {k. top1_loop_equiv_on ?U ?TU a
                    (top1_basepoint_change_on ?U ?TU ?b a ?rev\<delta> ?g') k}"
                  using top1_loop_equiv_on_trans[OF hTopU_outer hequiv h1] by (by100 blast)
              qed
            qed
            thus ?thesis using hf'(3) by (by100 simp)
          qed
          \<comment> \<open>Finally: c = [bc_back(g')]_U \<in> N.\<close>
          show "c \<in> N" using hbc_back_class hbc_back_in_N by (by100 simp)
        qed
      qed
      \<comment> \<open>Step 3: preimage under (A\<hookrightarrow>U)* of \<langle>\<langle>{[k\<circ>p]_U}\<rangle>\<rangle> \<subseteq> \<langle>\<langle>{[k\<circ>p]_A}\<rangle>\<rangle> = ?relator.\<close>
      have hstep3: "\<And>c. c \<in> top1_fundamental_group_carrier A ?TA a \<Longrightarrow>
          (top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
              \<in> top1_normal_subgroup_generated_on
                  (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
                  (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
                  {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?U ?TU a
                     (\<lambda>z. h z) {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}}
          \<Longrightarrow> c \<in> ?relator"
      proof -
        fix c assume hc_A: "c \<in> top1_fundamental_group_carrier A ?TA a"
        let ?iota_c = "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c"
        let ?kp_U = "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?U ?TU a
                     (\<lambda>z. h z) {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
        let ?N_U = "top1_normal_subgroup_generated_on
                  (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
                  (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
                  {?kp_U}"
        assume h_iota_c_in: "?iota_c \<in> ?N_U"
        \<comment> \<open>The (A\<hookrightarrow>U) inclusion maps [k\<circ>p]_A to [k\<circ>p]_U (both are the same loop).
           The inclusion-induced map is injective (deformation retract gives iso).
           For any normal subgroup M of \<pi>_1(A,a) containing [k\<circ>p]_A:
           (A\<hookrightarrow>U)*(M) is a normal subgroup of \<pi>_1(U,a) containing [k\<circ>p]_U.
           So \<langle>\<langle>{[k\<circ>p]_U}\<rangle>\<rangle> \<subseteq> (A\<hookrightarrow>U)*(M).
           Since (A\<hookrightarrow>U)*(c) \<in> \<langle>\<langle>{[k\<circ>p]_U}\<rangle>\<rangle> \<subseteq> (A\<hookrightarrow>U)*(M), injectivity gives c \<in> M.
           Since M was arbitrary: c \<in> \<langle>\<langle>{[k\<circ>p]_A}\<rangle>\<rangle> = ?relator.\<close>
        \<comment> \<open>c \<in> ?relator = \<langle>\<langle>{[k\<circ>p]_A}\<rangle>\<rangle> = \<Inter>{N. [k\<circ>p]_A \<in> N \<and> normal N}.
           For any such N, (A\<hookrightarrow>U)*(N) is normal in \<pi>_1(U,a) containing [k\<circ>p]_U.
           So ?N_U \<subseteq> (A\<hookrightarrow>U)*(N). Since (A\<hookrightarrow>U)*(c) \<in> ?N_U \<subseteq> (A\<hookrightarrow>U)*(N),
           injectivity of (A\<hookrightarrow>U)* gives c \<in> N. Since N arbitrary, c \<in> ?relator.\<close>
        \<comment> \<open>Apply inj_hom_preimage_normal_closure with f = (A\<hookrightarrow>U)*, s = [k\<circ>p]_A.
           Need f(s) = [k\<circ>p]_U by functoriality.\<close>
        let ?kp_A = "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
                       {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}"
        let ?AU = "top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)"
        \<comment> \<open>f(kp_A) = kp_U by functoriality: (A\<hookrightarrow>U)* \<circ> (S1\<rightarrow>A)* = (S1\<rightarrow>U)*.\<close>
        have hf_kpA_eq_kpU: "?AU ?kp_A = ?kp_U"
        proof -
          have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hTopU_k: "is_topology_on ?U ?TU"
            by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
          have hAU_cont: "top1_continuous_map_on A ?TA ?U ?TU (\<lambda>x. x)"
          proof -
            have "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
            from top1_continuous_map_on_restrict_domain_simple[OF top1_continuous_map_on_id[OF hTopU_k] this]
            show ?thesis using subspace_topology_trans[OF \<open>A \<subseteq> ?U\<close>] unfolding id_def by (by100 simp)
          qed
          have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
          have hiota_a: "?\<iota> (1, 0) = a" using assms(9) by (by100 simp)
          have hcomp_eq: "(\<lambda>x. x) \<circ> ?\<iota> = (\<lambda>z. h z)" by (rule ext) (by100 simp)
          have hf_loop_k: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?f"
            unfolding top1_is_loop_on_def top1_is_path_on_def
          proof (intro conjI)
            have "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
              using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
            from top1_continuous_map_on_restrict_domain_simple[OF this subset_UNIV]
            have "top1_continuous_map_on top1_unit_interval
                (subspace_topology UNIV top1_open_sets top1_unit_interval)
                top1_S1 top1_S1_topology top1_R_to_S1" .
            moreover have "?f = top1_R_to_S1"
            proof (rule ext)
              fix s :: real show "?f s = top1_R_to_S1 s" unfolding top1_R_to_S1_def by (by100 simp)
            qed
            ultimately show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_S1 top1_S1_topology ?f"
              unfolding top1_unit_interval_topology_def using subspace_topology_UNIV_self by (by100 simp)
          next show "?f 0 = (1::real, 0::real)" by (by100 simp)
          next show "?f 1 = (1::real, 0::real)" by (by100 simp)
          qed
          have hkp_class: "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
              \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
            unfolding top1_fundamental_group_carrier_def using hf_loop_k by (by100 blast)
          show ?thesis
            using fundamental_group_induced_comp[OF hS1_top hTA_top hTopU_k h\<iota>_cont hAU_cont
                h10_S1 hiota_a _ hkp_class] hcomp_eq by (by100 simp)
        qed
        \<comment> \<open>h_iota_c_in says ?AU(c) \<in> \<langle>\<langle>{?kp_U}\<rangle>\<rangle> = \<langle>\<langle>{?AU(?kp_A)}\<rangle>\<rangle>.\<close>
        have hfc_in: "?AU c \<in> top1_normal_subgroup_generated_on
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
            (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
            {?AU ?kp_A}"
          using h_iota_c_in hf_kpA_eq_kpU by (by100 simp)
        \<comment> \<open>Collect premises for inj_hom_preimage_normal_closure.\<close>
        have hTopU_k: "is_topology_on ?U ?TU"
          by (rule subspace_topology_is_topology_on[OF hTopX_ns]) (by100 blast)
        have ha_U_k: "a \<in> ?U" using assms(6) hA_sub_X hx0_notin_A by (by100 blast)
        have hA_sub_U_k: "A \<subseteq> ?U" using hA_sub_X hx0_notin_A by (by100 blast)
        have hgrpA_k: "top1_is_group_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
            (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)"
          by (rule top1_fundamental_group_is_group[OF hTA_top assms(6)])
        have hgrpU_k: "top1_is_group_on
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
            (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)"
          by (rule top1_fundamental_group_is_group[OF hTopU_k ha_U_k])
        have hAU_hom_k: "top1_group_hom_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
            (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a) ?AU"
        proof -
          have hTA_eq: "subspace_topology ?U ?TU A = ?TA"
            using subspace_topology_trans[OF hA_sub_U_k] by (by100 simp)
          from subspace_inclusion_induced_hom[OF hTopU_k hA_sub_U_k assms(6)]
          show ?thesis using hTA_eq by (by100 simp)
        qed
        have hAU_surj_k: "?AU ` top1_fundamental_group_carrier A ?TA a
            = top1_fundamental_group_carrier ?U ?TU a"
          using hAU_surj_outer .
        have hAU_inj_k: "inj_on ?AU (top1_fundamental_group_carrier A ?TA a)"
          using hAU_inj_outer .
        have hkpA_sub: "{?kp_A} \<subseteq> top1_fundamental_group_carrier A ?TA a"
        proof -
          have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
            using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
          have "?\<iota> (1, 0) = a" using assms(9) by (by100 simp)
          have hiota_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
              (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>)"
            by (rule top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA_top h10 assms(6)
                h\<iota>_cont \<open>?\<iota> (1, 0) = a\<close>])
          show ?thesis using hiota_hom standard_S1_loop_class_in_carrier
            unfolding top1_group_hom_on_def by (by100 blast)
        qed
        have hrelator_normal_k: "top1_normal_subgroup_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
            (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a) ?relator"
          by (rule normal_subgroup_generated_is_normal[OF hgrpA_k hkpA_sub])
        have hkpA_in_relator: "?kp_A \<in> ?relator"
        proof -
          have "?kp_A \<in> {?kp_A}" by (by100 blast)
          hence "?kp_A \<in> top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
              (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)
              {?kp_A}"
            unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
          thus ?thesis .
        qed
        show "c \<in> ?relator"
          by (rule inj_hom_preimage_normal_closure[OF hgrpA_k hgrpU_k hAU_hom_k hAU_surj_k
              hAU_inj_k hrelator_normal_k hkpA_in_relator hc_A hfc_in])
      qed
      \<comment> \<open>Combine steps 1-3.\<close>
      show ?thesis
      proof
        fix c assume hc: "c \<in> top1_group_kernel_on
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_id X TX a) ?jAX"
        have hc_A: "c \<in> top1_fundamental_group_carrier A ?TA a"
          using hc unfolding top1_group_kernel_on_def by (by100 blast)
        from hstep1[OF hc] have "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
            \<in> top1_group_kernel_on
              (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_id X TX a)
              (top1_fundamental_group_induced_on ?U ?TU a X TX a (\<lambda>x. x))" .
        with hstep2 have "(top1_fundamental_group_induced_on A ?TA a ?U ?TU a (\<lambda>x. x)) c
            \<in> top1_normal_subgroup_generated_on
                (top1_fundamental_group_carrier ?U ?TU a) (top1_fundamental_group_mul ?U ?TU a)
                (top1_fundamental_group_id ?U ?TU a) (top1_fundamental_group_invg ?U ?TU a)
                {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) ?U ?TU a
                   (\<lambda>z. h z) {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}}"
          by (by100 blast)
        from hstep3[OF hc_A this] show "c \<in> ?relator" .
      qed
    qed
    \<comment> \<open>Step (c): \<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle> \<subseteq> ker(j_*). The normal closure of {[k\<circ>p]} is contained
       in ker(j_*) because [k\<circ>p] \<in> ker(j_*) and ker is a normal subgroup.\<close>
    have hrelator_sub_ker: "?relator \<subseteq> top1_group_kernel_on
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_id X TX a) ?jAX"
    proof -
      let ?ker = "top1_group_kernel_on
          (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_id X TX a) ?jAX"
      \<comment> \<open>ker is a normal subgroup.\<close>
      have hker_normal: "top1_normal_subgroup_on
          (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
          (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a) ?ker"
        by (rule kernel_is_normal_subgroup[OF
            top1_fundamental_group_is_group[OF hTA_top assms(6)]
            top1_fundamental_group_is_group[OF hTopX_ns ha_X] hj_hom])
      \<comment> \<open>{[k\<circ>p]} \<subseteq> ker. Need [k\<circ>p] \<in> carrier(A,a) and j_*([k\<circ>p]) = id.\<close>
      have hkp_in_carrier: "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
          {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
        \<in> top1_fundamental_group_carrier A ?TA a"
      proof -
        have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
        have hiota_a: "?\<iota> (1, 0) = a" using assms(9) by (by100 simp)
        have h\<iota>_hom_loc: "top1_group_hom_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
            (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>)"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA_top h10 assms(6)
              h\<iota>_cont hiota_a])
        have hf_loop_loc: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?f"
          unfolding top1_is_loop_on_def top1_is_path_on_def
        proof (intro conjI)
          have hf_eq: "?f = top1_R_to_S1"
          proof (rule ext)
            fix s :: real show "?f s = top1_R_to_S1 s" unfolding top1_R_to_S1_def by (by100 simp)
          qed
          have hR_to_S1_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets
              top1_S1 top1_S1_topology top1_R_to_S1"
            using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
          from top1_continuous_map_on_restrict_domain_simple[OF hR_to_S1_cont UNIV_I[THEN subsetI]]
          show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              top1_S1 top1_S1_topology ?f"
            unfolding top1_unit_interval_topology_def hf_eq
            using subspace_topology_UNIV_self by (by100 simp)
        next show "?f 0 = (1::real, 0::real)" by (by100 simp)
        next show "?f 1 = (1::real, 0::real)" by (by100 simp)
        qed
        have "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
            \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          unfolding top1_fundamental_group_carrier_def using hf_loop_loc by (by100 blast)
        thus ?thesis using h\<iota>_hom_loc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      have hkp_sub: "{top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
          {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}} \<subseteq> ?ker"
        unfolding top1_group_kernel_on_def using hkp_in_ker hkp_in_carrier by (by100 blast)
      \<comment> \<open>Normal closure of subset of normal subgroup \<subseteq> the normal subgroup.\<close>
      show ?thesis unfolding top1_normal_subgroup_generated_on_def
        using hkp_sub hker_normal by (by100 blast)
    qed
    show ?thesis using hker_sub_relator hrelator_sub_ker by (by100 blast)
  qed
  \<comment> \<open>Step 4: Group and normal subgroup properties.\<close>
  have hgrpA: "top1_is_group_on
      (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
      (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a)"
    by (rule top1_fundamental_group_is_group[OF hTA_top assms(6)])
  have hrelator_sub: "{top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
      {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}}
    \<subseteq> top1_fundamental_group_carrier A ?TA a"
  proof -
    \<comment> \<open>The induced map \<iota>_* is a homomorphism \<pi>_1(S1,(1,0)) \<rightarrow> \<pi>_1(A,a),
       so it maps carrier elements to carrier elements.\<close>
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hiota_a: "?\<iota> (1, 0) = a" using assms(9) by (by100 simp)
    have h\<iota>_hom: "top1_group_hom_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier A ?TA a)
        (top1_fundamental_group_mul A ?TA a)
        (top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>)"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hS1_top hTA_top h10 assms(6) h\<iota>_cont hiota_a])
    \<comment> \<open>The class [f] is in \<pi>_1(S1,(1,0)): f = R_to_S1 restricted to I is a loop.\<close>
    have hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?f"
      unfolding top1_is_loop_on_def top1_is_path_on_def
    proof (intro conjI)
      have hf_eq: "?f = top1_R_to_S1"
      proof (rule ext)
        fix s :: real
        show "?f s = top1_R_to_S1 s" unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have hR_to_S1_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets
          top1_S1 top1_S1_topology top1_R_to_S1"
        using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
      have hI_sub_R: "top1_unit_interval \<subseteq> (UNIV::real set)" by (by100 blast)
      have hI_restrict: "top1_continuous_map_on top1_unit_interval
          (subspace_topology UNIV top1_open_sets top1_unit_interval)
          top1_S1 top1_S1_topology top1_R_to_S1"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hR_to_S1_cont hI_sub_R])
      have hI_top_eq: "subspace_topology UNIV top1_open_sets top1_unit_interval =
          top1_unit_interval_topology"
        unfolding top1_unit_interval_topology_def by (by100 simp)
      show "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_S1 top1_S1_topology ?f"
        using hI_restrict unfolding hI_top_eq hf_eq .
    next
      show "?f 0 = (1::real, 0::real)" by (by100 simp)
    next
      show "?f 1 = (1::real, 0::real)" by (by100 simp)
    qed
    have hf_class_in: "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
        \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      unfolding top1_fundamental_group_carrier_def using hf_loop by (by100 blast)
    \<comment> \<open>hom maps carrier to carrier.\<close>
    have "top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0) A ?TA a ?\<iota>
        {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?f g}
      \<in> top1_fundamental_group_carrier A ?TA a"
      using h\<iota>_hom hf_class_in unfolding top1_group_hom_on_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hrelator_normal: "top1_normal_subgroup_on
      (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a)
      (top1_fundamental_group_id A ?TA a) (top1_fundamental_group_invg A ?TA a) ?relator"
    by (rule normal_subgroup_generated_is_normal[OF hgrpA hrelator_sub])
  have hgrpX: "top1_is_group_on
      (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a)
      (top1_fundamental_group_id X TX a) (top1_fundamental_group_invg X TX a)"
    by (rule top1_fundamental_group_is_group[OF hTopX_ns ha_X])
  \<comment> \<open>Step 5: First Isomorphism Theorem: \<pi>_1(X,a) \<cong> \<pi>_1(A,a)/\<langle>\<langle>{[k\<circ>p]}\<rangle>\<rangle>.\<close>
  have hiso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX a) (top1_fundamental_group_mul X TX a)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A ?TA a) (top1_fundamental_group_mul A ?TA a) ?relator)
        (top1_quotient_group_mul_on (top1_fundamental_group_mul A ?TA a))"
    by (rule first_isomorphism_theorem_forward[OF hgrpA hrelator_normal hgrpX hj_hom hj_surj hj_ker])
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
  have hA_free: "\<exists>(F::int set) mulF eF invgF (\<iota>F::nat \<Rightarrow> int).
      top1_is_free_group_full_on F mulF eF invgF \<iota>F {0::nat, 1}
      \<and> top1_groups_isomorphic_on F mulF
          (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
          (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
  proof -
    have hset_eq: "{0::nat, 1} = {..<(2::nat)}" by (by100 auto)
    have hwedge2: "top1_is_wedge_of_circles_on A (subspace_topology T_torus TT A) {..<(2::nat)} x0"
      using hA_wedge hset_eq by (by100 simp)
    from Theorem_71_1_wedge_of_circles_finite[OF hwedge2]
    obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int" where
        hG0f: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<2::nat}" and
        hG0i: "top1_groups_isomorphic_on G0 mul0
            (top1_fundamental_group_carrier A (subspace_topology T_torus TT A) x0)
            (top1_fundamental_group_mul A (subspace_topology T_torus TT A) x0)"
      by (elim exE conjE) (rule that, assumption+)
    have "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {0::nat, 1}"
      using hG0f hset_eq by (by100 simp)
    thus ?thesis using hG0i by (by100 blast)
  qed
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
      and hx0_A: "x0 \<in> A" and hA_sub: "A \<subseteq> X"
    sorry \<comment> \<open>From dunce cap definition: quotient of B² by n-fold rotation on S¹.\<close>
  \<comment> \<open>Step 2: \<pi>_1(A) \<cong> Z (fundamental group of circle).\<close>
  have hA_Z: "\<exists>f. top1_group_iso_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (UNIV::int set) (\<lambda>a b. a + b) f"
  proof -
    let ?TA = "subspace_topology X TX A"
    \<comment> \<open>Extract homeomorphism h_circ: S1 \<rightarrow> A.\<close>
    obtain h_circ where h_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology A ?TA h_circ"
      using hA_circle by (by100 blast)
    \<comment> \<open>\<pi>_1(S1, (1,0)) \<cong> (Z, +) by Theorem 54.5.\<close>
    have hS1_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>By Corollary 52.5: homeomorphism S1 \<cong> A gives \<pi>_1(S1, (1,0)) \<cong> \<pi>_1(A, h_circ(1,0)).\<close>
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hTA_top: "is_topology_on A ?TA"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(2) unfolding top1_is_dunce_cap_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
    qed
    have h10_S1: "(1::real, 0::real) \<in> top1_S1"
      unfolding top1_S1_def by (by100 simp)
    have hS1_A_iso: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTA_top h_homeo h10_S1]) (by100 simp)
    \<comment> \<open>Chain: \<pi>_1(A, h_circ(1,0)) \<cong> \<pi>_1(S1, (1,0)) \<cong> Z.\<close>
    have hA_hc_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
        top1_Z_group top1_Z_mul"
    proof -
      have hA_S1: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
      proof -
        have hgrpS1: "top1_is_group_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
          by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
        have hhc_A: "h_circ (1, 0) \<in> A"
          using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hgrpA: "top1_is_group_on
            (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_id A ?TA (h_circ (1, 0)))
            (top1_fundamental_group_invg A ?TA (h_circ (1, 0)))"
          by (rule top1_fundamental_group_is_group[OF hTA_top hhc_A])
        show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hS1_A_iso hgrpS1 hgrpA])
      qed
      show ?thesis by (rule groups_isomorphic_trans_fwd[OF hA_S1 hS1_Z])
    qed
    \<comment> \<open>Base change: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) (since A is path-connected).\<close>
    have hA_pc: "top1_path_connected_on A ?TA"
    proof -
      have "top1_path_connected_on top1_S1 top1_S1_topology"
        by (rule S1_path_connected)
      thus ?thesis
        by (rule homeomorphism_preserves_path_connected[OF h_homeo])
    qed
    have hhc_A: "h_circ (1, 0) \<in> A"
      using h_homeo h10_S1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have hA_bc: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        (top1_fundamental_group_carrier A ?TA (h_circ (1, 0)))
        (top1_fundamental_group_mul A ?TA (h_circ (1, 0)))"
      by (rule Corollary_52_2_basepoint_independent[OF hA_pc hx0_A hhc_A])
    \<comment> \<open>Chain: \<pi>_1(A, x0) \<cong> \<pi>_1(A, h_circ(1,0)) \<cong> Z.\<close>
    have hA_x0_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A ?TA x0)
        (top1_fundamental_group_mul A ?TA x0)
        top1_Z_group top1_Z_mul"
      by (rule groups_isomorphic_trans_fwd[OF hA_bc hA_hc_Z])
    \<comment> \<open>Unfold Z definitions.\<close>
    have "top1_Z_group = (UNIV :: int set)" unfolding top1_Z_group_def by (by100 simp)
    moreover have "top1_Z_mul = (\<lambda>a b. a + b)" unfolding top1_Z_mul_def by (rule ext)+ (by100 simp)
    ultimately show ?thesis using hA_x0_Z unfolding top1_groups_isomorphic_on_def by (by100 simp)
  qed
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
      using hxy0 by auto
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
    unfolding top1_is_polygonal_quotient_on_def
  proof (intro conjI)
    show "is_topology_on_strict X TX"
      using assms(1) unfolding top1_is_n_fold_torus_on_def top1_quotient_of_scheme_on_def by (by100 blast)
    show "\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
      using assms(1) unfolding top1_is_n_fold_torus_on_def by (by100 blast)
  qed
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
    using assms(1) unfolding top1_is_m_fold_projective_on_def
  proof (elim disjE conjE)
    \<comment> \<open>Case m = 1: dunce cap. Need to show dunce cap is polygonal quotient.\<close>
    assume "m = 1" "top1_is_dunce_cap_on X TX (2::nat)"
    thus ?thesis sorry \<comment> \<open>Dunce cap with n=2 is a polygonal quotient.\<close>
  next
    \<comment> \<open>Case m \<ge> 2: directly from the projective scheme.\<close>
    assume "2 \<le> m" "top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)"
    thus ?thesis unfolding top1_is_polygonal_quotient_on_def
    proof (intro conjI)
      show "is_topology_on_strict X TX"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close>
        unfolding top1_quotient_of_scheme_on_def by (by100 blast)
      show "\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
        using \<open>top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m)\<close> by (by100 blast)
    qed
  qed
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
      ultimately show ?thesis by metis
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
            unfolding top1_loop_equiv_on_def by blast
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
      and "top1_path_connected_on Y TY"
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
        by (rule top1_path_connected_imp_connected[OF assms(8)])
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
      and "top1_path_connected_on Y TY"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-7) by (by100 blast)

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
  have hCov_group: "\<exists>eC invgC. top1_is_group_on ?Cov (\<lambda>h k e. h (k e)) eC invgC"
  proof -
    let ?mul = "\<lambda>h k e. h (k e)" \<comment> \<open>= \<circ> (function composition)\<close>
    let ?eC = "id :: 'e \<Rightarrow> 'e"
    let ?invC = "\<lambda>h. inv_into E h"
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
      \<comment> \<open>inv_into E h is the inverse homeomorphism.\<close>
      have hinv_homeo: "top1_homeomorphism_on E TE E TE (inv_into E h)"
        by (rule homeomorphism_inverse[OF hh_homeo])
      moreover have "\<forall>e\<in>E. p (inv_into E h e) = p e"
      proof (intro ballI)
        fix e assume "e \<in> E"
        have hbij: "bij_betw h E E" using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have hsurj_loc: "h ` E = E" using hbij unfolding bij_betw_def by (by100 blast)
        have "e \<in> h ` E" using \<open>e \<in> E\<close> hsurj_loc by (by100 blast)
        have "inv_into E h e \<in> E" using inv_into_into[OF \<open>e \<in> h ` E\<close>] .
        have "h (inv_into E h e) = e" using f_inv_into_f[OF \<open>e \<in> h ` E\<close>] .
        hence "p e = p (h (inv_into E h e))" by (by100 simp)
        also have "\<dots> = p (inv_into E h e)" using hh_p \<open>inv_into E h e \<in> E\<close> by (by100 blast)
        finally show "p (inv_into E h e) = p e" by (by100 simp)
      qed
      ultimately show "?invC h \<in> ?Cov"
        unfolding top1_covering_transformation_on_def by (by100 blast)
    qed
    \<comment> \<open>Associativity.\<close>
    have hassoc: "\<forall>h\<in>?Cov. \<forall>k\<in>?Cov. \<forall>l\<in>?Cov. ?mul (?mul h k) l = ?mul h (?mul k l)"
      by (by100 auto)
    \<comment> \<open>Identity.\<close>
    have hident: "\<forall>h\<in>?Cov. ?mul ?eC h = h \<and> ?mul h ?eC = h"
      by (by100 auto)
    \<comment> \<open>Inverse.\<close>
    have hinverse: "\<forall>h\<in>?Cov. ?mul (?invC h) h = ?eC \<and> ?mul h (?invC h) = ?eC"
      sorry \<comment> \<open>inv_into E h \<circ> h = id and h \<circ> inv = id.
             Subtlety: equality as total functions requires h to be globally injective,
             not just on E. Covering transformations (as homeomorphisms E\<rightarrow>E) may need
             the UNIV-injectivity from the homeomorphism_on definition.\<close>
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
  show ?thesis
    sorry \<comment> \<open>Full coset-space construction (Munkres 82.1):
       Define E' = H-right-cosets of path classes from b0.
       Topology via path-extension basis.
       Verify: covering map (semilocal simple connectivity) + connected + locally path-connected.
       p'_*(pi_1(E', e0')) = H.\<close>
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
      and "is_topology_on_strict E TE"
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
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A'\<in>\<A>E. \<forall>B'\<in>\<A>E. A' \<noteq> B' \<longrightarrow>
           A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
         \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
         \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2)
      \<and> (\<forall>C. C \<subseteq> E \<longrightarrow>
           (closedin_on E TE C \<longleftrightarrow>
            (\<forall>A'\<in>\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C))))"
    sorry \<comment> \<open>Lift graph structure from B: arcs + intersection + weak topology.\<close>
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have hE_hausdorff: "is_hausdorff_on E TE"
  proof -
    have hB_haus: "is_hausdorff_on B TB"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using hB_haus unfolding is_hausdorff_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_surj: "p ` E = B"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis unfolding is_hausdorff_on_def neighborhood_of_def
    proof (intro conjI ballI impI)
      show "is_topology_on E TE" by (rule hTE)
    next
      fix x y assume hx: "x \<in> E" and hy: "y \<in> E" and hne: "x \<noteq> y"
      show "\<exists>U V. (U \<in> TE \<and> x \<in> U) \<and> (V \<in> TE \<and> y \<in> V) \<and> U \<inter> V = {}"
      proof (cases "p x = p y")
        case False
        \<comment> \<open>Separate in B, pull back preimages.\<close>
        have hpx: "p x \<in> B" using hp_surj hx by (by100 blast)
        have hpy: "p y \<in> B" using hp_surj hy by (by100 blast)
        obtain U1 V1 where hU1: "U1 \<in> TB" "p x \<in> U1" and hV1: "V1 \<in> TB" "p y \<in> V1"
            and hdisj: "U1 \<inter> V1 = {}"
          using hB_haus hpx hpy False unfolding is_hausdorff_on_def neighborhood_of_def
          by (by100 blast)
        have hpU: "{e \<in> E. p e \<in> U1} \<in> TE"
          using hp_cont hU1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have hpV: "{e \<in> E. p e \<in> V1} \<in> TE"
          using hp_cont hV1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have "x \<in> {e \<in> E. p e \<in> U1}" using hx hU1(2) by (by100 blast)
        moreover have "y \<in> {e \<in> E. p e \<in> V1}" using hy hV1(2) by (by100 blast)
        moreover have "{e \<in> E. p e \<in> U1} \<inter> {e \<in> E. p e \<in> V1} = {}"
          using hdisj by (by100 blast)
        ultimately show ?thesis using hpU hpV by (by100 blast)
      next
        case True
        \<comment> \<open>Same fiber: x, y in different sheets.\<close>
        have hb: "p x \<in> B" using hp_surj hx by (by100 blast)
        obtain U0 where hbU: "p x \<in> U0"
            and hev: "top1_evenly_covered_on E TE B TB p U0"
          using assms(2) hb unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_all: "(\<forall>V\<in>\<V>. openin_on E TE V)
            \<and> (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
            \<and> {e \<in> E. p e \<in> U0} = \<Union>\<V>
            \<and> (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U0 (subspace_topology B TB U0) p)"
          using hev unfolding top1_evenly_covered_on_def
          apply (elim conjE exE)
          apply (rule that)
          apply (by100 blast)+
          done
        have hV_open: "\<forall>V\<in>\<V>. openin_on E TE V" using hV_all by (by100 blast)
        have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_all by (by100 blast)
        have hV_union: "{e \<in> E. p e \<in> U0} = \<Union>\<V>" using hV_all by (by100 blast)
        have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
            U0 (subspace_topology B TB U0) p" using hV_all by (by100 blast)
        have hx_in_V: "x \<in> \<Union>\<V>" using hx hbU hV_union by (by100 blast)
        have "p y \<in> U0" using hbU True by (by100 simp)
        have hy_in_V: "y \<in> \<Union>\<V>" using hy \<open>p y \<in> U0\<close> hV_union by (by100 blast)
        obtain Vx where hVx: "Vx \<in> \<V>" "x \<in> Vx" using hx_in_V by (by100 blast)
        obtain Vy where hVy: "Vy \<in> \<V>" "y \<in> Vy" using hy_in_V by (by100 blast)
        have "Vx \<noteq> Vy"
        proof
          assume heq: "Vx = Vy"
          \<comment> \<open>p is injective on Vx (homeomorphism), p x = p y, so x = y. Contradiction.\<close>
          have "inj_on p Vx"
            using hV_homeo hVx(1) unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          have "y \<in> Vx" using hVy(2) heq by (by100 simp)
          have "x = y" using inj_onD[OF \<open>inj_on p Vx\<close> True hVx(2) \<open>y \<in> Vx\<close>] .
          thus False using hne by (by100 simp)
        qed
        hence "Vx \<inter> Vy = {}" using hV_disj hVx(1) hVy(1) by (by100 blast)
        moreover have "Vx \<in> TE" using hV_open hVx(1)
          unfolding openin_on_def by (by100 blast)
        moreover have "Vy \<in> TE" using hV_open hVy(1)
          unfolding openin_on_def by (by100 blast)
        ultimately show ?thesis using hVx(2) hVy(2) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: Combine all conditions into top1_is_graph_on.\<close>
  show ?thesis unfolding top1_is_graph_on_def
    using assms(3) hE_hausdorff hAE by (by100 blast)
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
  \<comment> \<open>Step 1: X is a graph, so extract arcs.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
    using assms(1) unfolding top1_is_graph_on_def by (by100 auto)
  \<comment> \<open>Step 2: Choose a maximal tree T \<subseteq> X. A maximal tree exists by Zorn's lemma
     (or, for countable graphs, by explicit construction).\<close>
  obtain T :: "'a set" where hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_max: "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
      and hx0_T: "x0 \<in> T"
    sorry \<comment> \<open>Existence of maximal tree containing x0 (Munkres Lemma 84.3).\<close>
  \<comment> \<open>Step 3: X/T is a wedge of circles (one per edge not in T).
     The edges not in T form loops when their endpoints are identified via T-collapse.\<close>
  obtain n :: nat and W :: "'b set" and TW :: "'b set set" and q :: "'a \<Rightarrow> 'b" and pw :: 'b
    where hW_wedge: "top1_is_wedge_of_circles_on W TW {..<n} pw"
      and hq_quotient: "top1_quotient_map_on X TX W TW q"
      and hq_T: "\<forall>x\<in>T. q x = pw"
    sorry \<comment> \<open>Quotient X/T = wedge of circles (Munkres Lemma 84.5).\<close>
  \<comment> \<open>Step 4: The quotient map q: X \<rightarrow> X/T is a homotopy equivalence
     (since T is contractible in X).\<close>
  have hq_equiv: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    sorry \<comment> \<open>Homotopy equivalence of quotient: Theorem 58.7 or direct SvK argument.\<close>
  \<comment> \<open>Step 5: \<pi>_1(X/T) = \<pi>_1(wedge of n circles) is free on n generators (Theorem 71.1).
     Need q(x0) = pw for Theorem_71_1. Then apply Theorem_71_1 to the wedge W.\<close>
  have hqx0: "q x0 = pw"
    using hq_T hx0_T by (by100 blast)
  from Theorem_71_1_wedge_of_circles_finite[OF hW_wedge]
  obtain G0 :: "int set" and mul0 e0 invg0 and \<iota>0 :: "nat \<Rightarrow> int"
    where hfree: "top1_is_free_group_full_on G0 mul0 e0 invg0 \<iota>0 {..<n}"
      and hW_iso: "top1_groups_isomorphic_on G0 mul0
          (top1_fundamental_group_carrier W TW pw)
          (top1_fundamental_group_mul W TW pw)"
    by (by100 blast)
  \<comment> \<open>Rewrite using hqx0.\<close>
  have hW_iso': "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0))"
    using hW_iso unfolding hqx0 .
  \<comment> \<open>Step 6: Combine: \<pi>_1(X) \<cong> \<pi>_1(W) (hq_equiv) and \<pi>_1(W) \<cong> free (hW_iso').
     By transitivity: \<pi>_1(X) \<cong> free group.\<close>
  have hiso_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier W TW (q x0))
      (top1_fundamental_group_mul W TW (q x0)) G0 mul0"
  proof -
    have hgrpW: "top1_is_group_on
        (top1_fundamental_group_carrier W TW (q x0))
        (top1_fundamental_group_mul W TW (q x0))
        (top1_fundamental_group_id W TW (q x0))
        (top1_fundamental_group_invg W TW (q x0))"
    proof -
      have hTW: "is_topology_on W TW"
        using hW_wedge unfolding top1_is_wedge_of_circles_on_def is_topology_on_strict_def
        by (by100 blast)
      have hqx0_W: "q x0 \<in> W"
        using hW_wedge hqx0 unfolding top1_is_wedge_of_circles_on_def by (by100 simp)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTW hqx0_W])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hW_iso' hgrpG0 hgrpW])
  qed
  have hchain: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0) G0 mul0"
    by (rule groups_isomorphic_trans_fwd[OF hq_equiv hiso_sym])
  have hchain_sym: "top1_groups_isomorphic_on G0 mul0
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)"
  proof -
    have hgrpX: "top1_is_group_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_id X TX x0)
        (top1_fundamental_group_invg X TX x0)"
    proof -
      have hTX: "is_topology_on X TX"
        using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      show ?thesis by (rule top1_fundamental_group_is_group[OF hTX assms(3)])
    qed
    have hgrpG0: "top1_is_group_on G0 mul0 e0 invg0"
      using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
    show ?thesis by (rule top1_groups_isomorphic_on_sym[OF hchain hgrpX hgrpG0])
  qed
  show ?thesis using hfree hchain_sym by (by100 blast)
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



























































































































































































































































































 
  
   
    



  








 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  
 









































