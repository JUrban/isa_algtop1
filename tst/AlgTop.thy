theory AlgTop
  imports "AlgTopC.AlgTopCached"
begin


\<comment> \<open>===== Theorems with sorry, moved here for caching =====\<close>

text \<open>Lemma 60.5 (Munkres): The fundamental group of the figure eight is not abelian.\<close>
lemma Lemma_60_5_figure_eight_not_abelian:
  assumes "is_topology_on X TX"
      and "top1_is_wedge_of_circles_on X TX {0::nat, 1} p"
  shows "\<not> (\<forall>a\<in>top1_fundamental_group_carrier X TX p.
             \<forall>b\<in>top1_fundamental_group_carrier X TX p.
               top1_fundamental_group_mul X TX p a b = top1_fundamental_group_mul X TX p b a)"
  sorry


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
  \<comment> \<open>Proof: decompose S²-{p,q} = (S²-e13) ∪ (S²-e24). Their intersection S²-(e13∪e24)
     has two components. The 4-cycle loop f alternates between the components,
     creating a nontrivial element by Theorem 63.1.\<close>
  show ?thesis sorry
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
      moreover have "subspace_topology ?Xpq ?TXpq C = ?TC"
        using subspace_topology_trans[OF \<open>C \<subseteq> ?Xpq\<close>] by (by100 simp)
      moreover have "id = (\<lambda>x::(real\<times>real\<times>real). x)" by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
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

text \<open>A free group on a set S is a group G together with \<iota>: S \<hookrightarrow> G such that
  \<iota>(S) generates G, \<iota> is injective, and (externally) for any group H and
  function \<phi>: S \<rightarrow> H there is a unique homomorphism \<psi>: G \<rightarrow> H with \<psi> \<circ> \<iota> = \<phi>.
  See top1_is_free_group_full_on (intrinsic) and top1_free_group_universal_prop
  (external) above.\<close>

(** from \<S>69 Theorem 69.2: free product of free groups on S1, S2 (disjoint)
    is the free group on S1 \<union> S2. **)
theorem Theorem_69_2:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and \<iota>1 \<iota>2 :: "'s \<Rightarrow> 'g"
    and S1 S2 :: "'s set"
  assumes "top1_is_free_group_full_on G1 mul1 e1 invg1 \<iota>1 S1"
      and "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 S2"
      and "S1 \<inter> S2 = {}"
  shows "\<exists>(FP :: (nat \<times> 'g) list set) mulFP eFP invgFP \<iota>fam12 \<iota>S12.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
         \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s))
         \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))"
proof -
  \<comment> \<open>Munkres 69.2: G1 * G2 has reduced words alternating between G1 and G2 elements.
     Since G1 = free on S1 and G2 = free on S2, reduced words in G1*G2 are exactly
     reduced words in S1 \<union> S2 (with S1 \<inter> S2 = {}). So G1*G2 is free on S1\<union>S2.
     The injection \<iota>S12 maps s\<in>S1 to \<iota>fam12(0)(\<iota>1(s)) and s\<in>S2 to \<iota>fam12(1)(\<iota>2(s)).\<close>
  \<comment> \<open>Step 1: Build the free product FP = G1 * G2 (Theorem 68.2).\<close>
  have hgroups: "\<forall>\<alpha>\<in>({0,1}::nat set). top1_is_group_on
      ((if \<alpha> = 0 then G1 else G2)::'g set) (if \<alpha> = 0 then mul1 else mul2)
      (if \<alpha> = 0 then e1 else e2) (if \<alpha> = 0 then invg1 else invg2)"
  proof (intro ballI)
    fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
    hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
    thus "top1_is_group_on (if \<alpha> = 0 then G1 else G2) (if \<alpha> = 0 then mul1 else mul2)
        (if \<alpha> = 0 then e1 else e2) (if \<alpha> = 0 then invg1 else invg2)"
    proof
      assume "\<alpha> = 0"
      thus ?thesis using assms(1) unfolding top1_is_free_group_full_on_def by (by100 simp)
    next
      assume "\<alpha> = 1"
      thus ?thesis using assms(2) unfolding top1_is_free_group_full_on_def by (by100 simp)
    qed
  qed
  obtain FP :: "(nat \<times> 'g) list set" and mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hgroups]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Step 2: Since G1, G2 are free on S1, S2, reduced words in FP correspond to
     reduced words in S1 \<union> S2. Define \<iota>S12.\<close>
  have h_free_on_union: "\<exists>\<iota>S12. top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
    \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)) \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))" sorry
  obtain \<iota>S12 where h\<iota>: "top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)"
      and hcomp1: "\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)"
      and hcomp2: "\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s)"
    using h_free_on_union by (by100 blast)
  show ?thesis using hFP h\<iota> hcomp1 hcomp2 by (by100 blast)
qed

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


(** from \<S>71 Theorem 71.1: finite wedge of circles has free fundamental group
    generated by the individual circle loops. **)
theorem Theorem_71_1_wedge_of_circles_finite:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX {..<n} p"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::nat \<Rightarrow> 'g).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
proof -
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
    moreover from assms obtain C where "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X" and "p \<in> X"
      unfolding top1_is_wedge_of_circles_on_def
      apply (elim conjE exE) by (by100 blast)
    ultimately show False by (by100 simp)
  qed
  have hbase: "n = 0 \<longrightarrow> ?thesis" using hn_pos by (by100 simp)
  \<comment> \<open>n=1: X = single circle ≅ S¹, π₁ = Z = free on 1 generator.
     n≥2: decompose X = X_{n-1} ∪ C_n, intersection {p}. Apply SvK.
     π₁(X) ≅ π₁(X_{n-1}) * π₁(C_n) ≅ free(n-1) * Z ≅ free(n).\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 1: For each finite F \<subseteq> J, the sub-wedge X_F has free fundamental group on F.\<close>
  \<comment> \<open>Step 2: The direct limit of these free groups (as F ranges over finite subsets)
     is the free group on J.\<close>
  show ?thesis sorry
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
  \<comment> \<open>The 1-skeleton is a wedge of 2 circles (Step 1), π₁ of which is free on {a,b} (Step 2).
     Attaching the 2-cell kills the commutator aba⁻¹b⁻¹ (Step 3 via Theorem 72.1).
     So π₁(T) ≅ F({a,b})/⟨⟨aba⁻¹b⁻¹⟩⟩ ≅ Z×Z.\<close>
  show ?thesis sorry
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
  \<comment> \<open>The 1-skeleton is a single circle A with \<pi>_1(A) \<cong> Z.\<close>
  \<comment> \<open>The attaching map wraps S^1 n times around the circle A.\<close>
  \<comment> \<open>By Theorem 72.1: \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.\<close>
  show ?thesis sorry
qed

text \<open>Path homotopy is compatible with path reversal: f \<simeq> g \<Longrightarrow> rev f \<simeq> rev g.\<close>
lemma path_homotopic_subspace_superspace:
  assumes hAsub: "A \<subseteq> X" and hTX: "is_topology_on X TX"
      and hTA: "subspace_topology X TX A = TA"
      and hhom: "top1_path_homotopic_on A TA x0 x1 f g"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  from hhom obtain F where
      hfpath: "top1_is_path_on A TA x0 x1 f"
      and hgpath: "top1_is_path_on A TA x0 x1 g"
      and hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology A TA F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFx0: "\<forall>t\<in>I_set. F (0, t) = x0" and hFx1: "\<forall>t\<in>I_set. F (1, t) = x1"
    unfolding top1_path_homotopic_on_def by (by100 auto)
  \<comment> \<open>F maps into A ⊆ X. Compose with inclusion to get F: I²→X.\<close>
  \<comment> \<open>Continuous map into subspace A → continuous map into X.\<close>
  have hcont_lift: "\<And>S TS f'. top1_continuous_map_on S TS A TA f' \<Longrightarrow>
      top1_continuous_map_on S TS X TX f'"
  proof -
    fix S TS f' assume hf': "top1_continuous_map_on S TS A TA f'"
    show "top1_continuous_map_on S TS X TX f'"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> S"
      thus "f' s \<in> X" using hf' hAsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have "A \<inter> V \<in> TA" using hV hTA unfolding subspace_topology_def by (by100 blast)
      have "{s \<in> S. f' s \<in> V} = {s \<in> S. f' s \<in> A \<inter> V}"
        using hf' unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> TS" using hf' \<open>A \<inter> V \<in> TA\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> S. f' s \<in> V} \<in> TS" .
    qed
  qed
  have hF_X: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    by (rule hcont_lift[OF hF])
  have hfpathX: "top1_is_path_on X TX x0 x1 f"
    using hfpath hcont_lift unfolding top1_is_path_on_def by (by100 blast)
  have hgpathX: "top1_is_path_on X TX x0 x1 g"
    using hgpath hcont_lift unfolding top1_is_path_on_def by (by100 blast)
  show ?thesis unfolding top1_path_homotopic_on_def
    using hF_X hfpathX hgpathX hF0 hF1 hFx0 hFx1 by (by100 blast)
qed

lemma loop_equiv_subspace_superspace:
  assumes hAsub: "A \<subseteq> X" and hTX: "is_topology_on X TX"
      and hTA: "subspace_topology X TX A = TA"
      and hhom: "top1_loop_equiv_on A TA x0 f g"
  shows "top1_loop_equiv_on X TX x0 f g"
proof -
  from hhom have hfA: "top1_is_loop_on A TA x0 f" and hgA: "top1_is_loop_on A TA x0 g"
      and hfg: "top1_path_homotopic_on A TA x0 x0 f g"
    unfolding top1_loop_equiv_on_def by (by100 blast)+
  have hcont_lift_loop: "\<And>f'. top1_continuous_map_on I_set I_top A TA f' \<Longrightarrow>
      top1_continuous_map_on I_set I_top X TX f'"
  proof -
    fix f' assume "top1_continuous_map_on I_set I_top A TA f'"
    show "top1_continuous_map_on I_set I_top X TX f'"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "f' s \<in> X"
        using \<open>top1_continuous_map_on I_set I_top A TA f'\<close> hAsub
        unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have "A \<inter> V \<in> TA" using hV hTA unfolding subspace_topology_def by (by100 blast)
      have heq: "{s \<in> I_set. f' s \<in> V} = {s \<in> I_set. f' s \<in> A \<inter> V}"
      proof (rule Collect_cong)
        fix s show "(s \<in> I_set \<and> f' s \<in> V) = (s \<in> I_set \<and> f' s \<in> A \<inter> V)"
          using \<open>top1_continuous_map_on I_set I_top A TA f'\<close>
          unfolding top1_continuous_map_on_def by (by100 blast)
      qed
      have "{s \<in> I_set. f' s \<in> A \<inter> V} \<in> I_top"
        using \<open>top1_continuous_map_on I_set I_top A TA f'\<close> \<open>A \<inter> V \<in> TA\<close>
        unfolding top1_continuous_map_on_def by (by100 blast)
      thus "{s \<in> I_set. f' s \<in> V} \<in> I_top" using heq by (by100 simp)
    qed
  qed
  have hfX: "top1_is_loop_on X TX x0 f"
    using hfA hcont_lift_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hgX: "top1_is_loop_on X TX x0 g"
    using hgA hcont_lift_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have "top1_path_homotopic_on X TX x0 x0 f g"
    by (rule path_homotopic_subspace_superspace[OF hAsub hTX hTA hfg])
  thus ?thesis using hfX hgX unfolding top1_loop_equiv_on_def by (by100 blast)
qed

lemma path_homotopic_reverse_congruence:
  assumes hTX: "is_topology_on X TX"
      and hhom: "top1_path_homotopic_on X TX x0 x1 f g"
  shows "top1_path_homotopic_on X TX x1 x0 (top1_path_reverse f) (top1_path_reverse g)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hhom unfolding top1_path_homotopic_on_def by blast
  \<comment> \<open>G(s,t) = F(1-s, t): homotopy from rev f to rev g.\<close>
  let ?G = "\<lambda>p. F (1 - fst p, snd p)"
  have hflip_s: "top1_continuous_map_on (I_set \<times> I_set) II_topology
      (I_set \<times> I_set) II_topology (\<lambda>p. (1 - fst p, snd p))"
  proof -
    \<comment> \<open>By Theorem_18_4: \<pi>1 \<circ> flip = (1-) \<circ> \<pi>1, \<pi>2 \<circ> flip = \<pi>2.\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTP: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>(1-) continuous I \<rightarrow> I.\<close>
    have h1minus: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>s. 1 - s)"
      unfolding top1_unit_interval_topology_def
      by (rule top1_continuous_map_on_real_subspace_open_sets)
         (auto simp: top1_unit_interval_def intro: continuous_intros)
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hpi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
      unfolding II_topology_def by (rule top1_continuous_pi2[OF hTI hTI])
    have hpi1_flip: "pi1 \<circ> (\<lambda>p. (1 - fst p, snd p)) = (\<lambda>s. 1 - s) \<circ> pi1"
      unfolding pi1_def comp_def by (rule ext, simp add: case_prod_beta)
    have hpi2_flip: "pi2 \<circ> (\<lambda>p. (1 - fst p, snd p)) = pi2"
      unfolding pi2_def comp_def by (rule ext, simp add: case_prod_beta)
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      unfolding hpi1_flip by (rule top1_continuous_map_on_comp[OF hpi1 h1minus])
    moreover have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi2 \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      unfolding hpi2_flip by (rule hpi2)
    ultimately have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
        (I_set \<times> I_set) (product_topology_on I_top I_top) (\<lambda>p. (1 - fst p, snd p))"
      using iffD2[OF Theorem_18_4[OF hTP hTI hTI]] unfolding II_topology_def by (by100 blast)
    thus ?thesis unfolding II_topology_def .
  qed
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (F \<circ> (\<lambda>p. (1 - fst p, snd p)))"
      by (rule top1_continuous_map_on_comp[OF hflip_s hF])
    thus ?thesis unfolding comp_def by (by100 simp)
  qed
  have hfp: "top1_is_path_on X TX x0 x1 f" and hgp: "top1_is_path_on X TX x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by blast+
  have "top1_path_homotopic_on X TX x1 x0 (top1_path_reverse f) (top1_path_reverse g)"
    unfolding top1_path_homotopic_on_def
  proof (intro exI[of _ ?G] conjI)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G" by (rule hG)
    show "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_reverse f s"
      unfolding top1_path_reverse_def using hF0
      unfolding top1_unit_interval_def by (by100 auto)
    show "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_reverse g s"
      unfolding top1_path_reverse_def using hF1
      unfolding top1_unit_interval_def by (by100 auto)
    show "\<forall>t\<in>I_set. ?G (0, t) = x1"
      using hFright by (by100 simp)
    show "\<forall>t\<in>I_set. ?G (1, t) = x0"
      using hFleft by (by100 simp)
    show "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_path[OF hfp])
    show "top1_is_path_on X TX x1 x0 (top1_path_reverse g)"
      by (rule top1_path_reverse_is_path[OF hgp])
  qed
  thus ?thesis .
qed

text \<open>Fundamental group inverse of a class equals the class of the reverse.\<close>
lemma fundamental_group_invg_class:
  assumes hTX: "is_topology_on X TX" and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_fundamental_group_invg X TX x0
      {g. top1_loop_equiv_on X TX x0 f g}
    = {g. top1_loop_equiv_on X TX x0 (top1_path_reverse f) g}"
proof (rule set_eqI, rule iffI)
  fix h assume "h \<in> top1_fundamental_group_invg X TX x0
      {g. top1_loop_equiv_on X TX x0 f g}"
  then obtain f' where hf': "top1_loop_equiv_on X TX x0 f f'"
      and hh: "top1_loop_equiv_on X TX x0 (top1_path_reverse f') h"
    unfolding top1_fundamental_group_invg_def by (by100 blast)
  have hff': "top1_path_homotopic_on X TX x0 x0 f f'"
    using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
  have hrev: "top1_loop_equiv_on X TX x0 (top1_path_reverse f) (top1_path_reverse f')"
  proof -
    have "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse f')"
      by (rule path_homotopic_reverse_congruence[OF hTX hff'])
    moreover have "top1_is_loop_on X TX x0 (top1_path_reverse f)"
      using hf unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
    moreover have "top1_is_loop_on X TX x0 (top1_path_reverse f')"
    proof -
      have "top1_is_loop_on X TX x0 f'" using hf' unfolding top1_loop_equiv_on_def by (by100 blast)
      thus ?thesis unfolding top1_is_loop_on_def by (rule top1_path_reverse_is_path)
    qed
    ultimately show ?thesis unfolding top1_loop_equiv_on_def by (by100 blast)
  qed
  from top1_loop_equiv_on_trans[OF hTX hrev hh]
  show "h \<in> {g. top1_loop_equiv_on X TX x0 (top1_path_reverse f) g}" by (by100 blast)
next
  fix h assume "h \<in> {g. top1_loop_equiv_on X TX x0 (top1_path_reverse f) g}"
  hence "top1_loop_equiv_on X TX x0 (top1_path_reverse f) h" by (by100 blast)
  moreover have "f \<in> {g. top1_loop_equiv_on X TX x0 f g}"
    using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
  ultimately show "h \<in> top1_fundamental_group_invg X TX x0
      {g. top1_loop_equiv_on X TX x0 f g}"
    unfolding top1_fundamental_group_invg_def by (by100 blast)
qed

text \<open>The fundamental group \<pi>_1(X, x_0) is a group under path-product of equivalence classes.\<close>
lemma top1_fundamental_group_is_group:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
  shows "top1_is_group_on
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_mul X TX x0)
    (top1_fundamental_group_id X TX x0)
    (top1_fundamental_group_invg X TX x0)"
  unfolding top1_is_group_on_def
proof (intro conjI)
  let ?G = "top1_fundamental_group_carrier X TX x0"
  let ?mul = "top1_fundamental_group_mul X TX x0"
  let ?e = "top1_fundamental_group_id X TX x0"
  let ?inv = "top1_fundamental_group_invg X TX x0"
  have hconst_loop: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_loop[OF hTX hx0])
  \<comment> \<open>(1) Identity in carrier.\<close>
  show "?e \<in> ?G"
    unfolding top1_fundamental_group_carrier_def top1_fundamental_group_id_def
    using hconst_loop by (by100 blast)
  \<comment> \<open>(2) Closure under mul.\<close>
  show "\<forall>x\<in>?G. \<forall>y\<in>?G. ?mul x y \<in> ?G"
  proof (intro ballI)
    fix c1 c2 assume "c1 \<in> ?G" "c2 \<in> ?G"
    then obtain f g where hf: "top1_is_loop_on X TX x0 f" and hc1: "c1 = {h. top1_loop_equiv_on X TX x0 f h}"
        and hg: "top1_is_loop_on X TX x0 g" and hc2: "c2 = {h. top1_loop_equiv_on X TX x0 g h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfg: "top1_is_loop_on X TX x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTX hf hg])
    have "?mul c1 c2 = {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
      unfolding hc1 hc2 by (rule top1_fundamental_group_mul_class[OF hTX hf hg])
    thus "?mul c1 c2 \<in> ?G"
      unfolding top1_fundamental_group_carrier_def using hfg by (by100 blast)
  qed
  \<comment> \<open>(3) Closure under inverse.\<close>
  show "\<forall>x\<in>?G. ?inv x \<in> ?G"
  proof (intro ballI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hrf: "top1_is_loop_on X TX x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_loop[OF hf])
    have hinvc: "?inv c = {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> ?inv c"
      then obtain g where hg_in: "g \<in> c" and hrev_g_h: "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
      have hg_equiv: "top1_loop_equiv_on X TX x0 f g" using hg_in unfolding hc by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 f g" unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)"
        by (rule path_homotopic_reverse_congruence[OF hTX])
      have hg_loop: "top1_is_loop_on X TX x0 g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      have hrg: "top1_is_loop_on X TX x0 (top1_path_reverse g)" by (rule top1_path_reverse_is_loop[OF hg_loop])
      hence "top1_loop_equiv_on X TX x0 (top1_path_reverse f) (top1_path_reverse g)"
        unfolding top1_loop_equiv_on_def
        using hrf \<open>top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)\<close>
        by (by100 blast)
      moreover have "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h" by (rule hrev_g_h)
      ultimately show "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] hrf by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
      hence "top1_loop_equiv_on X TX x0 (top1_path_reverse f) h" by (by100 blast)
      moreover have "f \<in> c" unfolding hc using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
      ultimately show "h \<in> ?inv c"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
    qed
    show "?inv c \<in> ?G"
      unfolding hinvc top1_fundamental_group_carrier_def using hrf by (by100 blast)
  qed
  \<comment> \<open>(4) Associativity.\<close>
  show "\<forall>x\<in>?G. \<forall>y\<in>?G. \<forall>z\<in>?G. ?mul (?mul x y) z = ?mul x (?mul y z)"
  proof (intro ballI)
    fix c1 c2 c3 assume "c1 \<in> ?G" "c2 \<in> ?G" "c3 \<in> ?G"
    then obtain f g h where hf: "top1_is_loop_on X TX x0 f" and hc1: "c1 = {k. top1_loop_equiv_on X TX x0 f k}"
        and hg: "top1_is_loop_on X TX x0 g" and hc2: "c2 = {k. top1_loop_equiv_on X TX x0 g k}"
        and hh: "top1_is_loop_on X TX x0 h" and hc3: "c3 = {k. top1_loop_equiv_on X TX x0 h k}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    have hgp: "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
    have hhp: "top1_is_path_on X TX x0 x0 h" using hh unfolding top1_is_loop_on_def .
    have hfg: "top1_is_loop_on X TX x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTX hf hg])
    have hgh: "top1_is_loop_on X TX x0 (top1_path_product g h)"
      by (rule top1_path_product_is_loop[OF hTX hg hh])
    \<comment> \<open>LHS: (c1*c2)*c3 = [(f*g)*h].\<close>
    have "?mul c1 c2 = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hc1 hc2 by (rule top1_fundamental_group_mul_class[OF hTX hf hg])
    hence hlhs: "?mul (?mul c1 c2) c3 = {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
      unfolding hc3 by (by100 simp) (rule top1_fundamental_group_mul_class[OF hTX hfg hh])
    \<comment> \<open>RHS: c1*(c2*c3) = [f*(g*h)].\<close>
    have "?mul c2 c3 = {k. top1_loop_equiv_on X TX x0 (top1_path_product g h) k}"
      unfolding hc2 hc3 by (rule top1_fundamental_group_mul_class[OF hTX hg hh])
    hence hrhs: "?mul c1 (?mul c2 c3) = {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
      unfolding hc1 by (by100 simp) (rule top1_fundamental_group_mul_class[OF hTX hf hgh])
    \<comment> \<open>By Theorem_51_2_associativity: (f*g)*h \<simeq> f*(g*h). Hence equiv classes equal.\<close>
    have hassoc_path: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product f (top1_path_product g h)) (top1_path_product (top1_path_product f g) h)"
      by (rule Theorem_51_2_associativity[OF hTX hfp hgp hhp])
    have "{k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
    proof (rule set_eqI, rule iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
      hence "top1_is_loop_on X TX x0 k" "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_product f g) h) k"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_product g h)) (top1_path_product (top1_path_product f g) h)"
        by (rule hassoc_path)
      ultimately show "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] top1_path_product_is_loop[OF hTX hf hgh] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_product g h)) k}"
      hence "top1_is_loop_on X TX x0 k" "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_product g h)) k"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_product f g) h) (top1_path_product f (top1_path_product g h))"
        by (rule Lemma_51_1_path_homotopic_sym[OF hassoc_path])
      ultimately show "k \<in> {k. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_product f g) h) k}"
        unfolding top1_loop_equiv_on_def
        using Lemma_51_1_path_homotopic_trans[OF hTX] top1_path_product_is_loop[OF hTX hfg hh] by (by100 blast)
    qed
    thus "?mul (?mul c1 c2) c3 = ?mul c1 (?mul c2 c3)" unfolding hlhs hrhs .
  qed
  \<comment> \<open>(5) Left identity.\<close>
  show "\<forall>x\<in>?G. ?mul ?e x = x \<and> ?mul x ?e = x"
  proof (intro ballI conjI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    \<comment> \<open>Left identity: [const]*[f] = [const*f] = [f] by Theorem_51_2_left_identity.\<close>
    have "?mul ?e c = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
      unfolding top1_fundamental_group_id_def hc
      by (rule top1_fundamental_group_mul_class[OF hTX hconst_loop hf])
    also have "\<dots> = {h. top1_loop_equiv_on X TX x0 f h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
      hence "top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h"
        by (by100 blast)
      hence "top1_is_loop_on X TX x0 h \<and> top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) f"
        by (rule Theorem_51_2_left_identity[OF hTX hfp])
      ultimately have "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h" by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 f (top1_path_product (top1_constant_path x0) f)"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_left_identity[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 f h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
        unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      hence hloop_h: "top1_is_loop_on X TX x0 h" and hhom: "top1_path_homotopic_on X TX x0 x0 f h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) f"
        by (rule Theorem_51_2_left_identity[OF hTX hfp])
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_constant_path x0) f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX _ hhom] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_constant_path x0) f) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hconst_loop hf] hloop_h by (by100 blast)
    qed
    finally show "?mul ?e c = c" unfolding hc .
    \<comment> \<open>Right identity: [f]*[const] = [f*const] = [f] by Theorem_51_2_right_identity.\<close>
    have "?mul c ?e = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
      unfolding hc top1_fundamental_group_id_def
      by (rule top1_fundamental_group_mul_class[OF hTX hf hconst_loop])
    also have "\<dots> = {h. top1_loop_equiv_on X TX x0 f h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 f (top1_path_product f (top1_constant_path x0))"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_right_identity[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 f h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
        unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      hence hloop_h: "top1_is_loop_on X TX x0 h" and hhom: "top1_path_homotopic_on X TX x0 x0 f h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) f"
        by (rule Theorem_51_2_right_identity[OF hTX hfp])
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_constant_path x0)) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX _ hhom] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_constant_path x0)) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hf hconst_loop] hloop_h by (by100 blast)
    qed
    finally show "?mul c ?e = c" unfolding hc .
  qed
  \<comment> \<open>(6) Inverse.\<close>
  show "\<forall>x\<in>?G. ?mul (?inv x) x = ?e \<and> ?mul x (?inv x) = ?e"
  proof (intro ballI conjI)
    fix c assume "c \<in> ?G"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
    have hrf: "top1_is_loop_on X TX x0 (top1_path_reverse f)"
      by (rule top1_path_reverse_is_loop[OF hf])
    have hrfp: "top1_is_path_on X TX x0 x0 (top1_path_reverse f)"
      using hrf unfolding top1_is_loop_on_def .
    \<comment> \<open>inv([f]) = {h. \<exists>g\<in>[f]. rev(g) \<simeq> h} = [rev f] (reverse respects equiv class).\<close>
    have hinvc: "?inv c = {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> ?inv c"
      then obtain g where hg_in: "g \<in> c" and hrev_g_h: "top1_loop_equiv_on X TX x0 (top1_path_reverse g) h"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
      have hg_equiv: "top1_loop_equiv_on X TX x0 f g" using hg_in unfolding hc by (by100 blast)
      have hg_loop: "top1_is_loop_on X TX x0 g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_path_homotopic_on X TX x0 x0 f g" using hg_equiv unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) (top1_path_reverse g)"
        by (rule path_homotopic_reverse_congruence[OF hTX])
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse g) h"
        using hrev_g_h unfolding top1_loop_equiv_on_def by (by100 blast)
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_reverse f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
        unfolding top1_loop_equiv_on_def using hrf hrev_g_h unfolding top1_loop_equiv_on_def by (by100 blast)
    next
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"
      moreover have "f \<in> c" unfolding hc using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
      ultimately show "h \<in> ?inv c"
        unfolding top1_fundamental_group_invg_def by (by100 blast)
    qed
    \<comment> \<open>Left inverse: [rev f]*[f] = [rev f * f] = [const].\<close>
    have "?mul (?inv c) c = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
    proof -
      have "?mul {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h} {h. top1_loop_equiv_on X TX x0 f h}
          = {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX hrf hf])
      thus ?thesis using hinvc hc by (by100 simp)
    qed
    also have "\<dots> = ?e"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) (top1_path_product (top1_path_reverse f) f)"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_right[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> ?e" unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
        using hconst_loop \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> ?e"
      hence "top1_is_loop_on X TX x0 h" "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) (top1_constant_path x0)"
        by (rule Theorem_51_2_invgerse_right[OF hTX hfp])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_product (top1_path_reverse f) f) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product (top1_path_reverse f) f) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hrf hf] \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    qed
    finally show "?mul (?inv c) c = ?e" .
    \<comment> \<open>Right inverse: [f]*[rev f] = [f * rev f] = [const].\<close>
    have "?mul c (?inv c) = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
    proof -
      have "?mul {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}
          = {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX hf hrf])
      thus ?thesis using hinvc hc by (by100 simp)
    qed
    also have "\<dots> = ?e"
    proof (rule set_eqI, rule iffI)
      fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
      hence "top1_is_loop_on X TX x0 h"
          "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) h"
        unfolding top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) (top1_path_product f (top1_path_reverse f))"
        by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_left[OF hTX hfp]])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> ?e" unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
        using hconst_loop \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    next
      fix h assume "h \<in> ?e"
      hence "top1_is_loop_on X TX x0 h" "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) h"
        unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def by (by100 blast)+
      moreover have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
        by (rule Theorem_51_2_invgerse_left[OF hTX hfp])
      ultimately have "top1_path_homotopic_on X TX x0 x0 (top1_path_product f (top1_path_reverse f)) h"
        using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
      thus "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f (top1_path_reverse f)) h}"
        unfolding top1_loop_equiv_on_def
        using top1_path_product_is_loop[OF hTX hf hrf] \<open>top1_is_loop_on X TX x0 h\<close> by (by100 blast)
    qed
    finally show "?mul c (?inv c) = ?e" .
  qed
qed


(** from \<S>70 Theorem 70.2 (Seifert-van Kampen, classical version): if X = U \<union> V
    with U, V, U \<inter> V open and path-connected, then \<pi>_1(X, x_0) is isomorphic to
    the free product of \<pi>_1(U, x_0) and \<pi>_1(V, x_0) amalgamated over \<pi>_1(U \<inter> V, x_0).
    Equivalently, the images i_*(\<pi>_1(U)) and j_*(\<pi>_1(V)) generate \<pi>_1(X), and the
    kernel of the natural surjection is the normal subgroup generated by elements
    of the form (i_1)_*(\<gamma>) \<cdot> ((i_2)_*(\<gamma>))^{-1} for \<gamma> \<in> \<pi>_1(U \<inter> V). **)
theorem Theorem_70_2_SvK:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0
                then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
             (\<lambda>i. if i = 0
                then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
             \<iota>fam {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                        (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                        U (subspace_topology X TX U) x0 (\<lambda>x. x) c))
                          (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                            (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                            V (subspace_topology X TX V) x0 (\<lambda>x. x) c)))
                    | c. c \<in> top1_fundamental_group_carrier
                           (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 }))
             (top1_quotient_group_mul_on mulFP)"
  \<comment> \<open>See Theorem_70_2_SvK_parameterized for the non-existential version.
     UNPROVABLE: free type variable 'f cannot be instantiated.
     Use Theorem_70_2_SvK_parameterized instead.\<close>
  oops

lemma inclusion_induced_class:
  assumes hAsub: "A \<subseteq> X" and hTX: "is_topology_on X TX"
      and hTA: "subspace_topology X TX A = TA"
      and hg: "top1_is_loop_on A TA x0 g"
  shows "top1_fundamental_group_induced_on A TA x0 X TX x0 (\<lambda>x. x)
      {h. top1_loop_equiv_on A TA x0 g h} = {h. top1_loop_equiv_on X TX x0 g h}"
proof (rule set_eqI, rule iffI)
  fix k
  assume "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 (\<lambda>x. x)
      {h. top1_loop_equiv_on A TA x0 g h}"
  then obtain f' where hf': "top1_loop_equiv_on A TA x0 g f'"
      and hk: "top1_loop_equiv_on X TX x0 ((\<lambda>x. x) \<circ> f') k"
    unfolding top1_fundamental_group_induced_on_def by (by100 auto)
  have "top1_loop_equiv_on X TX x0 g f'"
    by (rule loop_equiv_subspace_superspace[OF hAsub hTX hTA hf'])
  moreover have "top1_loop_equiv_on X TX x0 f' k"
  proof -
    have "((\<lambda>x. x) \<circ> f') = f'" by (by100 auto)
    thus ?thesis using hk by (by100 simp)
  qed
  ultimately have "top1_loop_equiv_on X TX x0 g k"
    by (rule top1_loop_equiv_on_trans[OF hTX])
  thus "k \<in> {h. top1_loop_equiv_on X TX x0 g h}" by (by100 blast)
next
  fix k
  assume hk: "k \<in> {h. top1_loop_equiv_on X TX x0 g h}"
  hence "top1_loop_equiv_on X TX x0 g k" by (by100 blast)
  have "g \<in> {h. top1_loop_equiv_on A TA x0 g h}"
  proof -
    have "top1_loop_equiv_on A TA x0 g g"
      using top1_loop_equiv_on_refl[of A TA x0 g] hg unfolding top1_is_loop_on_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  moreover have "top1_loop_equiv_on X TX x0 ((\<lambda>x. x) \<circ> g) k"
  proof -
    have "((\<lambda>x. x) \<circ> g) = g" by (by100 auto)
    thus ?thesis using \<open>top1_loop_equiv_on X TX x0 g k\<close> by (by100 simp)
  qed
  ultimately show "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 (\<lambda>x. x)
      {h. top1_loop_equiv_on A TA x0 g h}"
    unfolding top1_fundamental_group_induced_on_def by (by100 auto)
qed

lemma continuous_map_restrict_codomain:
  assumes hf: "top1_continuous_map_on S TS X TX f"
      and hrange: "\<forall>s\<in>S. f s \<in> A"
      and hAsub: "A \<subseteq> X"
  shows "top1_continuous_map_on S TS A (subspace_topology X TX A) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix s assume "s \<in> S" thus "f s \<in> A" using hrange by (by100 blast)
next
  fix V assume hV: "V \<in> subspace_topology X TX A"
  then obtain W where hW: "W \<in> TX" and hVeq: "V = A \<inter> W"
    unfolding subspace_topology_def by (by100 blast)
  have "{s \<in> S. f s \<in> V} = {s \<in> S. f s \<in> W}"
  proof (rule Collect_cong)
    fix s show "(s \<in> S \<and> f s \<in> V) = (s \<in> S \<and> f s \<in> W)"
      using hVeq hrange by (by100 blast)
  qed
  thus "{s \<in> S. f s \<in> V} \<in> TS"
    using hf hW unfolding top1_continuous_map_on_def by (by100 simp)
qed

text \<open>Helper for SvK surjectivity: a foldr path product of pieces, each in U or V,
  gives a loop class in any subgroup H of π₁(X) containing loops from U and V.\<close>
lemma svk_pieces_in_subgroup:
  assumes hTX: "is_topology_on X TX"
      and hUsub: "U \<subseteq> X" and hVsub: "V \<subseteq> X"
      and hUpc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hVpc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hUVpc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hx0: "x0 \<in> U \<inter> V"
      and hH_grp: "top1_is_group_on H (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
      and hU_in_H: "\<And>g. top1_is_loop_on U (subspace_topology X TX U) x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> H"
      and hV_in_H: "\<And>g. top1_is_loop_on V (subspace_topology X TX V) x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> H"
      \<comment> \<open>ps is a list of paths composable end-to-end, each mapping into U or V,
         starting at x₀ and ending at x₀.\<close>
      and hk: "k \<ge> 1" and hlen: "length ps = k"
      and hps_UV: "\<And>i. i < k \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (ps!i) t \<in> U)
                                  \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (ps!i) t \<in> V)"
      and hps_cont: "\<And>i. i < k \<Longrightarrow> top1_continuous_map_on I_set I_top X TX (ps!i)"
      and hps_endpts: "\<And>i. i < k \<Longrightarrow> (ps!i) 0 = (if i = 0 then x0 else (ps!(i-1)) 1)"
      and hps_end: "(ps!(k-1)) 1 = x0"
  shows "{g. top1_loop_equiv_on X TX x0
      (foldr top1_path_product ps (top1_constant_path x0)) g} \<in> H"
  using hk hlen hps_UV hps_cont hps_endpts hps_end
proof (induction k arbitrary: ps rule: nat_induct_at_least[of 1])
  case base
  \<comment> \<open>k=1: single piece p₀ maps into U or V, is a loop at x₀.\<close>
  hence hlen1: "length ps = 1" by (by100 simp)
  then obtain p where hps_eq: "ps = [p]" by (cases ps) (by100 auto)+
  have hp_UV: "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> U) \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> V)"
    using base.prems(2)[of 0] hps_eq by (by100 simp)
  have hp_cont: "top1_continuous_map_on I_set I_top X TX p"
    using base.prems(3)[of 0] hps_eq by (by100 simp)
  have hp0: "p 0 = x0" using base.prems(4)[of 0] hps_eq by (by100 simp)
  have hp1: "p 1 = x0" using base.prems(5) hps_eq by (by100 simp)
  \<comment> \<open>p is a loop at x₀ in U or V.\<close>
  have hfold_eq: "foldr top1_path_product ps (top1_constant_path x0)
      = top1_path_product p (top1_constant_path x0)" using hps_eq by (by100 simp)
  \<comment> \<open>[p · const] = [p] in π₁(X) by right identity.\<close>
  \<comment> \<open>And [p] ∈ H since p is a loop in U or V.\<close>
  \<comment> \<open>p is a loop in X. If p maps into U (or V), it's a loop in U (or V).\<close>
  \<comment> \<open>The class [p·const] = [p] by right identity. And [p] ∈ H.\<close>
  \<comment> \<open>But the subspace continuity needs: continuous I → U (not just I → X with range in U).\<close>
  have hp_loop_in_U_or_V: "top1_is_loop_on U (subspace_topology X TX U) x0 p
      \<or> top1_is_loop_on V (subspace_topology X TX V) x0 p"
  proof -
    from hp_UV show ?thesis
    proof
      assume hpU: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> U"
      have "\<forall>s\<in>I_set. p s \<in> U"
        using hpU unfolding top1_unit_interval_def by (by100 auto)
      hence "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) p"
        by (rule continuous_map_restrict_codomain[OF hp_cont _ hUsub])
      thus ?thesis using hp0 hp1 hx0 unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
    next
      assume hpV: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> V"
      have "\<forall>s\<in>I_set. p s \<in> V"
        using hpV unfolding top1_unit_interval_def by (by100 auto)
      hence "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) p"
        by (rule continuous_map_restrict_codomain[OF hp_cont _ hVsub])
      thus ?thesis using hp0 hp1 hx0 unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
    qed
  qed
  have "[p] ∈ H": "{h. top1_loop_equiv_on X TX x0 p h} \<in> H"
    using hp_loop_in_U_or_V hU_in_H hV_in_H by (by100 blast)
  have hfold1: "foldr top1_path_product [p] (top1_constant_path x0)
      = top1_path_product p (top1_constant_path x0)" by (by100 simp)
  \<comment> \<open>[p · const] = [p] by right identity in π₁(X).\<close>
  have "{g. top1_loop_equiv_on X TX x0 (top1_path_product p (top1_constant_path x0)) g}
      = {g. top1_loop_equiv_on X TX x0 p g}"
  proof -
    have hp_path: "top1_is_path_on X TX x0 x0 p"
      using hp_cont hp0 hp1 unfolding top1_is_path_on_def by (by100 blast)
    have hri: "top1_path_homotopic_on X TX x0 x0 (top1_path_product p (top1_constant_path x0)) p"
      by (rule Theorem_51_2_right_identity[OF hTX hp_path])
    have hri_equiv: "top1_loop_equiv_on X TX x0 (top1_path_product p (top1_constant_path x0)) p"
    proof -
      have "top1_is_loop_on X TX x0 (top1_path_product p (top1_constant_path x0))"
        using hri unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
      moreover have "top1_is_loop_on X TX x0 p"
        using hp_path unfolding top1_is_loop_on_def by (by100 blast)
      ultimately show ?thesis using hri unfolding top1_loop_equiv_on_def top1_is_loop_on_def
        by (by100 blast)
    qed
    show ?thesis
    proof (rule set_eqI)
      fix k show "k \<in> {g. top1_loop_equiv_on X TX x0 (top1_path_product p (top1_constant_path x0)) g}
          \<longleftrightarrow> k \<in> {g. top1_loop_equiv_on X TX x0 p g}"
      proof -
        have hri_sym: "top1_loop_equiv_on X TX x0 p (top1_path_product p (top1_constant_path x0))"
          by (rule top1_loop_equiv_on_sym[OF hri_equiv])
        show ?thesis
          using top1_loop_equiv_on_trans[OF hTX hri_equiv]
                top1_loop_equiv_on_trans[OF hTX hri_sym] by (by100 blast)
      qed
    qed
  qed
  have "{g. top1_loop_equiv_on X TX x0 (foldr top1_path_product ps (top1_constant_path x0)) g}
      = {g. top1_loop_equiv_on X TX x0 p g}"
    using hfold_eq \<open>{g. top1_loop_equiv_on X TX x0 (top1_path_product p (top1_constant_path x0)) g}
      = {g. top1_loop_equiv_on X TX x0 p g}\<close> by (by100 simp)
  show ?case using \<open>{h. top1_loop_equiv_on X TX x0 p h} \<in> H\<close>
    \<open>{g. top1_loop_equiv_on X TX x0 (foldr top1_path_product ps (top1_constant_path x0)) g}
      = {g. top1_loop_equiv_on X TX x0 p g}\<close> by (by100 simp)
next
  case (Suc k')
  \<comment> \<open>k ≥ 2: split first piece, conjugate with connecting path, use induction.\<close>
  hence hk': "k' \<ge> 1" using Suc.prems(1) by (by100 arith)
  have hlen_ge2: "length ps \<ge> 2" using Suc.prems(1) Suc.hyps by (by100 linarith)
  obtain p rest where hps_eq: "ps = p # rest" using hlen_ge2 by (cases ps) (by100 auto)+
  have hrest_len: "length rest = k'" using Suc.prems(1) hps_eq Suc.hyps by (by100 simp)
  have hp_UV: "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> U) \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> V)"
    using Suc.prems(2)[of 0] hps_eq by (by100 simp)
  have hp0: "p 0 = x0" using Suc.prems(4)[of 0] hps_eq by (by100 simp)
  have hp1_eq: "p 1 = (rest!0) 0"
  proof -
    have "1 < Suc k'" using hk' by (by100 linarith)
    hence "(ps!1) 0 = (ps!0) 1" using Suc.prems(4)[of 1] by (by100 simp)
    thus ?thesis using hps_eq by (by100 simp)
  qed
  \<comment> \<open>p(1) ∈ U ∩ V (since p maps to U or V, and rest!0 maps to U or V, sharing endpoint).\<close>
  \<comment> \<open>Choose connecting path γ from x₀ to p(1) in S(p) ∩ S(rest!0).\<close>
  \<comment> \<open>[p # rest, const] = [p] · [rest, const] in π₁ → decompose.\<close>
  \<comment> \<open>[p · rest...] = [p · γ⁻¹] · [γ · rest...] via γ⁻¹·γ cancellation.\<close>
  \<comment> \<open>[p · γ⁻¹] is a loop in U/V at x₀ → ∈ H.\<close>
  \<comment> \<open>[γ · rest...] is a product of k' pieces → ∈ H by IH.\<close>
  \<comment> \<open>Product ∈ H (subgroup closure).\<close>
  \<comment> \<open>Determine which sets p and rest!0 map into.\<close>
  define Sp where "Sp = (if (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> U) then U else V)"
  define S1 where "S1 = (if (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (rest!0) t \<in> U) then U else V)"
  have hSp_UV: "Sp = U \<or> Sp = V" unfolding Sp_def by (by100 auto)
  have hS1_UV: "S1 = U \<or> S1 = V" unfolding S1_def by (by100 auto)
  have hp_in_Sp: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> p t \<in> Sp" unfolding Sp_def using hp_UV by (by100 auto)
  have hp_cont: "top1_continuous_map_on I_set I_top X TX p"
    using Suc.prems(3)[of 0] hps_eq by (by100 simp)
  \<comment> \<open>p(1) ∈ Sp. rest!0 starts at p(1) ∈ S1. So p(1) ∈ Sp ∩ S1.\<close>
  have hp1_in_Sp: "p 1 \<in> Sp" using hp_in_Sp by (by100 simp)
  have hp1_in_S1: "p 1 \<in> S1"
  proof -
    have "0 < Suc k'" using hk' by (by100 linarith)
    have "1 < Suc k'" using hk' by (by100 linarith)
    have hps1_UV: "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (ps!1) t \<in> U)
        \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (ps!1) t \<in> V)"
      using Suc.prems(2)[OF \<open>1 < Suc k'\<close>] by (by100 blast)
    have hrest0_UV: "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (rest!0) t \<in> U)
        \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (rest!0) t \<in> V)"
      using hps1_UV hps_eq by (by100 simp)
    have "((rest!0) 0) \<in> S1" unfolding S1_def using hrest0_UV by (by100 auto)
    thus ?thesis using hp1_eq by (by100 simp)
  qed
  have hx0_in_Sp: "x0 \<in> Sp" using hSp_UV hx0 by (by100 blast)
  have hx0_in_S1: "x0 \<in> S1" using hS1_UV hx0 by (by100 blast)
  \<comment> \<open>Sp ∩ S1 is path-connected (U, V, or U∩V).\<close>
  have hSpS1_pc: "top1_path_connected_on (Sp \<inter> S1) (subspace_topology X TX (Sp \<inter> S1))"
  proof -
    have "Sp \<inter> S1 \<in> {U, V, U \<inter> V}" using hSp_UV hS1_UV by (by100 auto)
    moreover have "top1_path_connected_on U (subspace_topology X TX U)" using hUpc by (by100 blast)
    moreover have "top1_path_connected_on V (subspace_topology X TX V)" using hVpc by (by100 blast)
    moreover have "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      using hUVpc by (by100 blast)
    ultimately show ?thesis by (by100 auto)
  qed
  \<comment> \<open>Choose connecting path γ from x₀ to p(1) in Sp ∩ S1.\<close>
  obtain \<gamma> where h\<gamma>: "top1_is_path_on (Sp \<inter> S1) (subspace_topology X TX (Sp \<inter> S1)) x0 (p 1) \<gamma>"
    using hSpS1_pc hx0_in_Sp hx0_in_S1 hp1_in_Sp hp1_in_S1
    unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>g₀ = p · γ⁻¹ is a loop at x₀ in Sp. [g₀] ∈ H.\<close>
  \<comment> \<open>γ · foldr rest const is a loop starting at x₀ with k' pieces → ∈ H by IH.\<close>
  \<comment> \<open>[foldr ps const] = [g₀] · [γ · foldr rest const] ∈ H (subgroup).\<close>
  \<comment> \<open>g₀ = p · γ⁻¹ is a loop at x₀ in Sp.\<close>
  let ?g0 = "top1_path_product p (top1_path_reverse \<gamma>)"
  have hg0_loop: "top1_is_loop_on Sp (subspace_topology X TX Sp) x0 ?g0"
  proof -
    have hSp_sub: "Sp \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
    have hTSp: "is_topology_on Sp (subspace_topology X TX Sp)"
      by (rule subspace_topology_is_topology_on[OF hTX hSp_sub])
    \<comment> \<open>p is a path in Sp from x₀ to p(1).\<close>
    have hp_in_Sp_all: "\<forall>s\<in>I_set. p s \<in> Sp"
      using hp_in_Sp unfolding top1_unit_interval_def by (by100 auto)
    have hp_Sp: "top1_is_path_on Sp (subspace_topology X TX Sp) x0 (p 1) p"
      using continuous_map_restrict_codomain[OF hp_cont hp_in_Sp_all hSp_sub]
            hp0 unfolding top1_is_path_on_def by (by100 blast)
    \<comment> \<open>γ maps into Sp∩S1 ⊆ Sp. Lift to Sp.\<close>
    have h\<gamma>_Sp: "top1_is_path_on Sp (subspace_topology X TX Sp) x0 (p 1) \<gamma>"
    proof -
      have hSpS1_sub_Sp: "Sp \<inter> S1 \<subseteq> Sp" by (by100 blast)
      have hSpS1_sub_X: "Sp \<inter> S1 \<subseteq> X" using hSp_sub by (by100 blast)
      \<comment> \<open>γ maps into Sp∩S1. First lift to X, then restrict to Sp.\<close>
      have h\<gamma>_cont_SpS1: "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
          (subspace_topology X TX (Sp \<inter> S1)) \<gamma>"
        using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have h\<gamma>_in_Sp: "\<forall>s\<in>I_set. \<gamma> s \<in> Sp"
        using h\<gamma>_cont_SpS1 unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Lift γ from Sp∩S1 to X (via inclusion).\<close>
      have h\<gamma>_cont_X: "top1_continuous_map_on I_set I_top X TX \<gamma>"
      proof -
        have "\<forall>s\<in>I_set. \<gamma> s \<in> X" using h\<gamma>_in_Sp hSp_sub by (by100 blast)
        have h\<gamma>_cont_SpS1': "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
            (subspace_topology X TX (Sp \<inter> S1)) \<gamma>" by (rule h\<gamma>_cont_SpS1)
        show ?thesis
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set" thus "\<gamma> s \<in> X" using \<open>\<forall>s\<in>I_set. \<gamma> s \<in> X\<close> by (by100 blast)
        next
          fix V assume "V \<in> TX"
          have "(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)"
            using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
          have heq: "{s \<in> I_set. \<gamma> s \<in> V} = {s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V}"
          proof (rule Collect_cong)
            fix s show "(s \<in> I_set \<and> \<gamma> s \<in> V) = (s \<in> I_set \<and> \<gamma> s \<in> (Sp \<inter> S1) \<inter> V)"
              using h\<gamma>_cont_SpS1 unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "{s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V} \<in> I_top"
            using h\<gamma>_cont_SpS1 \<open>(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<gamma> s \<in> V} \<in> I_top" using heq by (by100 simp)
        qed
      qed
      \<comment> \<open>Restrict from X to Sp.\<close>
      have h\<gamma>_cont_Sp: "top1_continuous_map_on I_set I_top Sp (subspace_topology X TX Sp) \<gamma>"
        by (rule continuous_map_restrict_codomain[OF h\<gamma>_cont_X h\<gamma>_in_Sp hSp_sub])
      have h\<gamma>0: "\<gamma> 0 = x0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have h\<gamma>1: "\<gamma> 1 = p 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      thus ?thesis using h\<gamma>_cont_Sp h\<gamma>0 h\<gamma>1 unfolding top1_is_path_on_def by (by100 blast)
    qed
    \<comment> \<open>γ⁻¹ is a path in Sp from p(1) to x₀.\<close>
    have h\<gamma>rev_Sp: "top1_is_path_on Sp (subspace_topology X TX Sp) (p 1) x0 (top1_path_reverse \<gamma>)"
      by (rule top1_path_reverse_is_path[OF h\<gamma>_Sp])
    \<comment> \<open>p · γ⁻¹ is a path in Sp from x₀ to x₀.\<close>
    have "top1_is_path_on Sp (subspace_topology X TX Sp) x0 x0 ?g0"
      by (rule top1_path_product_is_path[OF hTSp hp_Sp h\<gamma>rev_Sp])
    thus ?thesis unfolding top1_is_loop_on_def .
  qed
  have hg0_in_H: "{g. top1_loop_equiv_on X TX x0 ?g0 g} \<in> H"
    using hg0_loop hSp_UV hU_in_H hV_in_H by (by100 blast)
  \<comment> \<open>γ · foldr rest const: product of k' pieces starting at x₀.\<close>
  \<comment> \<open>The first piece is γ · rest!0 (maps to S1), remaining pieces are rest[1..].\<close>
  \<comment> \<open>By IH: [γ · foldr rest const] ∈ H.\<close>
  have hgamma_rest_in_H: "{g. top1_loop_equiv_on X TX x0
      (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0))) g} \<in> H"
  proof -
    \<comment> \<open>Construct new pieces: new_ps = (γ · rest!0) # drop 1 rest.\<close>
    let ?r0 = "rest ! 0"
    let ?new_first = "top1_path_product \<gamma> ?r0"
    let ?new_ps = "?new_first # (drop 1 rest)"
    \<comment> \<open>Apply IH to new_ps.\<close>
    have hlen_new: "length ?new_ps = k'"
      using hrest_len hk' by (by100 simp)
    \<comment> \<open>Verify IH conditions for new_ps.\<close>
    \<comment> \<open>Key fact: for i>0, new_ps!i = rest!i (via nth_Cons_Suc + nth_drop).\<close>
    have hnew_rest: "\<And>i. 0 < i \<and> i < k' \<Longrightarrow> ?new_ps!i = rest!i"
    proof -
      fix i assume hi: "0 < i \<and> i < k'"
      have "?new_ps!i = (drop 1 rest)!(i-1)" using hi by (by100 simp)
      also have "\<dots> = rest!(1 + (i-1))"
        by (rule nth_drop) (use hrest_len hk' in \<open>by100 linarith\<close>)
      also have "1 + (i - 1) = i" using hi by (by100 linarith)
      finally show "?new_ps!i = rest!i" .
    qed
    \<comment> \<open>rest!i = ps!(Suc i) for i < k'.\<close>
    have hrest_ps: "\<And>i. i < k' \<Longrightarrow> rest!i = ps!(Suc i)"
      using hps_eq by (by100 simp)
    \<comment> \<open>S1 = U or V. γ maps to Sp∩S1 ⊆ S1. r0 maps to S1.\<close>
    have h\<gamma>_in_S1: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> \<gamma> t \<in> S1"
    proof -
      have "\<forall>s\<in>I_set. \<gamma> s \<in> Sp \<inter> S1"
        using h\<gamma> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus ?thesis unfolding top1_unit_interval_def by (by100 auto)
    qed
    have hr0_in_S1: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> ?r0 t \<in> S1"
      unfolding S1_def using Suc.prems(2)[of 1] hps_eq hk' by (by100 auto)
    have hnew_UV: "\<And>i. i < k' \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?new_ps!i) t \<in> U)
                                  \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?new_ps!i) t \<in> V)"
    proof -
      fix i assume hi: "i < k'"
      show "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?new_ps!i) t \<in> U)
            \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?new_ps!i) t \<in> V)"
      proof (cases "i = 0")
        case True
        \<comment> \<open>new_ps!0 = γ·r0 maps to S1 ∈ {U,V}.\<close>
        have "?new_ps!0 = ?new_first" by (by100 simp)
        have "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> ?new_first t \<in> S1"
        proof (intro allI impI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          show "?new_first t \<in> S1"
            unfolding top1_path_product_def
            using h\<gamma>_in_S1 hr0_in_S1 ht by (by100 auto)
        qed
        from hS1_UV show ?thesis using True \<open>?new_ps!0 = ?new_first\<close> \<open>\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> ?new_first t \<in> S1\<close>
          by (by100 auto)
      next
        case False
        hence "?new_ps!i = rest!i" using hnew_rest hi by (by100 blast)
        also have "rest!i = ps!(Suc i)" using hrest_ps hi by (by100 blast)
        finally have "?new_ps!i = ps!(Suc i)" .
        have "Suc i < Suc k'" using hi by (by100 linarith)
        thus ?thesis using Suc.prems(2)[OF \<open>Suc i < Suc k'\<close>] hps_eq \<open>?new_ps!i = ps!(Suc i)\<close>
          by (by100 simp)
      qed
    qed
    have hnew_cont: "\<And>i. i < k' \<Longrightarrow> top1_continuous_map_on I_set I_top X TX (?new_ps!i)"
    proof -
      fix i assume hi: "i < k'"
      show "top1_continuous_map_on I_set I_top X TX (?new_ps!i)"
      proof (cases "i = 0")
        case True
        have h\<gamma>_cont_X: "top1_continuous_map_on I_set I_top X TX \<gamma>"
        proof -
          have hSpS1_sub_X: "Sp \<inter> S1 \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
          have h\<gamma>_cont_SpS1: "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
              (subspace_topology X TX (Sp \<inter> S1)) \<gamma>"
            using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
          have "\<forall>s\<in>I_set. \<gamma> s \<in> X"
            using h\<gamma>_cont_SpS1 hSpS1_sub_X unfolding top1_continuous_map_on_def by (by100 blast)
          show ?thesis unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set" thus "\<gamma> s \<in> X" using \<open>\<forall>s\<in>I_set. \<gamma> s \<in> X\<close> by (by100 blast)
          next
            fix V assume "V \<in> TX"
            have "(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)"
              using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
            have heq: "{s \<in> I_set. \<gamma> s \<in> V} = {s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V}"
            proof (rule Collect_cong)
              fix s show "(s \<in> I_set \<and> \<gamma> s \<in> V) = (s \<in> I_set \<and> \<gamma> s \<in> (Sp \<inter> S1) \<inter> V)"
                using h\<gamma>_cont_SpS1 unfolding top1_continuous_map_on_def by (by100 blast)
            qed
            have "{s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V} \<in> I_top"
              using h\<gamma>_cont_SpS1 \<open>(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)\<close>
              unfolding top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<gamma> s \<in> V} \<in> I_top" using heq by (by100 simp)
          qed
        qed
        have hr0_cont_X: "top1_continuous_map_on I_set I_top X TX ?r0"
          using Suc.prems(3)[of 1] hps_eq hk' by (by100 auto)
        have "\<gamma> 1 = p 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have h\<gamma>1_r0_0: "\<gamma> 1 = ?r0 0" using \<open>\<gamma> 1 = p 1\<close> hp1_eq by (by100 simp)
        show ?thesis using True
          top1_path_product_continuous[OF hTX h\<gamma>_cont_X hr0_cont_X h\<gamma>1_r0_0] by (by100 simp)
      next
        case False
        hence "?new_ps!i = rest!i" using hnew_rest hi by (by100 blast)
        also have "rest!i = ps!(Suc i)" using hrest_ps hi by (by100 blast)
        finally have "?new_ps!i = ps!(Suc i)" .
        have "Suc i < Suc k'" using hi by (by100 linarith)
        thus ?thesis using Suc.prems(3)[OF \<open>Suc i < Suc k'\<close>] hps_eq \<open>?new_ps!i = ps!(Suc i)\<close>
          by (by100 simp)
      qed
    qed
    have hnew_endpts: "\<And>i. i < k' \<Longrightarrow> (?new_ps!i) 0 = (if i = 0 then x0 else (?new_ps!(i-1)) 1)"
    proof -
      fix i assume hi: "i < k'"
      show "(?new_ps!i) 0 = (if i = 0 then x0 else (?new_ps!(i-1)) 1)"
      proof (cases "i = 0")
        case True
        have "(?new_ps!0) 0 = ?new_first 0" by (by100 simp)
        also have "\<dots> = \<gamma> 0" unfolding top1_path_product_def by (by100 simp)
        also have "\<dots> = x0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        finally show ?thesis using True by (by100 simp)
      next
        case False hence hi0: "0 < i" by (by100 linarith)
        have "?new_ps!i = rest!i" using hnew_rest hi hi0 by (by100 blast)
        have "rest!i = ps!(Suc i)" using hrest_ps hi by (by100 blast)
        \<comment> \<open>ps!(Suc i) starts at ps!i's end = rest!(i-1)'s end.\<close>
        have "Suc i < Suc k'" using hi by (by100 linarith)
        have "(ps!(Suc i)) 0 = (ps!i) 1"
          using Suc.prems(4)[OF \<open>Suc i < Suc k'\<close>] False by (by100 auto)
        hence "(rest!i) 0 = (ps!i) 1" using \<open>rest!i = ps!(Suc i)\<close> by (by100 simp)
        \<comment> \<open>ps!i = rest!(i-1) for i ≥ 1, so (ps!i) 1 = rest!(i-1) 1.\<close>
        have "i \<ge> 1" using hi0 by (by100 linarith)
        have "ps!i = rest!(i-1)" using hps_eq \<open>i \<ge> 1\<close> by (by100 simp)
        hence "(ps!i) 1 = (rest!(i-1)) 1" by (by100 simp)
        \<comment> \<open>For i ≥ 2: new_ps!(i-1) = rest!(i-1), so end matches.
           For i = 1: new_ps!0 = γ·r0, end = r0(1) = rest!0(1) = (ps!1)(1) = (rest!0)(1).\<close>
        show ?thesis
        proof (cases "i = 1")
          case True
          have "(?new_ps!0) 1 = ?new_first 1" by (by100 simp)
          also have "\<dots> = ?r0 1" unfolding top1_path_product_def by (by100 simp)
          finally show ?thesis using True \<open>(rest!i) 0 = (ps!i) 1\<close> \<open>(ps!i) 1 = (rest!(i-1)) 1\<close>
            \<open>?new_ps!i = rest!i\<close> by (by100 simp)
        next
          case False hence "i \<ge> 2" using hi0 by (by100 linarith)
          hence "i - 1 > 0" by (by100 linarith)
          have "0 < i - 1 \<and> i - 1 < k'" using \<open>i - 1 > 0\<close> hi by (by100 linarith)
          have "?new_ps!(i-1) = rest!(i-1)" using hnew_rest[OF \<open>0 < i - 1 \<and> i - 1 < k'\<close>] by (by100 blast)
          have "(?new_ps!i) 0 = (rest!i) 0" using \<open>?new_ps!i = rest!i\<close> by (by100 simp)
          also have "\<dots> = (ps!i) 1" using \<open>(rest!i) 0 = (ps!i) 1\<close> .
          also have "\<dots> = (rest!(i-1)) 1" using \<open>(ps!i) 1 = (rest!(i-1)) 1\<close> .
          also have "\<dots> = (?new_ps!(i-1)) 1" using \<open>?new_ps!(i-1) = rest!(i-1)\<close> by (by100 simp)
          finally show ?thesis using hi0 by (by100 simp)
        qed
      qed
    qed
    have hnew_end: "(?new_ps!(k'-1)) 1 = x0"
    proof (cases "k' = 1")
      case True
      have "?new_ps!0 = ?new_first" by (by100 simp)
      have "?new_first 1 = ?r0 1" unfolding top1_path_product_def by (by100 simp)
      have "?r0 1 = (ps!1) 1" using hrest_ps hk' by (by100 auto)
      have hpsk'_end: "(ps!k') 1 = x0" using Suc.prems(5) Suc.hyps by (by100 simp)
      have "(ps!1) 1 = x0" using hpsk'_end True Suc.hyps by (by100 simp)
      thus ?thesis using True \<open>?new_ps!0 = ?new_first\<close> \<open>?new_first 1 = ?r0 1\<close> \<open>?r0 1 = (ps!1) 1\<close>
        by (by100 simp)
    next
      case False hence "k' \<ge> 2" using hk' by (by100 linarith)
      hence "k' - 1 > 0" by (by100 linarith)
      have "0 < k' - 1 \<and> k' - 1 < k'" using \<open>k' - 1 > 0\<close> hk' by (by100 linarith)
      have "?new_ps!(k'-1) = rest!(k'-1)" using hnew_rest[OF \<open>0 < k' - 1 \<and> k' - 1 < k'\<close>] by (by100 blast)
      have "rest!(k'-1) = ps!k'" using hrest_ps hk' by (by100 auto)
      have hpsk'_end: "(ps!k') 1 = x0" using Suc.prems(5) Suc.hyps by (by100 simp)
      thus ?thesis using \<open>?new_ps!(k'-1) = rest!(k'-1)\<close> \<open>rest!(k'-1) = ps!k'\<close> by (by100 simp)
    qed
    have hIH_result: "{g. top1_loop_equiv_on X TX x0
        (foldr top1_path_product ?new_ps (top1_constant_path x0)) g} \<in> H"
      by (rule Suc.IH[OF hlen_new hnew_UV hnew_cont hnew_endpts hnew_end])
    \<comment> \<open>foldr new_ps const = pp (γ·r0) (foldr (drop 1 rest) const).
       By Thm 51.2 associativity: ~ pp γ (pp r0 (foldr (drop 1 rest) const))
                                  = pp γ (foldr rest const).\<close>
    have hfoldr_assoc: "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product ?new_ps (top1_constant_path x0))
        (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0)))"
    proof -
      \<comment> \<open>foldr (new_first # drop 1 rest) const = pp new_first (foldr (drop 1 rest) const).\<close>
      have hfoldr_expand: "foldr top1_path_product ?new_ps (top1_constant_path x0)
          = top1_path_product ?new_first (foldr top1_path_product (drop 1 rest) (top1_constant_path x0))"
        by (by100 simp)
      \<comment> \<open>rest = r0 # drop 1 rest (since rest has k' ≥ 1 elements).\<close>
      have hrest_cons: "rest = ?r0 # (drop 1 rest)"
        using hrest_len hk' by (cases rest) (by100 auto)+
      have hfoldr_rest: "foldr top1_path_product rest (top1_constant_path x0)
          = top1_path_product ?r0 (foldr top1_path_product (drop 1 rest) (top1_constant_path x0))"
      proof -
        have "foldr top1_path_product (?r0 # drop 1 rest) (top1_constant_path x0)
            = top1_path_product ?r0 (foldr top1_path_product (drop 1 rest) (top1_constant_path x0))"
          by (by100 simp)
        thus ?thesis using hrest_cons by (by100 simp)
      qed
      \<comment> \<open>Need: pp (pp γ r0) tail' ~ pp γ (pp r0 tail') where tail' = foldr(drop 1 rest, const).\<close>
      let ?tail' = "foldr top1_path_product (drop 1 rest) (top1_constant_path x0)"
      \<comment> \<open>Get paths in X for associativity.\<close>
      have hSp_sub': "Sp \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
      have hSpS1_sub_X: "Sp \<inter> S1 \<subseteq> X" using hSp_sub' by (by100 blast)
      have h\<gamma>_X_path: "top1_is_path_on X TX x0 (p 1) \<gamma>"
      proof -
        have h\<gamma>_cont_SpS1': "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
            (subspace_topology X TX (Sp \<inter> S1)) \<gamma>"
          using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have "\<forall>s\<in>I_set. \<gamma> s \<in> X"
          using h\<gamma>_cont_SpS1' hSpS1_sub_X unfolding top1_continuous_map_on_def by (by100 blast)
        have h\<gamma>_cont_X': "top1_continuous_map_on I_set I_top X TX \<gamma>"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set" thus "\<gamma> s \<in> X" using \<open>\<forall>s\<in>I_set. \<gamma> s \<in> X\<close> by (by100 blast)
        next
          fix V assume "V \<in> TX"
          have "(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)"
            using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
          have heq: "{s \<in> I_set. \<gamma> s \<in> V} = {s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V}"
          proof (rule Collect_cong)
            fix s show "(s \<in> I_set \<and> \<gamma> s \<in> V) = (s \<in> I_set \<and> \<gamma> s \<in> (Sp \<inter> S1) \<inter> V)"
              using h\<gamma>_cont_SpS1' unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "{s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V} \<in> I_top"
            using h\<gamma>_cont_SpS1' \<open>(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<gamma> s \<in> V} \<in> I_top" using heq by (by100 simp)
        qed
        have "\<gamma> 0 = x0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have "\<gamma> 1 = p 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        show ?thesis using h\<gamma>_cont_X' \<open>\<gamma> 0 = x0\<close> \<open>\<gamma> 1 = p 1\<close> unfolding top1_is_path_on_def by (by100 blast)
      qed
      have hr0_X_path: "top1_is_path_on X TX (p 1) (?r0 1) ?r0"
      proof -
        have "1 < Suc k'" using hk' by (by100 linarith)
        have hr0_cont: "top1_continuous_map_on I_set I_top X TX ?r0"
          using Suc.prems(3)[OF \<open>1 < Suc k'\<close>] hps_eq by (by100 simp)
        have "?r0 0 = p 1" using hp1_eq by (by100 simp)
        show ?thesis using hr0_cont \<open>?r0 0 = p 1\<close> unfolding top1_is_path_on_def by (by100 blast)
      qed
      have htail'_X_path: "top1_is_path_on X TX (?r0 1) x0 ?tail'"
      proof -
        let ?tl = "drop 1 rest"
        have htl_def: "rest = ?r0 # ?tl" using hrest_cons by (by100 blast)
        have htl_len: "length ?tl = k' - 1" using hrest_len hk' by (by100 simp)
        \<comment> \<open>Define endpoint sequence for foldr_path_product_is_path.\<close>
        define c where "c i = (if i = 0 then ?r0 1
            else if i + 1 < k' then (rest!(i)) 1 else x0)" for i
        \<comment> \<open>Each ?tl!i is a path in X from c(i) to c(i+1).\<close>
        have htl_paths: "\<And>i. i < length ?tl \<Longrightarrow>
            top1_is_path_on X TX (c i) (c (Suc i)) (?tl!i)"
        proof -
          fix i assume hi: "i < length ?tl"
          hence hi': "i < k' - 1" using htl_len by (by100 simp)
          \<comment> \<open>?tl!i = rest!(Suc i) via Cons decomposition.\<close>
          have htl_i: "?tl!i = rest!(Suc i)"
          proof -
            have "rest!(Suc i) = (?r0 # ?tl)!(Suc i)" using htl_def by (by100 simp)
            also have "\<dots> = ?tl!i" by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have "Suc (Suc i) < Suc k'" using hi' by (by100 linarith)
          have htl_cont: "top1_continuous_map_on I_set I_top X TX (?tl!i)"
            using Suc.prems(3)[OF \<open>Suc (Suc i) < Suc k'\<close>] hps_eq htl_i by (by100 simp)
          \<comment> \<open>Start point: (rest!(Suc i)) 0 = (rest!i) 1 = c(i).\<close>
          have "(ps!(Suc (Suc i))) 0 = (ps!(Suc i)) 1"
            using Suc.prems(4)[OF \<open>Suc (Suc i) < Suc k'\<close>] by (by100 auto)
          hence hstart: "(?tl!i) 0 = (rest!i) 1"
            using htl_i hps_eq by (by100 simp)
          have hstart_c: "(?tl!i) 0 = c i"
          proof (cases "i = 0")
            case True thus ?thesis using hstart c_def by (by100 simp)
          next
            case False hence "i \<ge> 1" by (by100 linarith)
            show ?thesis using hstart c_def hi' \<open>i \<ge> 1\<close> by (by100 auto)
          qed
          \<comment> \<open>End point: (?tl!i) 1 = c(Suc i).\<close>
          have hend_c: "(?tl!i) 1 = c (Suc i)"
          proof (cases "Suc i + 1 < k'")
            case True thus ?thesis using c_def htl_i by (by100 auto)
          next
            case False
            hence "i = k' - 2" using hi' by (by100 linarith)
            hence "k' \<ge> 2" using hi' by (by100 linarith)
            hence "Suc i = k' - 1" using \<open>i = k' - 2\<close> \<open>k' \<ge> 2\<close> by (by100 linarith)
            have "c (k' - 1) = x0"
            proof -
              have "k' - 1 \<noteq> 0" using \<open>k' \<ge> 2\<close> by (by100 linarith)
              have "k' - 1 + 1 < k' \<or> k' - 1 + 1 \<ge> k'" by (by100 linarith)
              thus ?thesis
              proof
                assume "k' - 1 + 1 < k'"
                hence False using hk' by (by100 linarith)
                thus ?thesis ..
              next
                assume "k' - 1 + 1 \<ge> k'"
                thus ?thesis using c_def \<open>k' - 1 \<noteq> 0\<close> by (by100 auto)
              qed
            qed
            moreover have "(?tl!i) 1 = (rest!(k'-1)) 1" using htl_i \<open>Suc i = k' - 1\<close> by (by100 simp)
            moreover have "(rest!(k'-1)) 1 = x0"
            proof -
              have "ps!k' = rest!(k'-1)" using hps_eq hk' by (by100 auto)
              have "(ps!k') 1 = x0" using Suc.prems(5) Suc.hyps by (by100 simp)
              thus ?thesis using \<open>ps!k' = rest!(k'-1)\<close> by (by100 simp)
            qed
            ultimately show ?thesis using \<open>Suc i = k' - 1\<close> by (by100 simp)
          qed
          show "top1_is_path_on X TX (c i) (c (Suc i)) (?tl!i)"
            using htl_cont hstart_c hend_c unfolding top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>Base: const x0 is a path from c(length ?tl) to x0.\<close>
        have hbase: "top1_is_path_on X TX (c (length ?tl)) x0 (top1_constant_path x0)"
        proof -
          have "c (k' - 1) = x0"
          proof (cases "k' = 1")
            case True
            hence "k' - 1 = 0" by (by100 simp)
            have "?r0 1 = x0"
            proof -
              have "ps!1 = rest!0" using hps_eq by (by100 simp)
              hence "ps!k' = rest!0" using True Suc.hyps by (by100 simp)
              have "(ps!k') 1 = x0" using Suc.prems(5) Suc.hyps by (by100 simp)
              thus ?thesis using \<open>ps!k' = rest!0\<close> True Suc.hyps by (by100 simp)
            qed
            thus ?thesis using c_def True by (by100 simp)
          next
            case False hence "k' \<ge> 2" using hk' by (by100 linarith)
            \<comment> \<open>c(k'-1) = x0 directly from c_def since k'-1 ≠ 0 and k'-1+1 = k' ≮ k'.\<close>
            have "k' - 1 \<noteq> 0" using \<open>k' \<ge> 2\<close> by (by100 linarith)
            have "\<not> (k' - 1 + 1 < k')" by (by100 linarith)
            show ?thesis using c_def \<open>k' - 1 \<noteq> 0\<close> \<open>\<not> (k' - 1 + 1 < k')\<close> by (by100 auto)
          qed
          have "x0 \<in> X" using hx0 hUsub by (by100 blast)
          have "c (length ?tl) = x0" using htl_len \<open>c (k'-1) = x0\<close> by (by100 simp)
          have "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
            by (rule top1_constant_path_is_path[OF hTX \<open>x0 \<in> X\<close>])
          show ?thesis using \<open>c (length ?tl) = x0\<close> \<open>top1_is_path_on X TX x0 x0 (top1_constant_path x0)\<close>
            by (by100 simp)
        qed
        have "c 0 = ?r0 1" using c_def by (by100 simp)
        have "top1_is_path_on X TX (c 0) x0 ?tail'"
          by (rule foldr_path_product_is_path[OF hTX htl_paths hbase])
        thus ?thesis using \<open>c 0 = ?r0 1\<close> by (by100 simp)
      qed
      \<comment> \<open>Apply Thm 51.2 associativity (reversed): pp (pp γ r0) tail' ~ pp γ (pp r0 tail').\<close>
      have hassoc: "top1_path_homotopic_on X TX x0 x0
          (top1_path_product \<gamma> (top1_path_product ?r0 ?tail'))
          (top1_path_product (top1_path_product \<gamma> ?r0) ?tail')"
        by (rule Theorem_51_2_associativity[OF hTX h\<gamma>_X_path hr0_X_path htail'_X_path])
      have hassoc_sym: "top1_path_homotopic_on X TX x0 x0
          (top1_path_product (top1_path_product \<gamma> ?r0) ?tail')
          (top1_path_product \<gamma> (top1_path_product ?r0 ?tail'))"
        by (rule Lemma_51_1_path_homotopic_sym[OF hassoc])
      show ?thesis using hassoc_sym hfoldr_expand hfoldr_rest by (by100 simp)
    qed
    \<comment> \<open>Classes equal: [foldr new_ps const] = [pp γ (foldr rest const)].\<close>
    have "{g. top1_loop_equiv_on X TX x0 (foldr top1_path_product ?new_ps (top1_constant_path x0)) g}
        = {g. top1_loop_equiv_on X TX x0
            (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0))) g}"
    proof -
      have hle: "top1_loop_equiv_on X TX x0
          (foldr top1_path_product ?new_ps (top1_constant_path x0))
          (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0)))"
        using hfoldr_assoc
        unfolding top1_loop_equiv_on_def top1_is_loop_on_def top1_path_homotopic_on_def
        by (by100 blast)
      have hle_sym: "top1_loop_equiv_on X TX x0
          (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0)))
          (foldr top1_path_product ?new_ps (top1_constant_path x0))"
        by (rule top1_loop_equiv_on_sym[OF hle])
      show ?thesis
      proof (rule set_eqI)
        fix k show "k \<in> {g. top1_loop_equiv_on X TX x0 (foldr top1_path_product ?new_ps (top1_constant_path x0)) g}
            \<longleftrightarrow> k \<in> {g. top1_loop_equiv_on X TX x0
                (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0))) g}"
          using top1_loop_equiv_on_trans[OF hTX hle]
                top1_loop_equiv_on_trans[OF hTX hle_sym] by (by100 blast)
      qed
    qed
    thus ?thesis using hIH_result by (by100 simp)
  qed
  \<comment> \<open>Product [g₀]·[γ·rest] ∈ H (subgroup closure).\<close>
  have hH_mul_closed: "\<forall>a\<in>H. \<forall>b\<in>H. top1_fundamental_group_mul X TX x0 a b \<in> H"
  proof -
    from hH_grp show ?thesis unfolding top1_is_group_on_def by (elim conjE) (by100 assumption)
  qed
  have hprod_in_H: "top1_fundamental_group_mul X TX x0
      {g. top1_loop_equiv_on X TX x0 ?g0 g}
      {g. top1_loop_equiv_on X TX x0
        (top1_path_product \<gamma> (foldr top1_path_product rest (top1_constant_path x0))) g} \<in> H"
    using hH_mul_closed hg0_in_H hgamma_rest_in_H by (by100 blast)
  \<comment> \<open>[g₀]·[γ·rest] = [g₀ · γ · rest] = [(p·γ⁻¹)·(γ·rest)] = [p·rest] = [foldr ps const].\<close>
  \<comment> \<open>The group product [a]·[b] = [a·b] by fundamental group multiplication.\<close>
  \<comment> \<open>Key: [foldr (p#rest) const] = [pp p tail] = [pp g₀ (pp γ tail)] = [g₀]·[γ·tail] ∈ H.
     The middle equality uses: pp p tail ~ pp (pp p (rev γ)) (pp γ tail) = pp g₀ (pp γ tail)
     by inserting rev(γ)·γ ~ const and using associativity.\<close>
  let ?tail = "foldr top1_path_product rest (top1_constant_path x0)"
  have hfold_eq: "foldr top1_path_product ps (top1_constant_path x0)
      = top1_path_product p ?tail" using hps_eq by (by100 simp)
  \<comment> \<open>Shared fact: tail is a path in X from p(1) to x₀.\<close>
  have htail_X_outer: "top1_is_path_on X TX (p 1) x0 ?tail"
  proof -
    define a where "a i = (if i = 0 then p 1 else (rest!(i-1)) 1)" for i
    have hrest_paths: "\<And>i. i < k' \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (rest!i)"
    proof -
      fix i assume hi: "i < k'"
      have "Suc i < Suc k'" using hi by (by100 linarith)
      have hri_cont: "top1_continuous_map_on I_set I_top X TX (rest!i)"
        using Suc.prems(3)[OF \<open>Suc i < Suc k'\<close>] hps_eq by (by100 simp)
      have hri_start: "(rest!i) 0 = a i"
      proof (cases "i = 0")
        case True thus ?thesis using hp1_eq a_def by (by100 simp)
      next
        case False
        have "(ps!(Suc i)) 0 = (ps!i) 1" using Suc.prems(4)[OF \<open>Suc i < Suc k'\<close>] False by (by100 auto)
        thus ?thesis using hps_eq False a_def by (by100 auto)
      qed
      have hri_end: "(rest!i) 1 = a (Suc i)" using a_def by (by100 simp)
      show "top1_is_path_on X TX (a i) (a (Suc i)) (rest!i)"
        using hri_cont hri_start hri_end unfolding top1_is_path_on_def by (by100 blast)
    qed
    have "a k' = x0"
    proof -
      have "k' \<ge> 1" using hk' by (by100 blast)
      have "(ps!k') 1 = x0" using Suc.prems(5) Suc.hyps by (by100 simp)
      have "ps!k' = rest!(k'-1)" using hps_eq hk' by (by100 auto)
      thus ?thesis using a_def \<open>(ps!k') 1 = x0\<close> \<open>ps!k' = rest!(k'-1)\<close> hk' by (by100 auto)
    qed
    have "x0 \<in> X" using hx0 hUsub by (by100 blast)
    have hbase: "top1_is_path_on X TX (a (length rest)) x0 (top1_constant_path x0)"
      using hrest_len \<open>a k' = x0\<close> top1_constant_path_is_path[OF hTX \<open>x0 \<in> X\<close>]
      unfolding top1_is_path_on_def by (by100 blast)
    have hrest_paths': "\<And>i. i < length rest \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (rest!i)"
      using hrest_paths hrest_len by (by100 simp)
    have "a 0 = p 1" using a_def by (by100 simp)
    show ?thesis using foldr_path_product_is_path[OF hTX hrest_paths' hbase] \<open>a 0 = p 1\<close> by (by100 simp)
  qed
  \<comment> \<open>Show pp p tail ~ pp g₀ (pp γ tail) via Theorem 51.2.\<close>
  have htail_homotopy: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product p ?tail) (top1_path_product ?g0 (top1_path_product \<gamma> ?tail))"
  proof -
    have hSp_sub': "Sp \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
    have hSpS1_sub_X: "Sp \<inter> S1 \<subseteq> X" using hSp_sub' by (by100 blast)
    \<comment> \<open>Get paths in X.\<close>
    have hp_X: "top1_is_path_on X TX x0 (p 1) p"
      using hp_cont hp0 unfolding top1_is_path_on_def by (by100 blast)
    have h\<gamma>_X: "top1_is_path_on X TX x0 (p 1) \<gamma>"
    proof -
      have h\<gamma>_cont_SpS1: "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
          (subspace_topology X TX (Sp \<inter> S1)) \<gamma>"
        using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have "\<forall>s\<in>I_set. \<gamma> s \<in> X"
        using h\<gamma>_cont_SpS1 hSpS1_sub_X unfolding top1_continuous_map_on_def by (by100 blast)
      have h\<gamma>_cont_X: "top1_continuous_map_on I_set I_top X TX \<gamma>"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume "s \<in> I_set" thus "\<gamma> s \<in> X" using \<open>\<forall>s\<in>I_set. \<gamma> s \<in> X\<close> by (by100 blast)
      next
        fix V assume "V \<in> TX"
        have "(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)"
          using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
        have heq: "{s \<in> I_set. \<gamma> s \<in> V} = {s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V}"
        proof (rule Collect_cong)
          fix s show "(s \<in> I_set \<and> \<gamma> s \<in> V) = (s \<in> I_set \<and> \<gamma> s \<in> (Sp \<inter> S1) \<inter> V)"
            using h\<gamma>_cont_SpS1 unfolding top1_continuous_map_on_def by (by100 blast)
        qed
        have "{s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V} \<in> I_top"
          using h\<gamma>_cont_SpS1 \<open>(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)\<close>
          unfolding top1_continuous_map_on_def by (by100 blast)
        thus "{s \<in> I_set. \<gamma> s \<in> V} \<in> I_top" using heq by (by100 simp)
      qed
      have "\<gamma> 0 = x0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have "\<gamma> 1 = p 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      show ?thesis using h\<gamma>_cont_X \<open>\<gamma> 0 = x0\<close> \<open>\<gamma> 1 = p 1\<close> unfolding top1_is_path_on_def by (by100 blast)
    qed
    have hrev\<gamma>_X: "top1_is_path_on X TX (p 1) x0 (top1_path_reverse \<gamma>)"
      by (rule top1_path_reverse_is_path[OF h\<gamma>_X])
    have htail_X: "top1_is_path_on X TX (p 1) x0 ?tail" by (rule htail_X_outer)
    have hg0_X: "top1_is_path_on X TX x0 x0 ?g0"
      by (rule top1_path_product_is_path[OF hTX hp_X hrev\<gamma>_X])
    have h\<gamma>tail_X: "top1_is_path_on X TX x0 x0 (top1_path_product \<gamma> ?tail)"
      by (rule top1_path_product_is_path[OF hTX h\<gamma>_X htail_X])
    \<comment> \<open>Chain: pp g₀ (pp γ tail) ~ pp p (pp (rev γ) (pp γ tail)) [assoc reversed]
             ~ pp p (pp const tail) [rev γ · γ ~ const inside]
             ~ pp p tail [left identity inside]\<close>
    \<comment> \<open>Step 1: pp g₀ (pp γ tail) ~ pp p (pp (rev γ) (pp γ tail)) by associativity reversed.\<close>
    have hstep1: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product p (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail)))
        (top1_path_product ?g0 (top1_path_product \<gamma> ?tail))"
      by (rule Theorem_51_2_associativity[OF hTX hp_X hrev\<gamma>_X h\<gamma>tail_X])
    \<comment> \<open>Step 2: rev(γ) · γ ~ const(p(1)).\<close>
    have hstep2: "top1_path_homotopic_on X TX (p 1) (p 1)
        (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) (top1_constant_path (p 1))"
      by (rule Theorem_51_2_invgerse_right[OF hTX h\<gamma>_X])
    \<comment> \<open>Step 3: pp (rev γ · γ) tail ~ pp const tail by product congruence.\<close>
    \<comment> \<open>Step 4: pp const tail ~ tail by left identity.\<close>
    \<comment> \<open>Step 5: pp p (pp (rev γ) (pp γ tail)) ~ pp p tail by combining steps 2-4 inside.\<close>
    \<comment> \<open>Combine: pp p tail ~ pp p (pp (rev γ) (pp γ tail)) ~ pp g₀ (pp γ tail).\<close>
    \<comment> \<open>Step 3: pp (rev γ) (pp γ tail) ~ pp (pp (rev γ) γ) tail by associativity.\<close>
    have hrev\<gamma>\<gamma>tail: "top1_is_path_on X TX (p 1) x0 (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail))"
      by (rule top1_path_product_is_path[OF hTX hrev\<gamma>_X h\<gamma>tail_X])
    have hstep3: "top1_path_homotopic_on X TX (p 1) x0
        (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail))
        (top1_path_product (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) ?tail)"
      by (rule Theorem_51_2_associativity[OF hTX hrev\<gamma>_X h\<gamma>_X htail_X])
    \<comment> \<open>Step 4: pp (pp (rev γ) γ) tail ~ pp const tail by product_left with hstep2.\<close>
    have hstep4: "top1_path_homotopic_on X TX (p 1) x0
        (top1_path_product (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) ?tail)
        (top1_path_product (top1_constant_path (p 1)) ?tail)"
      by (rule path_homotopic_product_left[OF hTX hstep2 htail_X])
    \<comment> \<open>Step 5: pp const tail ~ tail by left identity.\<close>
    have hstep5: "top1_path_homotopic_on X TX (p 1) x0
        (top1_path_product (top1_constant_path (p 1)) ?tail) ?tail"
      by (rule Theorem_51_2_left_identity[OF hTX htail_X])
    \<comment> \<open>Chain: pp (rev γ) (pp γ tail) ~ tail via steps 3-5.\<close>
    have hchain45: "top1_path_homotopic_on X TX (p 1) x0
        (top1_path_product (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) ?tail) ?tail"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX hstep4 hstep5])
    have hchain345: "top1_path_homotopic_on X TX (p 1) x0
        (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail)) ?tail"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX hstep3 hchain45])
    \<comment> \<open>Step 6: pp p (pp (rev γ) (pp γ tail)) ~ pp p tail by product_right with chain.\<close>
    have hstep6: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product p (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail)))
        (top1_path_product p ?tail)"
      by (rule path_homotopic_product_right[OF hTX hchain345 hp_X])
    \<comment> \<open>Combine with hstep1 (reversed): pp p tail ~ pp g₀ (pp γ tail).\<close>
    have hstep1_sym: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product ?g0 (top1_path_product \<gamma> ?tail))
        (top1_path_product p (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail)))"
      by (rule Lemma_51_1_path_homotopic_sym[OF hstep1])
    have hstep6_sym: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product p ?tail)
        (top1_path_product p (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product \<gamma> ?tail)))"
      by (rule Lemma_51_1_path_homotopic_sym[OF hstep6])
    show ?thesis
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX hstep6_sym hstep1])
  qed
  \<comment> \<open>Convert to loop_equiv classes.\<close>
  have hclass_eq: "{g. top1_loop_equiv_on X TX x0 (top1_path_product p ?tail) g}
      = {g. top1_loop_equiv_on X TX x0 (top1_path_product ?g0 (top1_path_product \<gamma> ?tail)) g}"
  proof -
    have hle: "top1_loop_equiv_on X TX x0 (top1_path_product p ?tail)
        (top1_path_product ?g0 (top1_path_product \<gamma> ?tail))"
      using htail_homotopy
      unfolding top1_loop_equiv_on_def top1_is_loop_on_def top1_path_homotopic_on_def
      by (by100 blast)
    have hle_sym: "top1_loop_equiv_on X TX x0
        (top1_path_product ?g0 (top1_path_product \<gamma> ?tail)) (top1_path_product p ?tail)"
      by (rule top1_loop_equiv_on_sym[OF hle])
    show ?thesis
    proof (rule set_eqI)
      fix k show "k \<in> {g. top1_loop_equiv_on X TX x0 (top1_path_product p ?tail) g} \<longleftrightarrow>
          k \<in> {g. top1_loop_equiv_on X TX x0 (top1_path_product ?g0 (top1_path_product \<gamma> ?tail)) g}"
        using top1_loop_equiv_on_trans[OF hTX hle] top1_loop_equiv_on_trans[OF hTX hle_sym]
        by (by100 blast)
    qed
  qed
  \<comment> \<open>[pp g₀ (pp γ tail)] = [g₀] · [pp γ tail] (fundamental group multiplication).\<close>
  have hmul_class: "{g. top1_loop_equiv_on X TX x0 (top1_path_product ?g0 (top1_path_product \<gamma> ?tail)) g}
      = top1_fundamental_group_mul X TX x0
          {g. top1_loop_equiv_on X TX x0 ?g0 g}
          {g. top1_loop_equiv_on X TX x0 (top1_path_product \<gamma> ?tail) g}"
  proof -
    have hSp_sub: "Sp \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
    have hg0_Xloop: "top1_is_loop_on X TX x0 ?g0"
    proof -
      have hg0_cont_Sp: "top1_continuous_map_on I_set I_top Sp (subspace_topology X TX Sp) ?g0"
        using hg0_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have "\<forall>s\<in>I_set. ?g0 s \<in> Sp"
        using hg0_cont_Sp unfolding top1_continuous_map_on_def by (by100 blast)
      hence "\<forall>s\<in>I_set. ?g0 s \<in> X" using hSp_sub by (by100 blast)
      have hg0_cont_X: "top1_continuous_map_on I_set I_top X TX ?g0"
      proof -
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set" thus "?g0 s \<in> X" using \<open>\<forall>s\<in>I_set. ?g0 s \<in> X\<close> by (by100 blast)
        next
          fix V assume "V \<in> TX"
          have "Sp \<inter> V \<in> subspace_topology X TX Sp" using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
          have heq: "{s \<in> I_set. ?g0 s \<in> V} = {s \<in> I_set. ?g0 s \<in> Sp \<inter> V}"
          proof (rule Collect_cong)
            fix s show "(s \<in> I_set \<and> ?g0 s \<in> V) = (s \<in> I_set \<and> ?g0 s \<in> Sp \<inter> V)"
              using \<open>\<forall>s\<in>I_set. ?g0 s \<in> Sp\<close> by (by100 blast)
          qed
          have "{s \<in> I_set. ?g0 s \<in> Sp \<inter> V} \<in> I_top"
            using hg0_cont_Sp \<open>Sp \<inter> V \<in> subspace_topology X TX Sp\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. ?g0 s \<in> V} \<in> I_top" using heq by (by100 simp)
        qed
      qed
      moreover have "?g0 0 = x0 \<and> ?g0 1 = x0"
        using hg0_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    qed
    have h\<gamma>tail_Xloop: "top1_is_loop_on X TX x0 (top1_path_product \<gamma> ?tail)"
    proof -
      have hSp_sub': "Sp \<subseteq> X" using hSp_UV hUsub hVsub by (by100 blast)
      have hSpS1_sub_X: "Sp \<inter> S1 \<subseteq> X" using hSp_sub' by (by100 blast)
      \<comment> \<open>γ is a path in X from x₀ to p(1).\<close>
      have h\<gamma>_cont_X: "top1_continuous_map_on I_set I_top X TX \<gamma>"
      proof -
        have h\<gamma>_cont_SpS1: "top1_continuous_map_on I_set I_top (Sp \<inter> S1)
            (subspace_topology X TX (Sp \<inter> S1)) \<gamma>"
          using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
        have "\<forall>s\<in>I_set. \<gamma> s \<in> X"
          using h\<gamma>_cont_SpS1 hSpS1_sub_X unfolding top1_continuous_map_on_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set" thus "\<gamma> s \<in> X" using \<open>\<forall>s\<in>I_set. \<gamma> s \<in> X\<close> by (by100 blast)
        next
          fix V assume "V \<in> TX"
          have "(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)"
            using \<open>V \<in> TX\<close> unfolding subspace_topology_def by (by100 blast)
          have heq: "{s \<in> I_set. \<gamma> s \<in> V} = {s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V}"
          proof (rule Collect_cong)
            fix s show "(s \<in> I_set \<and> \<gamma> s \<in> V) = (s \<in> I_set \<and> \<gamma> s \<in> (Sp \<inter> S1) \<inter> V)"
              using h\<gamma>_cont_SpS1 unfolding top1_continuous_map_on_def by (by100 blast)
          qed
          have "{s \<in> I_set. \<gamma> s \<in> (Sp \<inter> S1) \<inter> V} \<in> I_top"
            using h\<gamma>_cont_SpS1 \<open>(Sp \<inter> S1) \<inter> V \<in> subspace_topology X TX (Sp \<inter> S1)\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<gamma> s \<in> V} \<in> I_top" using heq by (by100 simp)
        qed
      qed
      have h\<gamma>0: "\<gamma> 0 = x0" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have h\<gamma>1: "\<gamma> 1 = p 1" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
      have h\<gamma>_X_path: "top1_is_path_on X TX x0 (p 1) \<gamma>"
        using h\<gamma>_cont_X h\<gamma>0 h\<gamma>1 unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>tail = foldr rest const is a path in X from p(1) to x₀.\<close>
      have htail_X_path: "top1_is_path_on X TX (p 1) x0 ?tail"
        by (rule htail_X_outer)
      show ?thesis using top1_path_product_is_path[OF hTX h\<gamma>_X_path htail_X_path]
        unfolding top1_is_loop_on_def by (by100 blast)
    qed
    show ?thesis
      using top1_fundamental_group_mul_class[OF hTX hg0_Xloop h\<gamma>tail_Xloop] by (by100 simp)
  qed
  show ?case using hfold_eq hclass_eq hmul_class hprod_in_H by (by100 simp)
qed

text \<open>Theorem 70.1 (Seifert-van Kampen, universal property):
  If X = U ∪ V with U, V, U∩V path-connected open, and φ₁: π₁(U) → H, φ₂: π₁(V) → H
  are homomorphisms compatible on U∩V (φ₁∘i₁ = φ₂∘i₂), then there exists a unique
  homomorphism Φ: π₁(X) → H extending φ₁ and φ₂.
  The proof constructs Φ via subdivision of loops into pieces in U or V.
  Well-definedness requires the 2D Lebesgue subdivision argument.\<close>
lemma Theorem_70_1_universal_property:
  assumes hTX: "is_topology_on_strict X TX" and hU: "openin_on X TX U" and hV: "openin_on X TX V"
      and hUV: "U \<union> V = X"
      and hUVpc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hUpc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hVpc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hx0: "x0 \<in> U \<inter> V"
      and hH: "top1_is_group_on H mulH eH invgH"
      and h\<phi>1: "top1_group_hom_on
          (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
          (top1_fundamental_group_mul U (subspace_topology X TX U) x0) H mulH \<phi>1"
      and h\<phi>2: "top1_group_hom_on
          (top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
          (top1_fundamental_group_mul V (subspace_topology X TX V) x0) H mulH \<phi>2"
      and hcompat: "\<forall>c\<in>top1_fundamental_group_carrier (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0.
          \<phi>1 (top1_fundamental_group_induced_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                U (subspace_topology X TX U) x0 (\<lambda>x. x) c)
        = \<phi>2 (top1_fundamental_group_induced_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                V (subspace_topology X TX V) x0 (\<lambda>x. x) c)"
  shows "\<exists>\<Phi>. top1_group_hom_on
          (top1_fundamental_group_carrier X TX x0)
          (top1_fundamental_group_mul X TX x0) H mulH \<Phi>
        \<and> (\<forall>a\<in>top1_fundamental_group_carrier U (subspace_topology X TX U) x0.
            \<Phi> (top1_fundamental_group_induced_on U (subspace_topology X TX U) x0 X TX x0 (\<lambda>x. x) a) = \<phi>1 a)
        \<and> (\<forall>b\<in>top1_fundamental_group_carrier V (subspace_topology X TX V) x0.
            \<Phi> (top1_fundamental_group_induced_on V (subspace_topology X TX V) x0 X TX x0 (\<lambda>x. x) b) = \<phi>2 b)"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  have hTopX: "is_topology_on X TX" using hTX unfolding is_topology_on_strict_def by (by100 blast)
  have hUsub: "U \<subseteq> X" using hU unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using hV unfolding openin_on_def by (by100 blast)
  have hx0_X: "x0 \<in> X" using hx0 hUsub by (by100 blast)
  have hx0_U: "x0 \<in> U" using hx0 by (by100 blast)
  have hx0_V: "x0 \<in> V" using hx0 by (by100 blast)
  \<comment> \<open>===== Construction of \<Phi> following Munkres §70 Theorem 70.1 =====\<close>
  have hTopU: "is_topology_on U ?TU" by (rule subspace_topology_is_topology_on[OF hTopX hUsub])
  have hTopV: "is_topology_on V ?TV" by (rule subspace_topology_is_topology_on[OF hTopX hVsub])
  have hUVsub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
  have hTopUV: "is_topology_on (U \<inter> V) ?TUV"
    by (rule subspace_topology_is_topology_on[OF hTopX hUVsub])
  \<comment> \<open>Step 1: Define \<rho> for loops f at x_0 in U or V.
     \<rho>(f) = \<phi>_1([f]_U) if \<forall>t\<in>I. f(t) \<in> U, else \<phi>_2([f]_V).
     Well-defined on U\<inter>V by compatibility.\<close>
  define \<rho> where "\<rho> f = (if (\<forall>s\<in>I_set. f s \<in> U)
      then \<phi>1 {g. top1_loop_equiv_on U ?TU x0 f g}
      else \<phi>2 {g. top1_loop_equiv_on V ?TV x0 f g})" for f
  \<comment> \<open>Step 2: Choose connecting paths \<alpha>_x from x_0 to x.
     For x = x_0: constant path. Otherwise: use path-connectedness.\<close>
  define \<alpha> where "\<alpha> x = (if x = x0 then top1_constant_path x0
      else if x \<in> U \<inter> V then SOME p. top1_is_path_on (U \<inter> V) ?TUV x0 x p
      else if x \<in> U then SOME p. top1_is_path_on U ?TU x0 x p
      else SOME p. top1_is_path_on V ?TV x0 x p)" for x
  \<comment> \<open>Step 3: Define \<sigma>(f) = \<rho>(\<alpha>_{f(0)} \<cdot> f \<cdot> rev(\<alpha>_{f(1)})) for paths f in U or V.\<close>
  define \<sigma> where "\<sigma> f = \<rho> (top1_path_product (\<alpha> (f 0)) (top1_path_product f (top1_path_reverse (\<alpha> (f 1)))))" for f
  \<comment> \<open>Step 4: Define \<tau>(f) for a loop f at x_0 in X.
     Pick SOME subdivision into U-or-V pieces, apply \<sigma> to each, multiply in H.
     The pieces are reparametrized sub-paths.\<close>
  define \<tau> where "\<tau> f = (
    let n = SOME n::nat. n \<ge> 1 \<and> (\<exists>sub. sub 0 = 0 \<and> sub n = 1
        \<and> (\<forall>i<n. sub i < sub (Suc i))
        \<and> (\<forall>i<n. (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> U)
               \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> V)));
        sub = SOME sub::nat\<Rightarrow>real. sub 0 = 0 \<and> sub n = 1
            \<and> (\<forall>i<n. sub i < sub (Suc i))
            \<and> (\<forall>i<n. (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> U)
                   \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> V));
        piece = (\<lambda>i t. f (sub i + t * (sub (Suc i) - sub i)))
    in foldr mulH (map (\<lambda>i. \<sigma> (piece i)) [0..<n]) eH)" for f
  \<comment> \<open>Step 5: Define \<Phi>([f]) = \<tau>(f) for a SOME representative f of the class.\<close>
  define \<Phi> where "\<Phi> c = \<tau> (SOME f. top1_is_loop_on X TX x0 f
      \<and> c = {g. top1_loop_equiv_on X TX x0 f g})" for c
  \<comment> \<open>===== Key property A: \<tau> well-defined under homotopy =====
     If f \<simeq> g (path homotopic in X, same endpoints), then \<tau>(f) = \<tau>(g).
     This is THE core 2D Lebesgue subdivision argument (Munkres Step 4).
     Given homotopy F: I\<times>I \<rightarrow> X, subdivide I\<times>I into grid with each cell in U or V.
     For adjacent rows: the cell homotopy gives \<sigma>-value equality via \<rho> compatibility.
     Telescoping across rows gives \<tau>(f) = \<tau>(g).\<close>
  have h\<tau>_wd: "\<And>f g. top1_is_loop_on X TX x0 f \<Longrightarrow> top1_is_loop_on X TX x0 g
      \<Longrightarrow> top1_path_homotopic_on X TX x0 x0 f g \<Longrightarrow> \<tau> f = \<tau> g"
  proof -
    fix f g assume hf: "top1_is_loop_on X TX x0 f" and hg: "top1_is_loop_on X TX x0 g"
        and hfg: "top1_path_homotopic_on X TX x0 x0 f g"
    \<comment> \<open>Step 1: Extract the homotopy F: I\<times>I \<rightarrow> X.\<close>
    obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
        and hF_s0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF_s1: "\<forall>s\<in>I_set. F (s, 1) = g s"
        and hF_0t: "\<forall>t\<in>I_set. F (0, t) = x0" and hF_1t: "\<forall>t\<in>I_set. F (1, t) = x0"
    proof -
      note hfg_raw = hfg[unfolded top1_path_homotopic_on_def]
      then obtain F where "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
          "(\<forall>s\<in>I_set. F (s, 0) = f s)" "(\<forall>s\<in>I_set. F (s, 1) = g s)"
          "(\<forall>t\<in>I_set. F (0, t) = x0)" "(\<forall>t\<in>I_set. F (1, t) = x0)"
        by (by100 fast)
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Step 2: F\<inverse>(U) and F\<inverse>(V) cover I\<times>I. Build per-row s-subdivisions, merge into grid.\<close>
    have hF_UV: "\<forall>p\<in>I_set \<times> I_set. F p \<in> U \<or> F p \<in> V"
    proof
      fix p assume "p \<in> I_set \<times> I_set"
      hence "F p \<in> X" using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
      thus "F p \<in> U \<or> F p \<in> V" using hUV by (by100 blast)
    qed
    \<comment> \<open>Step 3: 2D Lebesgue subdivision. Each cell maps into U or V.
       Use open_cover_subdivision_01 for the s-direction per each t-strip,
       then grid_from_per_piece_subdivisions to merge.\<close>
    \<comment> \<open>Step 4: For adjacent rows f_j and f_{j+1}, show \<tau>(f_j) = \<tau>(f_{j+1}).
       Key: each cell gives a (non-path) homotopy between pieces.
       By broken-line argument in the convex cell: piece_i \<cdot> \<beta>_i \<simeq> \<beta>_{i-1} \<cdot> piece'_i.
       This gives \<sigma>(piece_i) \<cdot> \<sigma>(\<beta>_i) = \<sigma>(\<beta>_{i-1}) \<cdot> \<sigma>(piece'_i).
       Telescoping + \<sigma>(\<beta>_0) = \<sigma>(\<beta>_n) = eH gives \<tau>(f_j) = \<tau>(f_{j+1}).\<close>
    \<comment> \<open>Step 5: Transitivity: \<tau>(f) = \<tau>(f_0) = ... = \<tau>(f_m) = \<tau>(g).\<close>
    \<comment> \<open>Step 3: Build the 2D grid. For each fixed t, the function s \<mapsto> F(s,t) maps [0,1]
       into X = U \<union> V. By open_cover_subdivision_01, subdivide [0,1] into intervals
       each mapping into U or V. Then grid_from_per_piece_subdivisions merges these
       into a uniform s-subdivision valid for all t-rows.\<close>
    \<comment> \<open>Step 3a: For each fixed t \<in> [0,1], get an s-subdivision.\<close>
    have hU_TX: "U \<in> TX" using hU unfolding openin_on_def by (by100 blast)
    have hV_TX: "V \<in> TX" using hV unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Step 3b: Get s-subdivision (using existing surjectivity proof machinery).
       Then merge into uniform t-subdivision via grid_from_per_piece_subdivisions.\<close>
    \<comment> \<open>Step 4: Row comparison. Define f_j(s) = F(s, t_j). Show \<tau>(f_{j-1}) = \<tau>(f_j) for
       adjacent rows. Each cell [s_{i-1},s_i]\<times>[t_{j-1},t_j] maps into U or V.
       The boundary paths \<beta>_i(t) = F(s_i, t) satisfy:
         piece_i \<cdot> \<beta>_i \<simeq> \<beta>_{i-1} \<cdot> piece'_i in U or V
       This gives \<sigma>(piece_i)\<cdot>\<sigma>(\<beta>_i) = \<sigma>(\<beta>_{i-1})\<cdot>\<sigma>(piece'_i) in H.
       Telescoping: \<Pi> \<sigma>(piece_i) = \<Pi> \<sigma>(piece'_i), i.e., \<tau>(f_{j-1}) = \<tau>(f_j).\<close>
    \<comment> \<open>Step 5: f_0 = f and f_m = g. By transitivity: \<tau>(f) = \<tau>(f_0) = ... = \<tau>(f_m) = \<tau>(g).\<close>
    \<comment> \<open>===== 2D GRID CONSTRUCTION =====\<close>
    \<comment> \<open>Step 3a: Get s-subdivision for f = F(\<cdot>,0). Same as surjectivity proof.\<close>
    have hf_cont_I: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    obtain ns sub_s where hns: "ns \<ge> 1" and hs0: "sub_s 0 = (0::real)" and hsn: "sub_s ns = 1"
        and hsinc: "\<forall>i<ns. sub_s i < sub_s (Suc i)"
        and hs_UV: "\<forall>i<ns. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f (sub_s i + t * (sub_s (Suc i) - sub_s i)) \<in> U)
                         \<or> (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f (sub_s i + t * (sub_s (Suc i) - sub_s i)) \<in> V)"
      sorry \<comment> \<open>1D Lebesgue for f. Same as surjectivity proof (lines 2646-2755).\<close>
    \<comment> \<open>Step 3b: For each s-strip, get t-subdivision via tube lemma + open_cover_subdivision_01.
       For each strip [s_{i-1}, s_i] and each t_0, the tube lemma gives a t-ball where the
       strip maps into U or V. These balls cover [0,1]. By open_cover_subdivision_01,
       get a t-subdivision for each strip. Merge via grid_from_per_piece_subdivisions.\<close>
    obtain nt sub_t where hnt: "nt \<ge> 1" and ht0: "sub_t 0 = (0::real)" and htn: "sub_t nt = 1"
        and htinc: "\<forall>j<nt. sub_t j < sub_t (Suc j)"
        and hcell_UV: "\<forall>i<ns. \<forall>j<nt. (\<forall>s t. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)
                                          \<and> sub_t j \<le> t \<and> t \<le> sub_t (Suc j)
                                          \<and> 0\<le>s \<and> s\<le>1 \<and> 0\<le>t \<and> t\<le>1
                                          \<longrightarrow> F (s,t) \<in> U)
                            \<or> (\<forall>s t. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)
                                   \<and> sub_t j \<le> t \<and> t \<le> sub_t (Suc j)
                                   \<and> 0\<le>s \<and> s\<le>1 \<and> 0\<le>t \<and> t\<le>1
                                   \<longrightarrow> F (s,t) \<in> V)"
      sorry \<comment> \<open>2D Lebesgue: tube lemma (Lemma_26_8) + open_cover_subdivision_01 per strip
         + grid_from_per_piece_subdivisions to merge. ~80 lines.\<close>
    \<comment> \<open>===== ROW COMPARISON + TELESCOPING =====\<close>
    \<comment> \<open>Define row functions: f_j(s) = F(s, sub_t j). f_0 = f, f_nt = g.
       Show \<tau>(f_j) = \<tau>(f_{j+1}) for each j via \<sigma> telescoping.
       Transitivity gives \<tau>(f) = \<tau>(g).\<close>
    show "\<tau> f = \<tau> g"
      sorry \<comment> \<open>Row comparison: for adjacent rows, \<sigma> values telescope.
         Key: fᵢ \<cdot> \<beta>ᵢ \<simeq> \<beta>_{i-1} \<cdot> gᵢ in U or V (broken-line in convex cell).
         Then \<sigma>(fᵢ)\<cdot>\<sigma>(\<beta>ᵢ) = \<sigma>(\<beta>_{i-1})\<cdot>\<sigma>(gᵢ). Telescope + \<sigma>(const) = eH.
         ~100 lines for row comparison + transitivity.\<close>
  qed
  \<comment> \<open>===== Derive all three properties from A =====\<close>
  \<comment> \<open>Also need: \<tau> multiplicative (\<tau>(f*g) = \<tau>(f)\<cdot>\<tau>(g)) and \<tau> extension (\<tau>(f) = \<phi>_i([f])
     for f in U or V). These follow from subdivision independence + \<sigma>/\<rho> properties.\<close>
  have h\<Phi>_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0) H mulH \<Phi>"
    sorry \<comment> \<open>From h\<tau>_wd + \<tau> multiplicativity. The multiplicativity is a 1D argument:
       \<tau>(f*g) uses subdivision of f*g = subdivision of f + subdivision of g.\<close>
  have h\<Phi>_ext_U: "\<forall>a\<in>top1_fundamental_group_carrier U ?TU x0.
      \<Phi> (top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x) a) = \<phi>1 a"
    sorry \<comment> \<open>Proof sketch (needs h\<tau>_wd + \<tau> subdivision independence + \<rho> properties):
       1. \<Phi>([f]_X) = \<tau>(SOME g with [g]=[f]) = \<tau>(f) by h\<tau>_wd (since g \<simeq> f)
       2. \<tau>(f) = \<sigma>(f) (trivial subdivision, f already in U)
       3. \<sigma>(f) = \<rho>(\<alpha>(x0)\<cdot>f\<cdot>rev(\<alpha>(x0))) = \<rho>(const\<cdot>f\<cdot>const) since \<alpha>(x0)=const
       4. const\<cdot>f\<cdot>const \<simeq>_U f by Thm_51_2 identity laws
       5. \<rho>(f) = \<phi>1([f]_U) by \<rho> definition (f in U)
       Needs also: \<tau> subdivision-independent (adding subdivision point doesn't change \<tau>),
       which follows from \<sigma>(f*g) = \<sigma>(f)\<cdot>\<sigma>(g) and \<rho> homotopy-invariance.\<close>
  have h\<Phi>_ext_V: "\<forall>b\<in>top1_fundamental_group_carrier V ?TV x0.
      \<Phi> (top1_fundamental_group_induced_on V ?TV x0 X TX x0 (\<lambda>x. x) b) = \<phi>2 b"
    sorry \<comment> \<open>Same as ext_U but for V.\<close>
  show ?thesis using h\<Phi>_hom h\<Phi>_ext_U h\<Phi>_ext_V by (by100 blast)
qed

text \<open>Parameterized SvK: given a free product FP of π₁(U) and π₁(V),
  π₁(X) ≅ FP / normal-closure of amalgamation generators.\<close>
theorem Theorem_70_2_SvK_parameterized:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
      and hFP: "top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0
                then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
             (\<lambda>i. if i = 0
                then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
             \<iota>fam {0, 1}"
  shows "top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                        (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                        U (subspace_topology X TX U) x0 (\<lambda>x. x) c))
                          (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                            (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                            V (subspace_topology X TX V) x0 (\<lambda>x. x) c)))
                    | c. c \<in> top1_fundamental_group_carrier
                           (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 }))
             (top1_quotient_group_mul_on mulFP)"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?\<pi>X = "top1_fundamental_group_carrier X TX x0"
  let ?N = "top1_normal_subgroup_generated_on FP mulFP eFP invgFP
     { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
  have hTopX: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hUsub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
  have hTopU: "is_topology_on U ?TU" by (rule subspace_topology_is_topology_on[OF hTopX hUsub])
  have hTopV: "is_topology_on V ?TV" by (rule subspace_topology_is_topology_on[OF hTopX hVsub])
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU x0"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV x0"
  have hN_gens_sub: "{ mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0} \<subseteq> FP"
  proof (rule subsetI)
    fix x assume "x \<in> {mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
        | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0}"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        and hx: "x = mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))"
      by (by100 blast)
    let ?ind_U = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c"
    let ?ind_V = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c"
    have hUV_sub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
    have hTUV: "is_topology_on (U \<inter> V) ?TUV"
      by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub])
    have hx0_UV: "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
    have h0_in: "\<iota>fam 0 ?ind_U \<in> FP"
    proof -
      have "?ind_U \<in> ?\<pi>U"
      proof -
        have hx0_U: "x0 \<in> U" using assms(8) by (by100 blast)
        have hincl_cont: "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
        proof -
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
          moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
            by (rule subspace_topology_trans) (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U
            (top1_fundamental_group_mul U ?TU x0)
            (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x))"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV hTopU hx0_UV hx0_U hincl_cont])
             (by100 simp)
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      moreover have "\<forall>x\<in>?\<pi>U. \<iota>fam 0 x \<in> FP"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        thus ?thesis by (by100 force)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have h1_in: "\<iota>fam 1 ?ind_V \<in> FP"
    proof -
      have "?ind_V \<in> ?\<pi>V"
      proof -
        have hx0_V: "x0 \<in> V" using assms(8) by (by100 blast)
        have hincl_cont_V: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
        proof -
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
          moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
            by (rule subspace_topology_trans) (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>V
            (top1_fundamental_group_mul V ?TV x0)
            (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x))"
        proof -
          have "(\<lambda>x. x) x0 = x0" by (by100 simp)
          thus ?thesis
            by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV hTopV hx0_UV hx0_V hincl_cont_V])
        qed
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      moreover have "\<forall>x\<in>?\<pi>V. \<iota>fam 1 x \<in> FP"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        thus ?thesis by (by100 force)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have "invgFP (\<iota>fam 1 ?ind_V) \<in> FP"
      using hFP_grp h1_in unfolding top1_is_group_on_def by (by100 blast)
    thus "x \<in> FP"
      using hx h0_in hFP_grp unfolding top1_is_group_on_def by (by100 blast)
  qed
  have hN_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP ?N"
    by (rule normal_subgroup_generated_is_normal[OF hFP_grp hN_gens_sub])
  have hx0_X: "x0 \<in> X" using assms(8) assms(4) by (by100 blast)
  have h\<pi>X_grp: "top1_is_group_on ?\<pi>X (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
    by (rule top1_fundamental_group_is_group[OF hTopX hx0_X])
  \<comment> \<open>j-construction: surjective hom FP → π₁(X) with kernel N.\<close>
  \<comment> \<open>Step 1: Define hfam — the inclusion-induced homomorphisms.\<close>
  let ?hfam = "\<lambda>i::nat. if i = 0
      then top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x)
      else top1_fundamental_group_induced_on V ?TV x0 X TX x0 (\<lambda>x. x)"
  \<comment> \<open>Each hfam is a group hom from π₁(U/V) → π₁(X).\<close>
  have hx0_U: "x0 \<in> U" using assms(8) by (by100 blast)
  have hx0_V: "x0 \<in> V" using assms(8) by (by100 blast)
  have hincl_U: "top1_continuous_map_on U ?TU X TX (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on U (subspace_topology X TX U) X TX (\<lambda>x. x)"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopX, unfolded id_def]]) (rule hUsub)
    moreover have "subspace_topology X TX U = ?TU" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hincl_V: "top1_continuous_map_on V ?TV X TX (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on V (subspace_topology X TX V) X TX (\<lambda>x. x)"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopX, unfolded id_def]]) (rule hVsub)
    moreover have "subspace_topology X TX V = ?TV" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hhfam_hom: "\<forall>\<alpha>\<in>{0::nat, 1}. top1_group_hom_on
      (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
      (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
      ?\<pi>X (top1_fundamental_group_mul X TX x0) (?hfam \<alpha>)"
  proof (intro ballI)
    fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
    show "top1_group_hom_on
        (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
        (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
        ?\<pi>X (top1_fundamental_group_mul X TX x0) (?hfam \<alpha>)"
    proof (cases "\<alpha> = 0")
      case True
      have "top1_group_hom_on ?\<pi>U (top1_fundamental_group_mul U ?TU x0)
          ?\<pi>X (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x))"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTopU hTopX hx0_U hx0_X hincl_U])
           (by100 simp)
      thus ?thesis using True by (by100 simp)
    next
      case False hence "\<alpha> = 1" using h\<alpha> by (by100 blast)
      have "top1_group_hom_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0)
          ?\<pi>X (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_induced_on V ?TV x0 X TX x0 (\<lambda>x. x))"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTopV hTopX hx0_V hx0_X hincl_V])
           (by100 simp)
      thus ?thesis using \<open>\<alpha> = 1\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>π₁(U), π₁(V) are groups.\<close>
  have hGG_grps: "\<forall>\<alpha>\<in>{0::nat, 1}. top1_is_group_on
      (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
      (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
      (if \<alpha> = 0 then top1_fundamental_group_id U ?TU x0 else top1_fundamental_group_id V ?TV x0)
      (if \<alpha> = 0 then top1_fundamental_group_invg U ?TU x0 else top1_fundamental_group_invg V ?TV x0)"
  proof (intro ballI)
    fix \<alpha> :: nat assume h\<alpha>: "\<alpha> \<in> {0, 1}"
    show "top1_is_group_on
        (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
        (if \<alpha> = 0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0)
        (if \<alpha> = 0 then top1_fundamental_group_id U ?TU x0 else top1_fundamental_group_id V ?TV x0)
        (if \<alpha> = 0 then top1_fundamental_group_invg U ?TU x0 else top1_fundamental_group_invg V ?TV x0)"
      using h\<alpha> top1_fundamental_group_is_group[OF hTopU hx0_U]
            top1_fundamental_group_is_group[OF hTopV hx0_V] by (by100 auto)
  qed
  \<comment> \<open>Apply extension property to get j.\<close>
  from Lemma_68_3_extension_property[OF hFP h\<pi>X_grp hhfam_hom hGG_grps]
  obtain j where hj_hom: "top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j"
      and hj_ext: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V).
          j (\<iota>fam \<alpha> x) = ?hfam \<alpha> x"
    by (elim exE conjE) (by100 blast)
  \<comment> \<open>Step 2: j is surjective (Lebesgue number argument — every loop can be subdivided into
     pieces in U and V).\<close>
  have hj_surj: "j ` FP = ?\<pi>X"
  proof (rule set_eqI)
    fix c
    show "c \<in> j ` FP \<longleftrightarrow> c \<in> ?\<pi>X"
    proof
      \<comment> \<open>(→): j maps FP into π₁(X) since j is a group hom.\<close>
      assume "c \<in> j ` FP"
      then obtain w where hw: "w \<in> FP" and hc: "c = j w" by (by100 blast)
      show "c \<in> ?\<pi>X" using hj_hom hw hc unfolding top1_group_hom_on_def by (by100 blast)
    next
      \<comment> \<open>(←): Every loop class [f] ∈ π₁(X) is in the image of j.
         Proof sketch: subdivide the loop into pieces in U and V, lift to FP.
         Uses: Lebesgue number + path connectedness of U∩V.\<close>
      assume hc: "c \<in> ?\<pi>X"
      \<comment> \<open>c is a loop class [f] in π₁(X, x₀). Pick a representative loop f.\<close>
      \<comment> \<open>Step A: Subdivide f into pieces, each in U or V.\<close>
      \<comment> \<open>Step B: Adjust each piece to a loop at x₀ via connecting paths in U∩V.\<close>
      \<comment> \<open>Step C: Map each adjusted piece to FP via ιfam(0) or ιfam(1).\<close>
      \<comment> \<open>Step D: Show the product in FP maps to [f] under j.\<close>
      \<comment> \<open>Steps A-D use: Lebesgue number (Top1_Ch5_8), Theorem_51_3_aux (AlgTop_JCT_Base0),
         path connectedness of U∩V, and the extension property of j.\<close>
      \<comment> \<open>Pick a representative loop from class c.\<close>
      obtain f where hf: "top1_is_loop_on X TX x0 f" and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f g}"
        using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
      \<comment> \<open>f maps into X = U ∪ V. The preimages f⁻¹(U) and f⁻¹(V) cover [0,1].\<close>
      \<comment> \<open>By Lebesgue number, subdivide [0,1] so each piece maps into U or V.\<close>
      obtain m :: nat and subdiv :: "nat \<Rightarrow> real"
        where hm: "m \<ge> 1" and hs0: "subdiv 0 = 0" and hsm: "subdiv m = 1"
          and hs_mono: "\<And>i. i < m \<Longrightarrow> subdiv i < subdiv (Suc i)"
          and hs_UV: "\<forall>i<m. (\<forall>t. 0 \<le> t \<and> t \<le> 1
              \<longrightarrow> f (subdiv i + t * (subdiv (Suc i) - subdiv i)) \<in> U)
            \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1
              \<longrightarrow> f (subdiv i + t * (subdiv (Suc i) - subdiv i)) \<in> V)"
      proof -
        \<comment> \<open>Build the cover: for each s ∈ [0,1], f(s) ∈ U or V, giving a ball around s.\<close>
        have hf_cont: "top1_is_path_on X TX x0 x0 f"
          using hf unfolding top1_is_loop_on_def by (by100 blast)
        have hf_maps: "\<forall>s. 0 \<le> s \<and> s \<le> 1 \<longrightarrow> f s \<in> X"
        proof (intro allI impI)
          fix s :: real assume "0 \<le> s \<and> s \<le> 1"
          hence "s \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          thus "f s \<in> X" using hf_cont unfolding top1_is_path_on_def top1_continuous_map_on_def
            by (by100 blast)
        qed
        have hf_cont_on: "top1_continuous_map_on I_set I_top X TX f"
          using hf_cont unfolding top1_is_path_on_def by (by100 blast)
        let ?\<A> = "{S. S = {s. f s \<in> U \<and> 0 \<le> s \<and> s \<le> 1} \<or> S = {s. f s \<in> V \<and> 0 \<le> s \<and> s \<le> 1}}"
        have hU_TX: "U \<in> TX"
          using assms(2) unfolding openin_on_def by (by100 blast)
        have hV_TX: "V \<in> TX"
          using assms(3) unfolding openin_on_def by (by100 blast)
        have hcover: "\<forall>s::real. 0 \<le> s \<and> s \<le> 1 \<longrightarrow>
            (\<exists>W\<in>?\<A>. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W))"
        proof (intro allI impI)
          fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
          have hs_I: "s \<in> I_set" using hs unfolding top1_unit_interval_def by (by100 auto)
          have hfs: "f s \<in> X" using hf_maps hs by (by100 blast)
          hence "f s \<in> U \<or> f s \<in> V" using assms(4) by (by100 blast)
          thus "\<exists>W\<in>?\<A>. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W)"
          proof
            assume "f s \<in> U"
            obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hball: "f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
              using top1_continuous_preimage_ball[OF hf_cont_on hU_TX hs_I \<open>f s \<in> U\<close>] by (by100 blast)
            let ?W = "{s. f s \<in> U \<and> 0 \<le> s \<and> s \<le> 1}"
            have hW_A: "?W \<in> ?\<A>" by (by100 blast)
            have hs_W: "s \<in> ?W" using hs \<open>f s \<in> U\<close> by (by100 blast)
            have hball_W: "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> ?W"
              using hball by (by100 blast)
            show ?thesis
              apply (rule bexI[of _ ?W])
              using hs_W h\<epsilon> hball_W apply (by100 blast)
              using hW_A by (by100 blast)
          next
            assume "f s \<in> V"
            obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hball: "f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
              using top1_continuous_preimage_ball[OF hf_cont_on hV_TX hs_I \<open>f s \<in> V\<close>] by (by100 blast)
            let ?W = "{s. f s \<in> V \<and> 0 \<le> s \<and> s \<le> 1}"
            have hW_A: "?W \<in> ?\<A>" by (by100 blast)
            have hs_W: "s \<in> ?W" using hs \<open>f s \<in> V\<close> by (by100 blast)
            have hball_W: "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> ?W"
              using hball by (by100 blast)
            show ?thesis
              apply (rule bexI[of _ ?W])
              using hs_W h\<epsilon> hball_W apply (by100 blast)
              using hW_A by (by100 blast)
          qed
        qed
        from open_cover_subdivision_01[OF hcover]
        obtain n :: nat and sub where hn: "n \<ge> 1" and hsub0: "sub 0 = 0" and hsubn: "sub n = 1"
            and hsub_mono: "\<forall>i<n. sub i < sub (Suc i)"
            and hsub_cover: "\<forall>i<n. \<exists>W\<in>?\<A>. {s. sub i \<le> s \<and> s \<le> sub (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
          by (by100 auto)
        \<comment> \<open>Convert: each piece maps into U or V.\<close>
        have hs_UV: "\<forall>i<n. (\<forall>t. 0 \<le> t \<and> t \<le> 1
              \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> U)
            \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1
              \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> V)"
        proof (intro allI impI)
          fix i assume hi: "i < n"
          from hsub_cover hi obtain W where hW: "W \<in> ?\<A>"
              and hWsub: "{s. sub i \<le> s \<and> s \<le> sub (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
            by (by100 auto)
          from hW have "W = {s. f s \<in> U \<and> 0 \<le> s \<and> s \<le> 1} \<or> W = {s. f s \<in> V \<and> 0 \<le> s \<and> s \<le> 1}"
            by (by100 blast)
          thus "(\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> U)
              \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> V)"
          proof
            assume hWU: "W = {s. f s \<in> U \<and> 0 \<le> s \<and> s \<le> 1}"
            show ?thesis
            proof (rule disjI1, intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              let ?s = "sub i + t * (sub (Suc i) - sub i)"
              have "sub i < sub (Suc i)" using hsub_mono hi by (by100 blast)
              have "0 \<le> t * (sub (Suc i) - sub i)"
                using ht \<open>sub i < sub (Suc i)\<close> by (simp add: mult_nonneg_nonneg)
              moreover have "t * (sub (Suc i) - sub i) \<le> sub (Suc i) - sub i"
                using ht \<open>sub i < sub (Suc i)\<close>
                by (simp add: mult_left_le)
              ultimately have "sub i \<le> ?s \<and> ?s \<le> sub (Suc i)" by (by100 linarith)
              have "sub i \<ge> 0"
              proof -
                have "\<And>j. j \<le> i \<Longrightarrow> sub j \<ge> 0"
                proof -
                  fix j show "j \<le> i \<Longrightarrow> sub j \<ge> 0"
                  proof (induction j)
                    case 0 thus ?case using hsub0 by (by100 simp)
                  next
                    case (Suc j')
                    have "j' < n" using Suc.prems hi by (by100 linarith)
                    have "sub j' < sub (Suc j')" using hsub_mono \<open>j' < n\<close> by (by100 blast)
                    moreover have "sub j' \<ge> 0" using Suc.IH Suc.prems by (by100 simp)
                    ultimately show ?case by (by100 linarith)
                  qed
                qed
                thus ?thesis by (by100 blast)
              qed
              have "sub (Suc i) \<le> 1"
              proof -
                have "\<And>j. j \<ge> Suc i \<and> j \<le> n \<Longrightarrow> sub j \<le> 1"
                proof -
                  fix j show "j \<ge> Suc i \<and> j \<le> n \<Longrightarrow> sub j \<le> 1"
                  proof (induction "n - j" arbitrary: j)
                    case 0 hence "j = n" by (by100 linarith)
                    thus ?case using hsubn by (by100 simp)
                  next
                    case (Suc k)
                    have "j < n" using Suc.hyps Suc.prems by (by100 linarith)
                    have "sub j < sub (Suc j)" using hsub_mono \<open>j < n\<close> by (by100 blast)
                    have "k = n - Suc j" using Suc.hyps(2) \<open>j < n\<close> by (by100 linarith)
                    have "Suc j \<ge> Suc i \<and> Suc j \<le> n" using Suc.prems \<open>j < n\<close> by (by100 linarith)
                    have "sub (Suc j) \<le> 1"
                      using Suc.hyps(1)[of "Suc j"] \<open>k = n - Suc j\<close> \<open>Suc j \<ge> Suc i \<and> Suc j \<le> n\<close>
                      by (by100 linarith)
                    show ?case using \<open>sub j < sub (Suc j)\<close> \<open>sub (Suc j) \<le> 1\<close> by (by100 linarith)
                  qed
                qed
                hence "Suc i \<ge> Suc i \<and> Suc i \<le> n \<Longrightarrow> sub (Suc i) \<le> 1" by (by100 blast)
                thus ?thesis using hi by (by100 linarith)
              qed
              hence "0 \<le> ?s \<and> ?s \<le> 1"
                using \<open>sub i \<ge> 0\<close> \<open>sub i \<le> ?s \<and> ?s \<le> sub (Suc i)\<close> by (by100 linarith)
              hence "?s \<in> W" using hWsub \<open>sub i \<le> ?s \<and> ?s \<le> sub (Suc i)\<close> by (by100 blast)
              thus "f ?s \<in> U" using hWU by (by100 blast)
            qed
          next
            assume hWV: "W = {s. f s \<in> V \<and> 0 \<le> s \<and> s \<le> 1}"
            show ?thesis
            proof (rule disjI2, intro allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              let ?s = "sub i + t * (sub (Suc i) - sub i)"
              have "sub i < sub (Suc i)" using hsub_mono hi by (by100 blast)
              have "0 \<le> t * (sub (Suc i) - sub i)"
                using ht \<open>sub i < sub (Suc i)\<close> by (simp add: mult_nonneg_nonneg)
              moreover have "t * (sub (Suc i) - sub i) \<le> sub (Suc i) - sub i"
                using ht \<open>sub i < sub (Suc i)\<close>
                by (simp add: mult_left_le)
              ultimately have "sub i \<le> ?s \<and> ?s \<le> sub (Suc i)" by (by100 linarith)
              have "sub i \<ge> 0"
              proof -
                have "\<And>j. j \<le> i \<Longrightarrow> sub j \<ge> 0"
                proof -
                  fix j show "j \<le> i \<Longrightarrow> sub j \<ge> 0"
                  proof (induction j)
                    case 0 thus ?case using hsub0 by (by100 simp)
                  next
                    case (Suc j')
                    have "j' < n" using Suc.prems hi by (by100 linarith)
                    have "sub j' < sub (Suc j')" using hsub_mono \<open>j' < n\<close> by (by100 blast)
                    moreover have "sub j' \<ge> 0" using Suc.IH Suc.prems by (by100 simp)
                    ultimately show ?case by (by100 linarith)
                  qed
                qed
                thus ?thesis by (by100 blast)
              qed
              have "sub (Suc i) \<le> 1"
              proof -
                have "\<And>j. j \<ge> Suc i \<and> j \<le> n \<Longrightarrow> sub j \<le> 1"
                proof -
                  fix j show "j \<ge> Suc i \<and> j \<le> n \<Longrightarrow> sub j \<le> 1"
                  proof (induction "n - j" arbitrary: j)
                    case 0 hence "j = n" by (by100 linarith)
                    thus ?case using hsubn by (by100 simp)
                  next
                    case (Suc k)
                    have "j < n" using Suc.hyps Suc.prems by (by100 linarith)
                    have "sub j < sub (Suc j)" using hsub_mono \<open>j < n\<close> by (by100 blast)
                    have "k = n - Suc j" using Suc.hyps(2) \<open>j < n\<close> by (by100 linarith)
                    have "Suc j \<ge> Suc i \<and> Suc j \<le> n" using Suc.prems \<open>j < n\<close> by (by100 linarith)
                    have "sub (Suc j) \<le> 1"
                      using Suc.hyps(1)[of "Suc j"] \<open>k = n - Suc j\<close> \<open>Suc j \<ge> Suc i \<and> Suc j \<le> n\<close>
                      by (by100 linarith)
                    show ?case using \<open>sub j < sub (Suc j)\<close> \<open>sub (Suc j) \<le> 1\<close> by (by100 linarith)
                  qed
                qed
                hence "Suc i \<ge> Suc i \<and> Suc i \<le> n \<Longrightarrow> sub (Suc i) \<le> 1" by (by100 blast)
                thus ?thesis using hi by (by100 linarith)
              qed
              hence "0 \<le> ?s \<and> ?s \<le> 1"
                using \<open>sub i \<ge> 0\<close> \<open>sub i \<le> ?s \<and> ?s \<le> sub (Suc i)\<close> by (by100 linarith)
              hence "?s \<in> W" using hWsub \<open>sub i \<le> ?s \<and> ?s \<le> sub (Suc i)\<close> by (by100 blast)
              thus "f ?s \<in> V" using hWV by (by100 blast)
            qed
          qed
        qed
        have "n \<ge> 1 \<and> sub 0 = 0 \<and> sub n = 1
            \<and> (\<forall>i. i < n \<longrightarrow> sub i < sub (Suc i))
            \<and> (\<forall>i<n. (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> U)
                  \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub i + t * (sub (Suc i) - sub i)) \<in> V))"
          using hn hsub0 hsubn hsub_mono hs_UV by (by100 blast)
        show ?thesis
          apply (rule that[of n sub])
          using hn apply (by100 blast)
          using hsub0 apply (by100 blast)
          using hsubn apply (by100 blast)
          using hsub_mono apply (by100 blast)
          using hs_UV by (by100 blast)
      qed
      \<comment> \<open>By Theorem_51_3_aux: [f] = [f₀ · f₁ · ... · f_{m-1}].\<close>
      let ?pieces = "map (\<lambda>i t. f (subdiv i + t * (subdiv (Suc i) - subdiv i))) [0..<m]"
      have hf_homotopic: "top1_path_homotopic_on X TX x0 x0 f
          (foldr top1_path_product ?pieces (top1_constant_path x0))"
      proof -
        have hf_path: "top1_is_path_on X TX x0 x0 f"
          using hf unfolding top1_is_loop_on_def by (by100 blast)
        show ?thesis by (rule Theorem_51_3_aux[OF hTopX hf_path hm hs0 hsm hs_mono])
      qed
      \<comment> \<open>Each piece maps into U or V. Assemble connecting paths and map to FP.\<close>
      \<comment> \<open>For each subdivision point f(sᵢ) ∈ U ∩ V (when consecutive pieces differ),
         choose a path αᵢ from x₀ to f(sᵢ) in U ∩ V. Then αᵢ⁻¹ · fᵢ · αᵢ₊₁ is a loop
         at x₀ in U or V, giving an element of π₁(U) or π₁(V). Map to FP via ιfam.\<close>
      \<comment> \<open>Path assembly: connecting paths + conjugation → j(FP).\<close>
      \<comment> \<open>Strategy: define S(i), choose connecting paths, form conjugated loops, apply j.\<close>
      define S where "S i = (if (\<forall>t. 0 \<le> t \<and> t \<le> 1
          \<longrightarrow> f (subdiv i + t * (subdiv (Suc i) - subdiv i)) \<in> U) then U else V)" for i
      have hS_maps: "\<forall>i<m. \<forall>t. 0 \<le> t \<and> t \<le> 1
          \<longrightarrow> f (subdiv i + t * (subdiv (Suc i) - subdiv i)) \<in> S i"
        unfolding S_def using hs_UV by (by100 auto)
      have hS_UV: "\<forall>i<m. S i = U \<or> S i = V" unfolding S_def by (by100 auto)
      have hS_sub_X: "\<forall>i<m. S i \<subseteq> X" using hS_UV assms(4) by (by100 auto)
      have hS_pc: "\<forall>i<m. top1_path_connected_on (S i) (subspace_topology X TX (S i))"
        using hS_UV assms(6,7) by (by100 auto)
      \<comment> \<open>Subdivision boundary values.\<close>
      have hfs0: "f (subdiv 0) = x0" using hs0 hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      have hfsm: "f (subdiv m) = x0" using hsm hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 simp)
      \<comment> \<open>Each f(sᵢ) is in S(i-1) ∩ S(i) (boundary of adjacent pieces).\<close>
      have hfs_in_Si: "\<forall>i<m. f (subdiv i) \<in> S i"
        using hS_maps[rule_format] by (by100 force)
      have hfs_in_Si_prev: "\<forall>i. 0 < i \<and> i < m \<longrightarrow> f (subdiv i) \<in> S (i - 1)"
      proof (intro allI impI)
        fix i assume hi: "0 < i \<and> i < m"
        have "i - 1 < m" using hi by (by100 linarith)
        have "Suc (i - 1) = i" using hi by (by100 simp)
        hence "f (subdiv (i-1) + 1 * (subdiv i - subdiv (i-1))) \<in> S (i - 1)"
          using hS_maps[rule_format, OF \<open>i - 1 < m\<close>, of 1] by (by100 simp)
        moreover have "subdiv (i-1) + 1 * (subdiv i - subdiv (i-1)) = subdiv i" by (by100 simp)
        ultimately show "f (subdiv i) \<in> S (i - 1)" by (by100 simp)
      qed
      \<comment> \<open>x₀ ∈ U ∩ V.\<close>
      have hx0_U: "x0 \<in> U" using assms(8) by (by100 blast)
      have hx0_V: "x0 \<in> V" using assms(8) by (by100 blast)
      have hx0_Si: "\<forall>i<m. x0 \<in> S i" using hS_UV hx0_U hx0_V by (by100 auto)
      \<comment> \<open>Each piece fᵢ, viewed in X, is a loop at x₀ of a conjugated form.
         For the simple approach: each fᵢ maps into S(i) which is path-connected.
         Choose connecting path αᵢ from x₀ to f(sᵢ) in S(i) (for i<m, uses hx0_Si + hfs_in_Si).
         Special: α₀ = const (f(s₀) = x₀), αₘ = const (f(sₘ) = x₀).

         Then gᵢ = αᵢ · fᵢ · αᵢ₊₁⁻¹ is a loop at x₀ in S(i).
         By telescoping_core: g₀·...·g_{m-1} ~ α₀ · (f₀·...·f_{m-1}) · αₘ⁻¹ ~ const·f·const⁻¹ ~ f.
         Each [gᵢ] ∈ π₁(S(i)) = π₁(U) or π₁(V).
         j(ιfam(0 or 1)([gᵢ])) = [gᵢ] in π₁(X).
         Product: j(∏ ιfam([gᵢ])) = [g₀·...·g_{m-1}] = [f] = c. ∈ j(FP). ✓\<close>
      \<comment> \<open>Choose connecting paths. For simplicity, use αᵢ in S(i) for i < m,
         with α₀ = const at x₀ and αₘ-trick for the last.\<close>
      \<comment> \<open>Actually, we need αᵢ to work for BOTH gᵢ₋₁ (in S(i-1)) and gᵢ (in S(i)).
         So αᵢ must be in S(i-1) ∩ S(i). Since f(sᵢ) ∈ S(i-1) ∩ S(i) and
         x₀ ∈ U∩V ⊆ S(i-1) ∩ S(i), we can choose αᵢ in S(i-1) ∩ S(i).
         But S(i-1) ∩ S(i) could be U, V, or U∩V — all path-connected.\<close>
      \<comment> \<open>Step A: For each boundary point 1≤i≤m-1, choose connecting path γᵢ from x₀ to f(sᵢ).
         γᵢ lives in S(i-1) ∩ S(i) ⊆ X. Path exists by path-connectedness.\<close>
      \<comment> \<open>Step B: Form conjugated loops gᵢ = γᵢ · fᵢ · γᵢ₊₁⁻¹ (with γ₀=γₘ=const).
         Each gᵢ is a loop at x₀ in S(i).\<close>
      \<comment> \<open>Step C: Each [gᵢ]∈π₁(S(i))→j(ιfam([gᵢ]))∈j(FP). Product∈j(FP) (subgroup).\<close>
      \<comment> \<open>Step D: [g₀·...·g_{m-1}]=[f] by telescoping (γᵢ⁻¹·γᵢ cancels). So c∈j(FP).\<close>
      \<comment> \<open>Implementation: use j(FP) subgroup property + generation argument.\<close>
      have hj_FP_grp: "top1_is_group_on (j ` FP) (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
        by (rule hom_image_is_subgroup[OF hFP_grp h\<pi>X_grp hj_hom])
      \<comment> \<open>Step A: connecting paths.\<close>
      \<comment> \<open>S(i-1) ∩ S(i) is path-connected: it's U, V, or U∩V.\<close>
      have hSint_pc: "\<forall>i. 1 \<le> i \<and> i < m \<longrightarrow>
          top1_path_connected_on (S (i-1) \<inter> S i) (subspace_topology X TX (S (i-1) \<inter> S i))"
      proof (intro allI impI)
        fix i assume hi: "1 \<le> i \<and> i < m"
        have "i - 1 < m" using hi by (by100 linarith)
        have "S (i-1) = U \<or> S (i-1) = V" using hS_UV \<open>i - 1 < m\<close> by (by100 blast)
        moreover have "S i = U \<or> S i = V" using hS_UV hi by (by100 blast)
        ultimately have "S (i-1) \<inter> S i \<in> {U, V, U \<inter> V}" by (by100 auto)
        moreover have "top1_path_connected_on U (subspace_topology X TX U)"
          using assms(6) by (by100 simp)
        moreover have "top1_path_connected_on V (subspace_topology X TX V)"
          using assms(7) by (by100 simp)
        moreover have "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
          using assms(5) by (by100 simp)
        ultimately show "top1_path_connected_on (S (i-1) \<inter> S i) (subspace_topology X TX (S (i-1) \<inter> S i))"
          by (by100 auto)
      qed
      have hconn: "\<forall>i. 1 \<le> i \<and> i < m \<longrightarrow> (\<exists>\<gamma>. top1_is_path_on (S (i-1) \<inter> S i)
          (subspace_topology X TX (S (i-1) \<inter> S i)) x0 (f (subdiv i)) \<gamma>)"
      proof (intro allI impI)
        fix i assume hi: "1 \<le> i \<and> i < m"
        have hx0_int: "x0 \<in> S (i-1) \<inter> S i"
          using hx0_Si hi by (by100 auto)
        have hfi_int: "f (subdiv i) \<in> S (i-1) \<inter> S i"
          using hfs_in_Si hfs_in_Si_prev hi by (by100 auto)
        from hSint_pc[rule_format, OF hi]
        show "\<exists>\<gamma>. top1_is_path_on (S (i-1) \<inter> S i)
            (subspace_topology X TX (S (i-1) \<inter> S i)) x0 (f (subdiv i)) \<gamma>"
          unfolding top1_path_connected_on_def using hx0_int hfi_int by (by100 blast)
      qed
      \<comment> \<open>Step B-D: assemble conjugated loops, show product = [f], conclude c∈j(FP).\<close>
      \<comment> \<open>Key claim: [f₀·...·f_{m-1}] ∈ j(FP).
         Proof: define gᵢ using connecting paths γᵢ.
         Each [gᵢ] ∈ π₁(S(i)) maps to j(FP) via inclusion-induced + ιfam.
         Telescoping: [g₀]·...·[g_{m-1}] = [f₀·...·f_{m-1}] in π₁(X).
         Since j(FP) is a subgroup: [f₀·...·f_{m-1}] ∈ j(FP).
         Since [f] = [f₀·...·f_{m-1}]: c ∈ j(FP).\<close>
      \<comment> \<open>The class [foldr(pieces,const)] is in j(FP). By hf_homotopic, c = [f] = [foldr...].\<close>
      \<comment> \<open>Each piece is a path in S(i). The product f₀·...·f_{m-1} is a loop at x₀.
         Using connecting paths and subgroup closure of j(FP), we get c ∈ j(FP).\<close>
      \<comment> \<open>j(FP) is a subgroup of π₁(X).\<close>
      have hj_FP_grp: "top1_is_group_on (j ` FP) (top1_fundamental_group_mul X TX x0)
          (top1_fundamental_group_id X TX x0) (top1_fundamental_group_invg X TX x0)"
        by (rule hom_image_is_subgroup[OF hFP_grp h\<pi>X_grp hj_hom])
      \<comment> \<open>j(FP) contains iU*(π₁(U)) and iV*(π₁(V)).\<close>
      have h\<iota>_in_FP: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      have hj_contains_U: "?hfam 0 ` ?\<pi>U \<subseteq> j ` FP"
      proof (rule image_subsetI)
        fix x assume hx: "x \<in> ?\<pi>U"
        have "\<iota>fam 0 x \<in> FP" using h\<iota>_in_FP hx by (by100 force)
        moreover have "j (\<iota>fam 0 x) = ?hfam 0 x" using hj_ext hx by (by100 force)
        ultimately show "?hfam 0 x \<in> j ` FP" by (by100 force)
      qed
      have hj_contains_V: "?hfam 1 ` ?\<pi>V \<subseteq> j ` FP"
      proof (rule image_subsetI)
        fix x assume hx: "x \<in> ?\<pi>V"
        have "\<iota>fam 1 x \<in> FP" using h\<iota>_in_FP hx by (by100 force)
        moreover have "j (\<iota>fam 1 x) = ?hfam 1 x" using hj_ext hx by (by100 force)
        ultimately show "?hfam 1 x \<in> j ` FP" by (by100 force)
      qed
      \<comment> \<open>Any loop in U at x₀ has its class in j(FP), similarly for V.\<close>
      have hloop_U_in_jFP: "\<And>g. top1_is_loop_on U ?TU x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> j ` FP"
      proof -
        fix g assume hg: "top1_is_loop_on U ?TU x0 g"
        have hg_class: "{h. top1_loop_equiv_on U ?TU x0 g h} \<in> ?\<pi>U"
          unfolding top1_fundamental_group_carrier_def using hg by (by100 blast)
        have hjFP: "?hfam 0 {h. top1_loop_equiv_on U ?TU x0 g h} \<in> j ` FP"
          using hj_contains_U hg_class by (by100 blast)
        have "?hfam 0 {h. top1_loop_equiv_on U ?TU x0 g h}
            = {h. top1_loop_equiv_on X TX x0 g h}"
          using inclusion_induced_class[OF hUsub hTopX, of ?TU x0 g] hg by (by100 simp)
        thus "{h. top1_loop_equiv_on X TX x0 g h} \<in> j ` FP" using hjFP by (by100 simp)
      qed
      have hloop_V_in_jFP: "\<And>g. top1_is_loop_on V ?TV x0 g \<Longrightarrow>
          {h. top1_loop_equiv_on X TX x0 g h} \<in> j ` FP"
      proof -
        fix g assume hg: "top1_is_loop_on V ?TV x0 g"
        have hg_class: "{h. top1_loop_equiv_on V ?TV x0 g h} \<in> ?\<pi>V"
          unfolding top1_fundamental_group_carrier_def using hg by (by100 blast)
        have hjFP: "?hfam 1 {h. top1_loop_equiv_on V ?TV x0 g h} \<in> j ` FP"
          using hj_contains_V hg_class by (by100 blast)
        have "?hfam 1 {h. top1_loop_equiv_on V ?TV x0 g h}
            = {h. top1_loop_equiv_on X TX x0 g h}"
          using inclusion_induced_class[OF hVsub hTopX, of ?TV x0 g] hg by (by100 simp)
        thus "{h. top1_loop_equiv_on X TX x0 g h} \<in> j ` FP" using hjFP by (by100 simp)
      qed
      \<comment> \<open>The key claim: [f] ∈ j(FP).
         Every loop in X at x₀ whose image lies in a single U or V is in j(FP).
         For the general case with m pieces: conjugate each piece with connecting paths
         to get loops in U or V. Product is in j(FP) by subgroup closure.
         Telescoping shows this product equals [f].\<close>
      \<comment> \<open>Apply svk_pieces_in_subgroup to get [foldr(pieces,const)] ∈ j(FP).\<close>
      have hpieces_cont: "\<And>i. i < m \<Longrightarrow> top1_continuous_map_on I_set I_top X TX (?pieces!i)"
      proof -
        fix i assume hi: "i < m"
        have hpi: "?pieces!i = (\<lambda>t. f (subdiv i + t * (subdiv (Suc i) - subdiv i)))" using hi by (by100 simp)
        have hf_cont_I: "top1_continuous_map_on I_set I_top X TX f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        \<comment> \<open>The affine map t ↦ subdiv i + t*(subdiv(Suc i) - subdiv i) maps [0,1] to [subdiv i, subdiv(Suc i)] ⊆ [0,1].\<close>
        define aff where "aff t = subdiv i + t * (subdiv (Suc i) - subdiv i)" for t :: real
        have hsi_ge0: "subdiv i \<ge> 0"
        proof -
          have "\<And>j. j \<le> i \<Longrightarrow> subdiv j \<ge> 0"
          proof -
            fix j show "j \<le> i \<Longrightarrow> subdiv j \<ge> 0"
            proof (induction j)
              case 0 thus ?case using hs0 by (by100 simp)
            next
              case (Suc j')
              have "j' < m" using Suc.prems hi by (by100 linarith)
              have "subdiv j' \<ge> 0" using Suc.IH Suc.prems by (by100 simp)
              have "subdiv j' < subdiv (Suc j')" using hs_mono \<open>j' < m\<close> by (by100 blast)
              thus ?case using \<open>subdiv j' \<ge> 0\<close> by (by100 linarith)
            qed
          qed
          thus ?thesis by (by100 blast)
        qed
        have hsi1_le1: "subdiv (Suc i) \<le> 1"
        proof -
          have "\<And>j. j \<ge> Suc i \<and> j \<le> m \<Longrightarrow> subdiv j \<le> 1"
          proof -
            fix j show "j \<ge> Suc i \<and> j \<le> m \<Longrightarrow> subdiv j \<le> 1"
            proof (induction "m - j" arbitrary: j)
              case 0 hence "j = m" by (by100 linarith)
              thus ?case using hsm by (by100 simp)
            next
              case (Suc k)
              have "j < m" using Suc.hyps Suc.prems by (by100 linarith)
              have "k = m - Suc j" using Suc.hyps(2) \<open>j < m\<close> by (by100 linarith)
              have "Suc j \<ge> Suc i \<and> Suc j \<le> m" using Suc.prems \<open>j < m\<close> by (by100 linarith)
              have "subdiv (Suc j) \<le> 1"
                using Suc.hyps(1)[of "Suc j"] \<open>k = m - Suc j\<close> \<open>Suc j \<ge> Suc i \<and> Suc j \<le> m\<close>
                by (by100 linarith)
              show ?case using hs_mono[OF \<open>j < m\<close>] \<open>subdiv (Suc j) \<le> 1\<close> by (by100 linarith)
            qed
          qed
          hence "Suc i \<ge> Suc i \<and> Suc i \<le> m \<Longrightarrow> subdiv (Suc i) \<le> 1" by (by100 blast)
          thus ?thesis using hi by (by100 linarith)
        qed
        have hsi_lt_si1: "subdiv i < subdiv (Suc i)" using hs_mono hi by (by100 blast)
        have haff_range: "\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> 0 \<le> aff t \<and> aff t \<le> 1"
        proof (intro allI impI conjI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          show "0 \<le> aff t" unfolding aff_def using hsi_ge0 hsi_lt_si1 ht
            by (simp add: mult_nonneg_nonneg)
          have "t * (subdiv (Suc i) - subdiv i) \<le> subdiv (Suc i) - subdiv i"
            using ht hsi_lt_si1 by (simp add: mult_left_le)
          hence "aff t \<le> subdiv (Suc i)" unfolding aff_def by (by100 linarith)
          thus "aff t \<le> 1" using hsi1_le1 by (by100 linarith)
        qed
        have haff_cont: "top1_continuous_map_on I_set I_top I_set I_top aff"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix t assume "t \<in> I_set"
          hence "0 \<le> t \<and> t \<le> 1" unfolding top1_unit_interval_def by (by100 auto)
          thus "aff t \<in> I_set" using haff_range unfolding top1_unit_interval_def by (by100 auto)
        next
          fix V assume hV: "V \<in> I_top"
          obtain W where hW: "W \<in> top1_open_sets" and hVW: "V = I_set \<inter> W"
            using hV unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 auto)
          have hW_open: "open W" using hW unfolding top1_open_sets_def by (by100 blast)
          have haff_HOL: "continuous_on UNIV aff"
            unfolding aff_def by (intro continuous_intros)
          have "\<forall>B. open B \<longrightarrow> open (aff -` B \<inter> UNIV)"
            using continuous_on_open_vimage[of UNIV aff] open_UNIV haff_HOL by (by100 blast)
          hence "open (aff -` W)" using hW_open by (by100 force)
          hence "aff -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
          have "{t \<in> I_set. aff t \<in> V} = I_set \<inter> (aff -` W)"
          proof
            show "{t \<in> I_set. aff t \<in> V} \<subseteq> I_set \<inter> (aff -` W)"
              using hVW by (by100 blast)
            show "I_set \<inter> (aff -` W) \<subseteq> {t \<in> I_set. aff t \<in> V}"
              using hVW haff_range unfolding top1_unit_interval_def by (by100 auto)
          qed
          thus "{t \<in> I_set. aff t \<in> V} \<in> I_top"
            unfolding top1_unit_interval_topology_def subspace_topology_def
            using \<open>aff -` W \<in> top1_open_sets\<close> by (by100 blast)
        qed
        have "top1_continuous_map_on I_set I_top X TX (f \<circ> aff)"
          by (rule top1_continuous_map_on_comp[OF haff_cont hf_cont_I])
        moreover have "(f \<circ> aff) = (?pieces!i)" unfolding aff_def hpi comp_def by (by100 auto)
        ultimately show "top1_continuous_map_on I_set I_top X TX (?pieces!i)" by (by100 simp)
      qed
      have hpieces_endpts: "\<And>i. i < m \<Longrightarrow>
          (?pieces!i) 0 = (if i = 0 then x0 else (?pieces!(i-1)) 1)"
      proof -
        fix i assume hi: "i < m"
        have hpi: "?pieces!i = (\<lambda>t. f (subdiv i + t * (subdiv (Suc i) - subdiv i)))"
          using hi by (by100 simp)
        have hpi0: "(?pieces!i) 0 = f (subdiv i)" using hpi by (by100 simp)
        show "(?pieces!i) 0 = (if i = 0 then x0 else (?pieces!(i-1)) 1)"
        proof (cases "i = 0")
          case True thus ?thesis using hpi0 hfs0 by (by100 simp)
        next
          case False
          hence "i - 1 < m" using hi by (by100 linarith)
          have "(?pieces!(i-1)) 1 = f (subdiv (i-1) + 1 * (subdiv (Suc (i-1)) - subdiv (i-1)))"
            using \<open>i - 1 < m\<close> by (by100 simp)
          also have "\<dots> = f (subdiv i)" using False by (by100 simp)
          finally show ?thesis using hpi0 False by (by100 simp)
        qed
      qed
      have hpieces_end: "(?pieces!(m-1)) 1 = x0"
      proof -
        have "m - 1 < m" using hm by (by100 linarith)
        hence "?pieces!(m-1) = (\<lambda>t. f (subdiv (m-1) + t * (subdiv m - subdiv (m-1))))"
          by (by100 simp)
        hence "(?pieces!(m-1)) 1 = f (subdiv (m-1) + 1 * (subdiv m - subdiv (m-1)))" by (by100 simp)
        also have "\<dots> = f (subdiv m)" by (by100 simp)
        also have "\<dots> = f 1" using hsm by (by100 simp)
        also have "\<dots> = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        finally show ?thesis .
      qed
      have hpieces_UV: "\<And>i. i < m \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?pieces!i) t \<in> U)
                                  \<or> (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> (?pieces!i) t \<in> V)"
        using hs_UV by (by100 auto)
      have hUV_sub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
      have hTUV: "is_topology_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
        by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub])
      have hx0_UV: "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
      have hpieces_len: "length ?pieces = m" by (by100 simp)
      have hfold_in_jFP: "{g. top1_loop_equiv_on X TX x0
          (foldr top1_path_product ?pieces (top1_constant_path x0)) g} \<in> j ` FP"
        by (rule svk_pieces_in_subgroup[OF hTopX hUsub hVsub assms(6) assms(7) assms(5) hx0_UV
              hj_FP_grp hloop_U_in_jFP hloop_V_in_jFP hm hpieces_len hpieces_UV
              hpieces_cont hpieces_endpts hpieces_end])
      \<comment> \<open>c = [f] = [foldr(pieces, const)] by hf_homotopic.\<close>
      have hc_eq_fold: "c = {g. top1_loop_equiv_on X TX x0
          (foldr top1_path_product ?pieces (top1_constant_path x0)) g}"
      proof -
        \<comment> \<open>f ~ foldr(pieces,const) by hf_homotopic. So [f] = [foldr(pieces,const)].\<close>
        have "top1_loop_equiv_on X TX x0 f
            (foldr top1_path_product ?pieces (top1_constant_path x0))"
        proof -
          have "top1_is_loop_on X TX x0 f" using hf by (by100 blast)
          moreover have "top1_is_loop_on X TX x0 (foldr top1_path_product ?pieces (top1_constant_path x0))"
            using hf_homotopic unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
          ultimately show ?thesis using hf_homotopic unfolding top1_loop_equiv_on_def top1_is_loop_on_def
            by (by100 blast)
        qed
        hence hfold_equiv: "top1_loop_equiv_on X TX x0 f
            (foldr top1_path_product ?pieces (top1_constant_path x0))" .
        have hfold_sym: "top1_loop_equiv_on X TX x0
            (foldr top1_path_product ?pieces (top1_constant_path x0)) f"
          by (rule top1_loop_equiv_on_sym[OF hfold_equiv])
        have "{g. top1_loop_equiv_on X TX x0 f g}
            = {g. top1_loop_equiv_on X TX x0
                (foldr top1_path_product ?pieces (top1_constant_path x0)) g}"
        proof (rule set_eqI)
          fix k show "k \<in> {g. top1_loop_equiv_on X TX x0 f g} \<longleftrightarrow>
              k \<in> {g. top1_loop_equiv_on X TX x0
                (foldr top1_path_product ?pieces (top1_constant_path x0)) g}"
            using top1_loop_equiv_on_trans[OF hTopX hfold_equiv]
                  top1_loop_equiv_on_trans[OF hTopX hfold_sym] by (by100 blast)
        qed
        thus ?thesis using hc_eq by (by100 simp)
      qed
      show "c \<in> j ` FP" using hc_eq_fold hfold_in_jFP by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 3: kernel(j) = N.\<close>
  \<comment> \<open>Kernel ⊇: N ⊆ ker(j). Each amalgamation generator maps to identity under j.\<close>
  let ?e_X = "top1_fundamental_group_id X TX x0"
  let ?gens = "{ mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
            (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
      | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
  have hgens_in_ker: "?gens \<subseteq> top1_group_kernel_on FP ?e_X j"
  proof (rule subsetI)
    fix w assume "w \<in> ?gens"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        and hw: "w = mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
            (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))"
      by (by100 blast)
    let ?iU_c = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c"
    let ?iV_c = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c"
    \<comment> \<open>j(ιfam 0 (iU*(c))) = iU*(c) viewed in π₁(X) = inclusion of c from U to X.\<close>
    have hUV_sub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
    have hTUV': "is_topology_on (U \<inter> V) ?TUV"
      by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub])
    have hx0_UV': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
    have hincl_UV_U: "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
      moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
        by (rule subspace_topology_trans) (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hincl_UV_V: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
      moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
        by (rule subspace_topology_trans) (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hiU_hom: "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
        (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U (top1_fundamental_group_mul U ?TU x0)
        (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopU hx0_UV' hx0_U hincl_UV_U])
         (by100 simp)
    have hiV_hom: "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
        (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>V (top1_fundamental_group_mul V ?TV x0)
        (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopV hx0_UV' hx0_V hincl_UV_V])
         (by100 simp)
    have hiUc_in: "?iU_c \<in> ?\<pi>U"
      using hiU_hom hc unfolding top1_group_hom_on_def by (by100 blast)
    have hiVc_in: "?iV_c \<in> ?\<pi>V"
      using hiV_hom hc unfolding top1_group_hom_on_def by (by100 blast)
    have hj_iU: "j (\<iota>fam 0 ?iU_c) = ?hfam 0 ?iU_c"
      using hj_ext hiUc_in by (by100 force)
    have hj_iV: "j (\<iota>fam 1 ?iV_c) = ?hfam 1 ?iV_c"
      using hj_ext hiVc_in by (by100 force)
    \<comment> \<open>Both hfam(0)(iU*(c)) and hfam(1)(iV*(c)) equal the inclusion of c from U∩V to X.\<close>
    \<comment> \<open>hfam(0) = induced map U→X, hfam(1) = induced map V→X.\<close>
    \<comment> \<open>iU*(c) is the induced of c along U∩V→U. Then applying U→X gives U∩V→U→X = U∩V→X.\<close>
    \<comment> \<open>Similarly for V. Both are the inclusion-induced map U∩V→X applied to c.\<close>
    have hfam_0_iU: "?hfam 0 ?iU_c
        = top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 (\<lambda>x. x) c"
    proof -
      have "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 ((\<lambda>x. x) \<circ> (\<lambda>x. x)) c
          = top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x)
              (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c)"
        by (rule fundamental_group_induced_comp[OF hTUV' hTopU hTopX hincl_UV_U hincl_U
              hx0_UV' _ _ hc]) (by100 simp)+
      moreover have "((\<lambda>x::'a. x) \<circ> (\<lambda>x. x)) = (\<lambda>x. x)" by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    have hfam_1_iV: "?hfam 1 ?iV_c
        = top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 (\<lambda>x. x) c"
    proof -
      have "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 ((\<lambda>x. x) \<circ> (\<lambda>x. x)) c
          = top1_fundamental_group_induced_on V ?TV x0 X TX x0 (\<lambda>x. x)
              (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)"
        by (rule fundamental_group_induced_comp[OF hTUV' hTopV hTopX hincl_UV_V hincl_V
              hx0_UV' _ _ hc]) (by100 simp)+
      moreover have "((\<lambda>x::'a. x) \<circ> (\<lambda>x. x)) = (\<lambda>x. x)" by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>So j maps the generator to iX*(c) * iX*(c)⁻¹ = e.\<close>
    have "w \<in> FP" using hN_gens_sub \<open>w \<in> ?gens\<close> by (by100 blast)
    let ?iX_c = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 (\<lambda>x. x) c"
    have "j (\<iota>fam 0 ?iU_c) = ?iX_c" using hj_iU hfam_0_iU by (by100 simp)
    have "j (\<iota>fam 1 ?iV_c) = ?iX_c" using hj_iV hfam_1_iV by (by100 simp)
    \<comment> \<open>w = ιfam(0)(iU*(c)) · invgFP(ιfam(1)(iV*(c))).\<close>
    have h\<iota>0_FP: "\<iota>fam 0 ?iU_c \<in> FP"
    proof -
      have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      thus ?thesis using hiUc_in by (by100 force)
    qed
    have h\<iota>1_FP: "\<iota>fam 1 ?iV_c \<in> FP"
    proof -
      have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      thus ?thesis using hiVc_in by (by100 force)
    qed
    have hinv\<iota>1_FP: "invgFP (\<iota>fam 1 ?iV_c) \<in> FP"
      using hFP_grp h\<iota>1_FP unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>j(w) = j(a · b) = j(a) · j(b) = iX*(c) · j(invgFP(ιfam 1 (iV*(c)))).\<close>
    have "j w = (top1_fundamental_group_mul X TX x0) (j (\<iota>fam 0 ?iU_c)) (j (invgFP (\<iota>fam 1 ?iV_c)))"
      using hw hj_hom h\<iota>0_FP hinv\<iota>1_FP unfolding top1_group_hom_on_def by (by100 blast)
    also have "j (\<iota>fam 0 ?iU_c) = ?iX_c" by (rule \<open>j (\<iota>fam 0 ?iU_c) = ?iX_c\<close>)
    also have "j (invgFP (\<iota>fam 1 ?iV_c)) = top1_fundamental_group_invg X TX x0 (j (\<iota>fam 1 ?iV_c))"
      by (rule hom_preserves_inv[OF hFP_grp h\<pi>X_grp hj_hom h\<iota>1_FP])
    also have "j (\<iota>fam 1 ?iV_c) = ?iX_c" by (rule \<open>j (\<iota>fam 1 ?iV_c) = ?iX_c\<close>)
    finally have "j w = (top1_fundamental_group_mul X TX x0) ?iX_c
        (top1_fundamental_group_invg X TX x0 ?iX_c)" by (by100 simp)
    \<comment> \<open>iX*(c) * iX*(c)⁻¹ = e_X.\<close>
    have hx0_X': "x0 \<in> X" using assms(8) assms(4) by (by100 blast)
    have hincl_UV_X: "top1_continuous_map_on (U \<inter> V) ?TUV X TX (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) X TX (\<lambda>x. x)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopX, unfolded id_def] hUV_sub])
      moreover have "subspace_topology X TX (U \<inter> V) = ?TUV" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hiX_hom: "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
        (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>X (top1_fundamental_group_mul X TX x0)
        (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 X TX x0 (\<lambda>x. x))"
      by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopX hx0_UV' hx0_X' hincl_UV_X])
         (by100 simp)
    have hiXc_in: "?iX_c \<in> ?\<pi>X"
      using hiX_hom hc unfolding top1_group_hom_on_def by (by100 blast)
    have "top1_fundamental_group_mul X TX x0 ?iX_c (top1_fundamental_group_invg X TX x0 ?iX_c) = ?e_X"
      by (rule group_inv_right[OF h\<pi>X_grp hiXc_in])
    hence "j w = ?e_X"
      using \<open>j w = (top1_fundamental_group_mul X TX x0) ?iX_c (top1_fundamental_group_invg X TX x0 ?iX_c)\<close>
      by (by100 simp)
    show "w \<in> top1_group_kernel_on FP ?e_X j"
      unfolding top1_group_kernel_on_def using \<open>w \<in> FP\<close> \<open>j w = ?e_X\<close> by (by100 blast)
  qed
  have hker_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP
      (top1_group_kernel_on FP ?e_X j)"
    by (rule kernel_is_normal_subgroup[OF hFP_grp h\<pi>X_grp hj_hom])
  have hN_sub_ker: "?N \<subseteq> top1_group_kernel_on FP ?e_X j"
    unfolding top1_normal_subgroup_generated_on_def
    using hgens_in_ker hker_normal by (by100 blast)
  have hker_sub_N: "top1_group_kernel_on FP ?e_X j \<subseteq> ?N"
  proof (rule subsetI)
    fix w assume hw: "w \<in> top1_group_kernel_on FP ?e_X j"
    hence hwFP: "w \<in> FP" and hjw: "j w = ?e_X"
      unfolding top1_group_kernel_on_def by (by100 blast)+
    \<comment> \<open>j(w) = identity in π₁(X) means the corresponding loop is nulhomotopic.
       The nulhomotopy can be subdivided into a grid, each cell mapping into U or V.
       Reading each row gives a word in FP that projects to the same element of FP/N.
       Bottom row = w mod N, top row = eFP mod N. Hence w ∈ N.

       This is the 2D Lebesgue number argument — the deepest part of SvK.
       Infrastructure available: grid_from_per_piece_subdivisions (Top1_Ch9_13),
       open_cover_subdivision_01, svk_pieces_in_subgroup.\<close>
    \<comment> \<open>==== ker \<subseteq> N proof via 2D nulhomotopy decomposition ====\<close>
    \<comment> \<open>Step A: j(w) = e_X means the image of w is the identity loop class.
       Extract a representative loop f and its nulhomotopy F: I\<times>I \<rightarrow> X.\<close>
    \<comment> \<open>j(w) \<in> \<pi>_1(X), and j(w) = e_X = {g | loop_equiv(x0, const, g)}.
       So const_{x0} \<in> j(w), meaning j(w) is a set of loops equivalent to const.\<close>
    \<comment> \<open>Since w \<in> FP and j is a hom with j(w) = e_X, the corresponding loop is nulhomotopic.\<close>

    \<comment> \<open>Step B: Subdivide I\<times>I into a grid where each cell maps into U or V.
       Apply open_cover_subdivision_01 to each "row" (fixed t, varying s) of F,
       then merge via grid_from_per_piece_subdivisions.\<close>

    \<comment> \<open>Step C: For each row j of the grid, read the cells as pieces.
       Each piece maps into U or V. Connect endpoints via paths in U\<inter>V.
       By svk_pieces_in_subgroup, each row gives an element of j(FP).
       Define row_j = the preimage word in FP.\<close>

    \<comment> \<open>Step D: Adjacent rows differ by a relator.
       Row_{j+1} differs from Row_j by one cell change. The cell maps into
       U \<inter> V (where the two rows overlap). The difference is
       \<iota>_0(c) \<cdot> \<iota>_1(c)\<inverse> for some c \<in> \<pi>_1(U \<inter> V), which is a generator of N.\<close>

    \<comment> \<open>Step E: Bottom row = w mod N, Top row = eFP mod N.
       Bottom row F(s,0) = f(s) corresponds to j(w).
       Top row F(s,1) = x0 corresponds to the constant loop = j(eFP).
       Transitivity of row equivalences: w \<equiv> eFP mod N, hence w \<in> N.\<close>

    \<comment> \<open>===== KER \<subseteq> N PROOF via left-inverse construction =====
       Strategy (Munkres Thm 70.2): construct \<Phi>: \<pi>_1(X) \<rightarrow> FP/N such that
       \<Phi> \<circ> j = \<pi> (quotient projection). Then j(w)=e_X \<Rightarrow> \<pi>(w) = \<Phi>(e_X) = e_{FP/N}
       \<Rightarrow> w \<in> N. The map \<Phi> is constructed using the universal property of \<pi>_1(X)
       with target H = FP/N, and \<phi>_1/\<phi>_2 being inclusion+projection.\<close>
    \<comment> \<open>Approach: Use Theorem 70.1 (parameterized SvK) with H = FP/N.
       Define \<phi>_1: \<pi>_1(U) \<rightarrow> FP/N by a \<mapsto> \<iota>_0(a) \<cdot> N.
       Define \<phi>_2: \<pi>_1(V) \<rightarrow> FP/N by b \<mapsto> \<iota>_1(b) \<cdot> N.
       Check: \<phi>_1 \<circ> i_1 = \<phi>_2 \<circ> i_2 (because i_1(c)\<inverse>\<cdot>i_2(c) \<in> N for c \<in> \<pi>_1(U\<inter>V)).
       Then \<exists>\<Phi> with \<Phi>\<circ>j_1 = \<phi>_1, \<Phi>\<circ>j_2 = \<phi>_2. So \<Phi>\<circ>j = \<pi>, giving the result.\<close>
    let ?Q = "top1_quotient_group_carrier_on FP mulFP ?N"
    let ?mulQ = "top1_quotient_group_mul_on mulFP"
    let ?\<pi>_q = "\<lambda>g. top1_group_coset_on FP mulFP ?N g"
    \<comment> \<open>Step 1: FP/N is a group.\<close>
    have hQ_grp: "\<exists>eQ invgQ. top1_is_group_on ?Q ?mulQ eQ invgQ"
      using quotient_group_is_group[OF hFP_grp hN_normal] by (by100 blast)
    \<comment> \<open>Step 2: \<phi>_1 and \<phi>_2 are compatible on U\<inter>V.\<close>
    let ?\<phi>1 = "\<lambda>a. ?\<pi>_q (\<iota>fam 0 a)"
    let ?\<phi>2 = "\<lambda>b. ?\<pi>_q (\<iota>fam 1 b)"
    have hcompat: "\<forall>c\<in>top1_fundamental_group_carrier (U \<inter> V) ?TUV x0.
        ?\<phi>1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c)
      = ?\<phi>2 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)"
    proof
      fix c assume hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
      let ?iU_c = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c"
      let ?iV_c = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c"
      \<comment> \<open>The generator mulFP(\<iota>0(?iU_c))(invgFP(\<iota>1(?iV_c))) is in N by definition.\<close>
      have hgen_in_N: "mulFP (\<iota>fam 0 ?iU_c) (invgFP (\<iota>fam 1 ?iV_c)) \<in> ?N"
      proof -
        have "mulFP (\<iota>fam 0 ?iU_c) (invgFP (\<iota>fam 1 ?iV_c)) \<in>
            { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c'))
                    (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c')))
              | c'. c' \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
          using hc by (by100 blast)
        thus ?thesis
          unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      qed
      \<comment> \<open>From the generator being in N, derive coset equality.\<close>
      \<comment> \<open>coset(\<iota>0(iU_c)) = coset(\<iota>1(iV_c)) iff mulFP(invgFP(\<iota>0(iU_c)))(\<iota>1(iV_c)) \<in> N.\<close>
      \<comment> \<open>The generator gives us \<iota>0 \<cdot> inv(\<iota>1) \<in> N. We need inv(\<iota>0) \<cdot> \<iota>1 \<in> N.\<close>
      \<comment> \<open>inv(generator) = \<iota>1 \<cdot> inv(\<iota>0) \<in> N (N is a group).\<close>
      \<comment> \<open>Conjugate: inv(\<iota>1) \<cdot> (\<iota>1 \<cdot> inv(\<iota>0)) \<cdot> \<iota>1 = inv(\<iota>0) \<cdot> \<iota>1 \<in> N (N is normal).\<close>
      \<comment> \<open>Need: inv(\<iota>0) \<cdot> \<iota>1 \<in> N. From generator \<iota>0 \<cdot> inv(\<iota>1) \<in> N:\<close>
      let ?a = "\<iota>fam 0 ?iU_c" and ?b = "\<iota>fam 1 ?iV_c"
      have hUV_sub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
      have hTUV_loc: "is_topology_on (U \<inter> V) ?TUV"
        by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub])
      have hx0_UV_loc: "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
      have hincl_UV_U_loc: "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
      proof -
        have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
        moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
          by (rule subspace_topology_trans) (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hincl_UV_V_loc: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
      proof -
        have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
        moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
          by (rule subspace_topology_trans) (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hiUc_piU: "?iU_c \<in> ?\<pi>U"
        using top1_fundamental_group_induced_on_is_hom[OF hTUV_loc hTopU hx0_UV_loc hx0_U hincl_UV_U_loc] hc
        unfolding top1_group_hom_on_def by (by100 blast)
      have hiVc_piV: "?iV_c \<in> ?\<pi>V"
        using top1_fundamental_group_induced_on_is_hom[OF hTUV_loc hTopV hx0_UV_loc hx0_V hincl_UV_V_loc] hc
        unfolding top1_group_hom_on_def by (by100 blast)
      have h\<iota>_in_FP: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      have ha_FP: "?a \<in> FP" using h\<iota>_in_FP hiUc_piU by (by100 force)
      have hb_FP: "?b \<in> FP" using h\<iota>_in_FP hiVc_piV by (by100 force)
      have hinva_FP: "invgFP ?a \<in> FP"
        using hFP_grp ha_FP unfolding top1_is_group_on_def by (by100 blast)
      have hinvb_FP: "invgFP ?b \<in> FP"
        using hFP_grp hb_FP unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>inv(generator) = \<iota>1 \<cdot> inv(\<iota>0) \<in> N (N is closed under inverse).\<close>
      have hN_grp: "top1_is_group_on ?N mulFP eFP invgFP"
        using hN_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
      have hinv_gen: "invgFP (mulFP ?a (invgFP ?b)) \<in> ?N"
      proof -
        have "mulFP ?a (invgFP ?b) \<in> ?N" by (rule hgen_in_N)
        thus ?thesis using hN_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      \<comment> \<open>inv(a \<cdot> inv(b)) = b \<cdot> inv(a) in a group.\<close>
      have hinv_expand: "invgFP (mulFP ?a (invgFP ?b)) = mulFP ?b (invgFP ?a)"
      proof -
        have "invgFP (mulFP ?a (invgFP ?b)) = mulFP (invgFP (invgFP ?b)) (invgFP ?a)"
          by (rule group_inv_mul[OF hFP_grp ha_FP hinvb_FP])
        also have "invgFP (invgFP ?b) = ?b"
          by (rule group_inv_inv[OF hFP_grp hb_FP])
        finally show ?thesis by (by100 simp)
      qed
      hence hb_inva_N: "mulFP ?b (invgFP ?a) \<in> ?N" using hinv_gen by (by100 simp)
      \<comment> \<open>Conjugate by inv(b): inv(b) \<cdot> (b \<cdot> inv(a)) \<cdot> b = inv(a) \<cdot> b.\<close>
      have hN_conj: "\<And>g n. g \<in> FP \<Longrightarrow> n \<in> ?N \<Longrightarrow> mulFP (mulFP g n) (invgFP g) \<in> ?N"
        using hN_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
      have "mulFP (mulFP (invgFP ?b) (mulFP ?b (invgFP ?a))) (invgFP (invgFP ?b)) \<in> ?N"
        by (rule hN_conj[OF hinvb_FP hb_inva_N])
      moreover have "mulFP (mulFP (invgFP ?b) (mulFP ?b (invgFP ?a))) (invgFP (invgFP ?b))
          = mulFP (invgFP ?a) ?b"
      proof -
        note hg = hFP_grp[unfolded top1_is_group_on_def]
        note hassoc_raw = hg[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
        note hid_raw = hg[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
        note hinv_raw = hg[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
        \<comment> \<open>inv(b) \<cdot> (b \<cdot> inv(a)) = (inv(b) \<cdot> b) \<cdot> inv(a) by assoc.\<close>
        note s1 = hassoc_raw[rule_format, OF hinvb_FP hb_FP hinva_FP, symmetric]
        note s2 = hinv_raw[rule_format, OF hb_FP, THEN conjunct1]
        note s3 = hid_raw[rule_format, OF hinva_FP, THEN conjunct1]
        have s4: "mulFP (invgFP ?b) (mulFP ?b (invgFP ?a)) = invgFP ?a"
          using s1 s2 s3 by (by100 simp)
        have s5: "invgFP (invgFP ?b) = ?b" by (rule group_inv_inv[OF hFP_grp hb_FP])
        show ?thesis using s4 s5 by (by100 simp)
      qed
      ultimately have h_invab_N: "mulFP (invgFP ?a) ?b \<in> ?N" by (by100 simp)
      \<comment> \<open>Apply normal_coset_eq: coset(a) = coset(b) \<longleftrightarrow> inv(a) \<cdot> b \<in> N.\<close>
      have "top1_group_coset_on FP mulFP ?N ?a = top1_group_coset_on FP mulFP ?N ?b"
        using iffD2[OF normal_coset_eq[OF hFP_grp hN_normal ha_FP hb_FP] h_invab_N] .
      thus "?\<phi>1 ?iU_c = ?\<phi>2 ?iV_c" by (by100 simp)
    qed
    \<comment> \<open>Step 3: By parameterized SvK (Theorem 70.1), get \<Phi>: \<pi>_1(X) \<rightarrow> FP/N.\<close>
    have hPhi: "\<exists>\<Phi>. top1_group_hom_on ?\<pi>X (top1_fundamental_group_mul X TX x0) ?Q ?mulQ \<Phi>
        \<and> (\<forall>a\<in>?\<pi>U. \<Phi> (?hfam 0 a) = ?\<phi>1 a)
        \<and> (\<forall>b\<in>?\<pi>V. \<Phi> (?hfam 1 b) = ?\<phi>2 b)"
    proof -
      \<comment> \<open>Instantiate Theorem_70_1 with H = FP/N.\<close>
      obtain eQ invgQ where hQ_grp_full: "top1_is_group_on ?Q ?mulQ eQ invgQ"
        using quotient_group_is_group[OF hFP_grp hN_normal] by (by100 blast)
      \<comment> \<open>\<phi>1 and \<phi>2 are group homs into Q.\<close>
      \<comment> \<open>\<iota>_0 is a group hom \<pi>U \<rightarrow> FP (from free product) and \<pi>_q is a hom FP \<rightarrow> Q.\<close>
      note hpiq_hom_loc = quotient_projection_properties(1)[OF hFP_grp hN_normal]
      have h\<iota>0_hom: "top1_group_hom_on ?\<pi>U (top1_fundamental_group_mul U ?TU x0) FP mulFP (\<iota>fam 0)"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        moreover have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<forall>y\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V).
            \<iota>fam \<alpha> ((if \<alpha>=0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0) x y)
            = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        ultimately show ?thesis unfolding top1_group_hom_on_def by (by100 force)
      qed
      have h\<iota>1_hom: "top1_group_hom_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0) FP mulFP (\<iota>fam 1)"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        moreover have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<forall>y\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V).
            \<iota>fam \<alpha> ((if \<alpha>=0 then top1_fundamental_group_mul U ?TU x0 else top1_fundamental_group_mul V ?TV x0) x y)
            = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        ultimately show ?thesis unfolding top1_group_hom_on_def by (by100 force)
      qed
      note hcomp0 = group_hom_comp[OF h\<iota>0_hom hpiq_hom_loc]
      note hcomp1 = group_hom_comp[OF h\<iota>1_hom hpiq_hom_loc]
      \<comment> \<open>hcomp0: hom(\<pi>_q \<circ> \<iota>_0). Need: hom(\<lambda>a. \<pi>_q(\<iota>_0 a)) = hom(\<pi>_q \<circ> \<iota>_0).\<close>
      have h\<phi>1_hom: "top1_group_hom_on ?\<pi>U (top1_fundamental_group_mul U ?TU x0) ?Q ?mulQ ?\<phi>1"
        using hcomp0 unfolding comp_def by (by100 simp)
      have h\<phi>2_hom: "top1_group_hom_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0) ?Q ?mulQ ?\<phi>2"
        using hcomp1 unfolding comp_def by (by100 simp)
      from Theorem_70_1_universal_property[OF assms(1-8) hQ_grp_full h\<phi>1_hom h\<phi>2_hom hcompat]
      show ?thesis by (by100 simp)
    qed
    then obtain \<Phi> where h\<Phi>_hom: "top1_group_hom_on ?\<pi>X (top1_fundamental_group_mul X TX x0) ?Q ?mulQ \<Phi>"
        and h\<Phi>_U: "\<forall>a\<in>?\<pi>U. \<Phi> (?hfam 0 a) = ?\<phi>1 a"
        and h\<Phi>_V: "\<forall>b\<in>?\<pi>V. \<Phi> (?hfam 1 b) = ?\<phi>2 b"
      by (by100 blast)
    \<comment> \<open>Step 4: \<Phi> \<circ> j = \<pi>_q (the quotient projection).
       For w \<in> FP, j(w) = j(letters). \<Phi>(j(w)) = product of \<Phi>(j_i(letter)) = \<pi>_q(w).\<close>
    have hPhij: "\<forall>v\<in>FP. \<Phi> (j v) = ?\<pi>_q v"
    proof -
      \<comment> \<open>The agreement set A = {v \<in> FP | \<Phi>(j(v)) = \<pi>_q(v)} contains generators and is a subgroup.\<close>
      let ?A = "{v \<in> FP. \<Phi> (j v) = ?\<pi>_q v}"
      \<comment> \<open>Step 4a: \<Phi>\<circ>j and \<pi>_q agree on generators \<iota>_\<alpha>(x).\<close>
      have hgen_in_A: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V).
          \<iota>fam \<alpha> x \<in> ?A"
      proof (intro ballI)
        fix \<alpha> x assume h\<alpha>: "\<alpha> \<in> {0::nat, 1}"
            and hx: "x \<in> (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)"
        have h\<iota>_FP: "\<iota>fam \<alpha> x \<in> FP"
          using hFP h\<alpha> hx unfolding top1_is_free_product_on_def by (by100 blast)
        have "j (\<iota>fam \<alpha> x) = ?hfam \<alpha> x"
          using hj_ext h\<alpha> hx by (by100 blast)
        hence "\<Phi> (j (\<iota>fam \<alpha> x)) = \<Phi> (?hfam \<alpha> x)" by (by100 simp)
        also have "\<Phi> (?hfam \<alpha> x) = ?\<pi>_q (\<iota>fam \<alpha> x)"
        proof (cases "\<alpha> = 0")
          case True thus ?thesis using hx h\<Phi>_U by (by100 simp)
        next
          case False hence "\<alpha> = 1" using h\<alpha> by (by100 blast)
          thus ?thesis using hx h\<Phi>_V by (by100 simp)
        qed
        finally show "\<iota>fam \<alpha> x \<in> ?A" using h\<iota>_FP by (by100 blast)
      qed
      \<comment> \<open>Step 4b: A contains all generators of FP.\<close>
      have hgens_sub_A: "(\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)) \<subseteq> ?A"
        using hgen_in_A by (by100 blast)
      \<comment> \<open>Step 4c: A is a subgroup of FP (closed under mul and inv).\<close>
      have hA_sub: "?A \<subseteq> FP" by (by100 blast)
      have hA_grp: "top1_is_group_on ?A mulFP eFP invgFP"
      proof -
        note hpiq_hom = quotient_projection_properties(1)[OF hFP_grp hN_normal]
        note hQ_grp' = quotient_group_is_group[OF hFP_grp hN_normal]
        note hg = hFP_grp[unfolded top1_is_group_on_def]
        \<comment> \<open>eFP \<in> A.\<close>
        have he_A: "eFP \<in> ?A"
        proof -
          have he_FP: "eFP \<in> FP" using hg by (by100 blast)
          have "j eFP = ?e_X" by (rule hom_preserves_id[OF hFP_grp h\<pi>X_grp hj_hom])
          hence "\<Phi> (j eFP) = \<Phi> ?e_X" by (by100 simp)
          also have "\<dots> = ?\<pi>_q eFP" by (rule hom_preserves_id[OF h\<pi>X_grp hQ_grp' h\<Phi>_hom])
          finally show ?thesis using he_FP by (by100 blast)
        qed
        \<comment> \<open>Closure under mul.\<close>
        have hmul_cl: "\<And>x y. x \<in> ?A \<Longrightarrow> y \<in> ?A \<Longrightarrow> mulFP x y \<in> ?A"
        proof -
          fix x y assume hx: "x \<in> ?A" and hy: "y \<in> ?A"
          hence hxFP: "x \<in> FP" and hyFP: "y \<in> FP"
              and hx_eq: "\<Phi> (j x) = ?\<pi>_q x" and hy_eq: "\<Phi> (j y) = ?\<pi>_q y" by (by100 blast)+
          have hxy_FP: "mulFP x y \<in> FP" using hg hxFP hyFP by (by100 blast)
          have "j (mulFP x y) = top1_fundamental_group_mul X TX x0 (j x) (j y)"
            using hj_hom hxFP hyFP unfolding top1_group_hom_on_def by (by100 blast)
          hence "\<Phi> (j (mulFP x y)) = \<Phi> (top1_fundamental_group_mul X TX x0 (j x) (j y))"
            by (by100 simp)
          also have "\<dots> = ?mulQ (\<Phi> (j x)) (\<Phi> (j y))"
          proof -
            have "j x \<in> ?\<pi>X" using hj_hom hxFP unfolding top1_group_hom_on_def by (by100 blast)
            moreover have "j y \<in> ?\<pi>X" using hj_hom hyFP unfolding top1_group_hom_on_def by (by100 blast)
            ultimately show ?thesis using h\<Phi>_hom unfolding top1_group_hom_on_def by (by100 blast)
          qed
          also have "\<dots> = ?mulQ (?\<pi>_q x) (?\<pi>_q y)" using hx_eq hy_eq by (by100 simp)
          also have "\<dots> = ?\<pi>_q (mulFP x y)"
            using hpiq_hom hxFP hyFP unfolding top1_group_hom_on_def by (by100 simp)
          finally show "mulFP x y \<in> ?A" using hxy_FP by (by100 blast)
        qed
        \<comment> \<open>Closure under inv.\<close>
        have hinv_cl: "\<And>x. x \<in> ?A \<Longrightarrow> invgFP x \<in> ?A"
        proof -
          fix x assume hx: "x \<in> ?A"
          hence hxFP: "x \<in> FP" and hx_eq: "\<Phi> (j x) = ?\<pi>_q x" by (by100 blast)+
          have hinvx_FP: "invgFP x \<in> FP" using hg hxFP by (by100 blast)
          have hjx: "j x \<in> ?\<pi>X" using hj_hom hxFP unfolding top1_group_hom_on_def by (by100 blast)
          \<comment> \<open>Chain: \<Phi>(j(inv x)) = \<Phi>(inv_\<pi>X(j x)) = inv_Q(\<Phi>(j x)) = inv_Q(\<pi>_q x) = \<pi>_q(inv x).\<close>
          note s1 = hom_preserves_inv[OF hFP_grp h\<pi>X_grp hj_hom hxFP]
          \<comment> \<open>s1: j(invgFP x) = invg_\<pi>X(j x)\<close>
          note s2 = hom_preserves_inv[OF h\<pi>X_grp hQ_grp' h\<Phi>_hom hjx]
          \<comment> \<open>s2: \<Phi>(invg_\<pi>X(j x)) = invg_Q(\<Phi>(j x))\<close>
          note s3 = hom_preserves_inv[OF hFP_grp hQ_grp' hpiq_hom hxFP]
          \<comment> \<open>s3: \<pi>_q(invgFP x) = invg_Q(\<pi>_q x)\<close>
          have "\<Phi> (j (invgFP x)) = ?\<pi>_q (invgFP x)"
            using s1 s2 s3 hx_eq by (by100 simp)
          thus "invgFP x \<in> ?A" using hinvx_FP by (by100 blast)
        qed
        \<comment> \<open>Assemble group axioms.\<close>
        show ?thesis unfolding top1_is_group_on_def
        proof (intro conjI)
          show "eFP \<in> ?A" by (rule he_A)
          show "\<forall>x\<in>?A. \<forall>y\<in>?A. mulFP x y \<in> ?A" using hmul_cl by (by100 blast)
          show "\<forall>x\<in>?A. invgFP x \<in> ?A" using hinv_cl by (by100 blast)
          show "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. mulFP (mulFP x y) z = mulFP x (mulFP y z)"
            using hg by (by100 blast)
          show "\<forall>x\<in>?A. mulFP eFP x = x \<and> mulFP x eFP = x"
            using hg by (by100 blast)
          show "\<forall>x\<in>?A. mulFP (invgFP x) x = eFP \<and> mulFP x (invgFP x) = eFP"
            using hg by (by100 blast)
        qed
      qed
      \<comment> \<open>Step 4d: FP = subgroup_generated(generators) \<subseteq> A, hence A = FP.\<close>
      have hFP_gen: "FP = top1_subgroup_generated_on FP mulFP eFP invgFP
          (\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V))"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      have "top1_subgroup_generated_on FP mulFP eFP invgFP
          (\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)) \<subseteq> ?A"
        by (rule subgroup_generated_minimal[OF hgens_sub_A hA_sub hA_grp])
      hence "FP \<subseteq> ?A" using hFP_gen by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 5: Conclude w \<in> N.\<close>
    have "\<Phi> (j w) = ?\<pi>_q w" using hPhij hwFP by (by100 blast)
    moreover have "\<Phi> (j w) = \<Phi> ?e_X" using hjw by (by100 simp)
    moreover have "\<Phi> ?e_X = ?\<pi>_q eFP"
    proof -
      note hQ_grp' = quotient_group_is_group[OF hFP_grp hN_normal]
      show ?thesis by (rule hom_preserves_id[OF h\<pi>X_grp hQ_grp' h\<Phi>_hom])
    qed
    ultimately have "?\<pi>_q w = ?\<pi>_q eFP" by (by100 simp)
    \<comment> \<open>Same coset means w \<cdot> eFP\<inverse> = w \<in> N.\<close>
    \<comment> \<open>same coset \<Rightarrow> inv(eFP) \<cdot> w \<in> N \<Rightarrow> w \<in> N (since inv(e) = e and e \<cdot> w = w).\<close>
    have heFP_FP: "eFP \<in> FP"
      using hFP_grp unfolding top1_is_group_on_def by (by100 blast)
    note hcoset_iff = normal_coset_eq[OF hFP_grp hN_normal heFP_FP hwFP]
    \<comment> \<open>hcoset_iff: coset(eFP) = coset(w) \<longleftrightarrow> mulFP(invgFP eFP) w \<in> N\<close>
    have "top1_group_coset_on FP mulFP ?N eFP = top1_group_coset_on FP mulFP ?N w"
      using \<open>?\<pi>_q w = ?\<pi>_q eFP\<close> by (by100 simp)
    hence "mulFP (invgFP eFP) w \<in> ?N" using hcoset_iff by (by100 blast)
    moreover have "mulFP (invgFP eFP) w = w"
    proof -
      have "invgFP eFP = eFP"
      proof -
        note hgrp_raw = hFP_grp[unfolded top1_is_group_on_def]
        have he_FP: "eFP \<in> FP" using hgrp_raw by (by100 blast)
        have "mulFP (invgFP eFP) eFP = eFP" using hgrp_raw he_FP by (by100 blast)
        moreover have "invgFP eFP \<in> FP" using hgrp_raw he_FP by (by100 blast)
        moreover have "mulFP (invgFP eFP) eFP = invgFP eFP"
          using hgrp_raw \<open>invgFP eFP \<in> FP\<close> by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "mulFP eFP w = w"
        using hFP_grp hwFP unfolding top1_is_group_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    ultimately show "w \<in> ?N" by (by100 simp)
  qed
  have hj_ker: "top1_group_kernel_on FP (top1_fundamental_group_id X TX x0) j = ?N"
    using hN_sub_ker hker_sub_N by (by100 blast)
  \<comment> \<open>Step 4: Now obtain j with all three properties for first_isomorphism_theorem.\<close>
  show ?thesis
    by (rule first_isomorphism_theorem_forward[OF hFP_grp hN_normal h\<pi>X_grp hj_hom hj_surj hj_ker])
qed

text \<open>Corollary 70.3 (Munkres): If U \<inter> V is simply connected, then
  \<pi>_1(X) \<cong> \<pi>_1(U) * \<pi>_1(V) (free product, no amalgamation).\<close>
corollary Corollary_70_3_simply_connected_intersection:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<exists>(FP::'f set) mulFP.
           top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0) FP mulFP
         \<and> (\<exists>eFP invgFP \<iota>fam.
              top1_is_free_product_on FP mulFP eFP invgFP
                (\<lambda>i::nat. if i = 0
                   then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                   else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
                (\<lambda>i. if i = 0
                   then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                   else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
                \<iota>fam {0, 1})"
  \<comment> \<open>UNPROVABLE: same type variable issue as Theorem_70_2_SvK.\<close>
  oops

text \<open>Helper: free product G * {e} = \<iota>_0(G), i.e. when one factor is trivial,
  the free product reduces to the other factor via the canonical embedding.\<close>
lemma free_product_trivial_factor_surj:
  assumes hFP: "top1_is_free_product_on FP mulFP eFP invgFP GG mulGG \<iota>fam {0::nat, 1}"
      and hGG1_triv: "GG 1 = {eGG1}"
      and hGG1_grp: "top1_is_group_on (GG 1) (mulGG 1) eGG1 invgGG1"
      and hGG0_grp: "top1_is_group_on (GG 0) (mulGG 0) eGG0 invgGG0"
  shows "FP = \<iota>fam 0 ` (GG 0)"
proof -
  have hG: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> FP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_hom: "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
      \<iota>fam \<alpha> (mulGG \<alpha> x y) = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hgen: "FP = top1_subgroup_generated_on FP mulFP eFP invgFP
      (\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` GG \<alpha>)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  \<comment> \<open>\<iota>_1(eGG1) = eFP (identity maps to identity under homomorphism).\<close>
  have heGG1: "eGG1 \<in> GG 1" using hGG1_grp unfolding top1_is_group_on_def by (by100 blast)
  have h\<iota>1_e: "\<iota>fam 1 eGG1 = eFP"
  proof -
    have "mulFP (\<iota>fam 1 eGG1) (\<iota>fam 1 eGG1) = \<iota>fam 1 (mulGG 1 eGG1 eGG1)"
      using h\<iota>_hom heGG1 by (by100 force)
    moreover have "mulGG 1 eGG1 eGG1 = eGG1"
      using hGG1_grp heGG1 unfolding top1_is_group_on_def by (by100 blast)
    ultimately have hidem: "mulFP (\<iota>fam 1 eGG1) (\<iota>fam 1 eGG1) = \<iota>fam 1 eGG1" by (by100 simp)
    have h_in: "\<iota>fam 1 eGG1 \<in> FP" using h\<iota>_in heGG1 by (by100 force)
    \<comment> \<open>Idempotent in group = identity.\<close>
    have "mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1)) = eFP"
      by (rule group_inv_right[OF hG h_in])
    have "mulFP (mulFP (\<iota>fam 1 eGG1) (\<iota>fam 1 eGG1)) (invgFP (\<iota>fam 1 eGG1))
        = mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1))"
      using hidem by (by100 simp)
    moreover have hinv_in: "invgFP (\<iota>fam 1 eGG1) \<in> FP"
      by (rule group_inv_closed[OF hG h_in])
    moreover have "mulFP (mulFP (\<iota>fam 1 eGG1) (\<iota>fam 1 eGG1)) (invgFP (\<iota>fam 1 eGG1))
        = mulFP (\<iota>fam 1 eGG1) (mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1)))"
      using hG h_in hinv_in unfolding top1_is_group_on_def by (by100 force)
    ultimately have "mulFP (\<iota>fam 1 eGG1) (mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1)))
        = mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1))" by (by100 simp)
    hence "mulFP (\<iota>fam 1 eGG1) eFP = eFP"
      using \<open>mulFP (\<iota>fam 1 eGG1) (invgFP (\<iota>fam 1 eGG1)) = eFP\<close> by (by100 simp)
    thus ?thesis using group_id_right[OF hG h_in] by (by100 simp)
  qed
  \<comment> \<open>The generating set = \<iota>_0(GG 0) \<union> {eFP}.\<close>
  have hgen_simp: "(\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` GG \<alpha>) = \<iota>fam 0 ` GG 0 \<union> {\<iota>fam 1 eGG1}"
  proof -
    have "(\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` GG \<alpha>) = \<iota>fam 0 ` GG 0 \<union> \<iota>fam 1 ` GG 1"
      by (by100 force)
    also have "\<iota>fam 1 ` GG 1 = {\<iota>fam 1 eGG1}" using hGG1_triv by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>eFP \<in> \<iota>_0(GG 0) (because \<iota>_0(eGG0) = eFP).\<close>
  have heGG0: "eGG0 \<in> GG 0" using hGG0_grp unfolding top1_is_group_on_def by (by100 blast)
  have h\<iota>0_e: "\<iota>fam 0 eGG0 = eFP"
  proof -
    have "mulFP (\<iota>fam 0 eGG0) (\<iota>fam 0 eGG0) = \<iota>fam 0 (mulGG 0 eGG0 eGG0)"
      using h\<iota>_hom heGG0 by (by100 force)
    moreover have "mulGG 0 eGG0 eGG0 = eGG0"
      using hGG0_grp heGG0 unfolding top1_is_group_on_def by (by100 blast)
    ultimately have hidem: "mulFP (\<iota>fam 0 eGG0) (\<iota>fam 0 eGG0) = \<iota>fam 0 eGG0" by (by100 simp)
    have h_in: "\<iota>fam 0 eGG0 \<in> FP" using h\<iota>_in heGG0 by (by100 force)
    have "mulFP (\<iota>fam 0 eGG0) (invgFP (\<iota>fam 0 eGG0)) = eFP"
      by (rule group_inv_right[OF hG h_in])
    have hinv_in: "invgFP (\<iota>fam 0 eGG0) \<in> FP" by (rule group_inv_closed[OF hG h_in])
    have "mulFP (mulFP (\<iota>fam 0 eGG0) (\<iota>fam 0 eGG0)) (invgFP (\<iota>fam 0 eGG0))
        = mulFP (\<iota>fam 0 eGG0) (mulFP (\<iota>fam 0 eGG0) (invgFP (\<iota>fam 0 eGG0)))"
      using hG h_in hinv_in unfolding top1_is_group_on_def by (by100 force)
    hence "mulFP (\<iota>fam 0 eGG0) (mulFP (\<iota>fam 0 eGG0) (invgFP (\<iota>fam 0 eGG0)))
        = mulFP (\<iota>fam 0 eGG0) (invgFP (\<iota>fam 0 eGG0))"
      using hidem by (by100 simp)
    hence "mulFP (\<iota>fam 0 eGG0) eFP = eFP"
      using \<open>mulFP (\<iota>fam 0 eGG0) (invgFP (\<iota>fam 0 eGG0)) = eFP\<close> by (by100 simp)
    thus ?thesis using group_id_right[OF hG h_in] by (by100 simp)
  qed
  have heFP_in: "eFP \<in> \<iota>fam 0 ` GG 0" using h\<iota>0_e heGG0 by (by100 blast)
  \<comment> \<open>Generating set = \<iota>_0(GG 0) (since eFP \<in> \<iota>_0(GG 0)).\<close>
  have hgen_eq: "(\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` GG \<alpha>) = \<iota>fam 0 ` GG 0"
  proof -
    have "(\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` GG \<alpha>) = \<iota>fam 0 ` GG 0 \<union> {\<iota>fam 1 eGG1}" by (rule hgen_simp)
    also have "\<iota>fam 1 eGG1 = eFP" by (rule h\<iota>1_e)
    also have "\<iota>fam 0 ` GG 0 \<union> {eFP} = \<iota>fam 0 ` GG 0" using heFP_in by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>\<iota>_0(GG 0) is a subgroup of FP (image of group hom).\<close>
  have h\<iota>0_hom: "top1_group_hom_on (GG 0) (mulGG 0) FP mulFP (\<iota>fam 0)"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> GG 0" thus "\<iota>fam 0 x \<in> FP" using h\<iota>_in by (by100 force)
  next
    fix x y assume "x \<in> GG 0" "y \<in> GG 0"
    thus "\<iota>fam 0 (mulGG 0 x y) = mulFP (\<iota>fam 0 x) (\<iota>fam 0 y)"
      using h\<iota>_hom by (by100 force)
  qed
  have h\<iota>0_img_grp: "top1_is_group_on (\<iota>fam 0 ` GG 0) mulFP eFP invgFP"
    by (rule hom_image_is_subgroup[OF hGG0_grp hG h\<iota>0_hom])
  \<comment> \<open>subgroup_generated of a subgroup is itself.\<close>
  have h\<iota>0_sub: "\<iota>fam 0 ` GG 0 \<subseteq> FP"
  proof (rule image_subsetI)
    fix x assume "x \<in> GG 0" thus "\<iota>fam 0 x \<in> FP" using h\<iota>_in by (by100 force)
  qed
  have "top1_subgroup_generated_on FP mulFP eFP invgFP (\<iota>fam 0 ` GG 0) = \<iota>fam 0 ` GG 0"
  proof (rule antisym)
    show "top1_subgroup_generated_on FP mulFP eFP invgFP (\<iota>fam 0 ` GG 0) \<subseteq> \<iota>fam 0 ` GG 0"
      by (rule subgroup_generated_minimal[OF _ h\<iota>0_sub h\<iota>0_img_grp]) (by100 blast)
    show "\<iota>fam 0 ` GG 0 \<subseteq> top1_subgroup_generated_on FP mulFP eFP invgFP (\<iota>fam 0 ` GG 0)"
    proof (rule image_subsetI)
      fix x assume "x \<in> GG 0"
      hence "\<iota>fam 0 x \<in> \<iota>fam 0 ` GG 0" by (by100 blast)
      thus "\<iota>fam 0 x \<in> top1_subgroup_generated_on FP mulFP eFP invgFP (\<iota>fam 0 ` GG 0)"
        by (rule subgroup_generated_contains[OF hG h\<iota>0_sub])
    qed
  qed
  thus ?thesis using hgen hgen_eq by (by100 simp)
qed

text \<open>Helper: preimage of a normal subgroup under a group hom is normal.\<close>
lemma preimage_normal_subgroup:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hf: "top1_group_hom_on G mul H mulH f"
      and hK: "top1_normal_subgroup_on H mulH eH invgH K"
  shows "top1_normal_subgroup_on G mul e invg {g \<in> G. f g \<in> K}"
proof -
  let ?P = "{g \<in> G. f g \<in> K}"
  have hKsub: "K \<subseteq> H" using hK unfolding top1_normal_subgroup_on_def top1_is_group_on_def
    by (by100 blast)
  have hK_grp: "top1_is_group_on K mulH eH invgH"
    using hK unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hf_e: "f e = eH" by (rule hom_preserves_id[OF hG hH hf])
  show ?thesis unfolding top1_normal_subgroup_on_def
  proof (intro conjI)
  show "?P \<subseteq> G"
  proof (rule subsetI)
    fix x assume "x \<in> ?P" thus "x \<in> G" by (by100 blast)
  qed
  next
  show "top1_is_group_on ?P mul e invg" unfolding top1_is_group_on_def
  proof (intro conjI ballI)
    \<comment> \<open>Identity: e \<in> P since f(e) = eH \<in> K.\<close>
    show "e \<in> ?P"
    proof -
      have "e \<in> G" by (rule group_e_mem[OF hG])
      moreover have "f e = eH" by (rule hf_e)
      moreover have "eH \<in> K" by (rule group_e_mem[OF hK_grp])
      ultimately show ?thesis by (by100 blast)
    qed
  next
    \<comment> \<open>Closure: f(xy) = f(x)f(y) \<in> K.\<close>
    fix x y assume hx: "x \<in> ?P" and hy: "y \<in> ?P"
    have hxG: "x \<in> G" and hfxK: "f x \<in> K" using hx by (by100 blast)+
    have hyG: "y \<in> G" and hfyK: "f y \<in> K" using hy by (by100 blast)+
    have hxyG: "mul x y \<in> G" by (rule group_mul_closed[OF hG hxG hyG])
    have hfxy: "f (mul x y) = mulH (f x) (f y)"
      using hf hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
    have "mulH (f x) (f y) \<in> K"
      using hK_grp hfxK hfyK unfolding top1_is_group_on_def by (by100 blast)
    hence "f (mul x y) \<in> K" using hfxy by (by100 simp)
    thus "mul x y \<in> ?P" using hxyG by (by100 blast)
  next
    \<comment> \<open>Inverse: f(x\<inverse>) = f(x)\<inverse> \<in> K.\<close>
    fix x assume hx: "x \<in> ?P"
    have hxG: "x \<in> G" and hfxK: "f x \<in> K" using hx by (by100 blast)+
    have hinvG: "invg x \<in> G" by (rule group_inv_closed[OF hG hxG])
    have hfinv: "f (invg x) = invgH (f x)"
      by (rule hom_preserves_inv[OF hG hH hf hxG])
    have "invgH (f x) \<in> K"
      using hK_grp hfxK unfolding top1_is_group_on_def by (by100 blast)
    hence "f (invg x) \<in> K" using hfinv by (by100 simp)
    thus "invg x \<in> ?P" using hinvG by (by100 blast)
  next
    \<comment> \<open>Associativity: inherited from G.\<close>
    fix x y z assume "x \<in> ?P" "y \<in> ?P" "z \<in> ?P"
    hence "x \<in> G" "y \<in> G" "z \<in> G" by (by100 blast)+
    thus "mul (mul x y) z = mul x (mul y z)"
      using hG unfolding top1_is_group_on_def by (by100 blast)
  next
    \<comment> \<open>Left identity.\<close>
    fix x assume "x \<in> ?P" hence "x \<in> G" by (by100 blast)
    thus "mul e x = x" using group_id_left[OF hG] by (by100 blast)
  next
    \<comment> \<open>Right inverse.\<close>
    fix x assume "x \<in> ?P" hence "x \<in> G" by (by100 blast)
    thus "mul x (invg x) = e" by (rule group_inv_right[OF hG])
  next
    \<comment> \<open>Left inverse.\<close>
    fix x assume "x \<in> ?P" hence "x \<in> G" by (by100 blast)
    have "invg x \<in> G" by (rule group_inv_closed[OF hG \<open>x \<in> G\<close>])
    show "mul (invg x) x = e"
      using hG \<open>x \<in> G\<close> \<open>invg x \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
  next
    \<comment> \<open>Right identity.\<close>
    fix x assume "x \<in> ?P" hence "x \<in> G" by (by100 blast)
    thus "mul x e = x" using group_id_right[OF hG] by (by100 blast)
  qed
next
  \<comment> \<open>Conjugation closure: g \<in> G, n \<in> P \<Rightarrow> gng\<inverse> \<in> P.\<close>
  show "\<forall>g\<in>G. \<forall>n\<in>?P. mul (mul g n) (invg g) \<in> ?P"
  proof (intro ballI)
    fix g n assume hg: "g \<in> G" and hn: "n \<in> ?P"
    have hnG: "n \<in> G" and hfnK: "f n \<in> K" using hn by (by100 blast)+
    have "invg g \<in> G" by (rule group_inv_closed[OF hG hg])
    have hgn: "mul g n \<in> G" by (rule group_mul_closed[OF hG hg hnG])
    have hconj_G: "mul (mul g n) (invg g) \<in> G"
      by (rule group_mul_closed[OF hG hgn \<open>invg g \<in> G\<close>])
    \<comment> \<open>f((gn)g\<inverse>) = f(gn)f(g\<inverse>) = (f(g)f(n))(f(g)\<inverse>) \<in> K (K is normal).\<close>
    have "f (mul (mul g n) (invg g)) = mulH (f (mul g n)) (f (invg g))"
      using hf hgn \<open>invg g \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "f (mul g n) = mulH (f g) (f n)"
      using hf hg hnG unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "f (invg g) = invgH (f g)"
      by (rule hom_preserves_inv[OF hG hH hf hg])
    ultimately have hf_conj: "f (mul (mul g n) (invg g))
        = mulH (mulH (f g) (f n)) (invgH (f g))" by (by100 simp)
    have hfgH: "f g \<in> H" using hf hg unfolding top1_group_hom_on_def by (by100 blast)
    have hfnH: "f n \<in> H" using hfnK hKsub by (by100 blast)
    have "mulH (mulH (f g) (f n)) (invgH (f g)) \<in> K"
      using hK hfgH hfnK unfolding top1_normal_subgroup_on_def by (by100 blast)
    hence "f (mul (mul g n) (invg g)) \<in> K" using hf_conj by (by100 simp)
    thus "mul (mul g n) (invg g) \<in> ?P" using hconj_G by (by100 blast)
  qed
  qed
qed

text \<open>Corollary 70.4 (Munkres): If V is simply connected, then
  \<pi>_1(X) \<cong> \<pi>_1(U) / N where N is the normal closure of the image of
  the inclusion \<pi>_1(U \<inter> V) \<hookrightarrow> \<pi>_1(U).\<close>
text \<open>Helper: simply connected implies trivial fundamental group.\<close>
lemma simply_connected_trivial_carrier:
  assumes hsc: "top1_simply_connected_on X TX"
      and hx0: "x0 \<in> X"
  shows "top1_fundamental_group_carrier X TX x0 = {top1_fundamental_group_id X TX x0}"
proof (rule set_eqI)
  have hTX: "is_topology_on X TX"
    using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
  fix c show "c \<in> top1_fundamental_group_carrier X TX x0 \<longleftrightarrow>
      c \<in> {top1_fundamental_group_id X TX x0}"
  proof
    assume hc: "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hf_nul: "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      using hsc hx0 hf unfolding top1_simply_connected_on_def by (by100 blast)
    have "c = {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"
    proof (rule set_eqI)
      fix g show "g \<in> c \<longleftrightarrow> g \<in> {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"
      proof
        assume "g \<in> c"
        hence "top1_loop_equiv_on X TX x0 f g" using hc_eq by (by100 blast)
        hence "top1_path_homotopic_on X TX x0 x0 f g"
          unfolding top1_loop_equiv_on_def by (by100 blast)
        have hfg: "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) g"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX
                Lemma_51_1_path_homotopic_sym[OF hf_nul]
                \<open>top1_path_homotopic_on X TX x0 x0 f g\<close>])
        have hg_loop: "top1_is_loop_on X TX x0 g"
          using \<open>g \<in> c\<close> hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
        show "g \<in> {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"
          unfolding top1_loop_equiv_on_def
          using hfg hg_loop top1_constant_path_is_loop[OF hTX hx0] by (by100 blast)
      next
        assume "g \<in> {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"
        hence hcg: "top1_loop_equiv_on X TX x0 (top1_constant_path x0) g" by (by100 blast)
        hence "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) g"
          unfolding top1_loop_equiv_on_def by (by100 blast)
        have "top1_path_homotopic_on X TX x0 x0 f g"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX hf_nul
                \<open>top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) g\<close>])
        have hg_loop: "top1_is_loop_on X TX x0 g"
          using hcg unfolding top1_loop_equiv_on_def by (by100 blast)
        show "g \<in> c" using hc_eq unfolding top1_loop_equiv_on_def
          using \<open>top1_path_homotopic_on X TX x0 x0 f g\<close> hf hg_loop by (by100 blast)
      qed
    qed
    thus "c \<in> {top1_fundamental_group_id X TX x0}"
      unfolding top1_fundamental_group_id_def by (by100 blast)
  next
    assume "c \<in> {top1_fundamental_group_id X TX x0}"
    hence "c = top1_fundamental_group_id X TX x0" by (by100 blast)
    thus "c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def top1_fundamental_group_id_def
      using top1_constant_path_is_loop[OF hTX hx0]
            top1_loop_equiv_on_refl[OF top1_constant_path_is_loop[OF hTX hx0]] by (by100 blast)
  qed
qed

corollary Corollary_70_4_simply_connected_V:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_mul X TX x0)
    (top1_quotient_group_carrier_on
       (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
       (top1_fundamental_group_mul U (subspace_topology X TX U) x0)
       (top1_normal_subgroup_generated_on
          (top1_fundamental_group_carrier U (subspace_topology X TX U) x0)
          (top1_fundamental_group_mul U (subspace_topology X TX U) x0)
          (top1_fundamental_group_id U (subspace_topology X TX U) x0)
          (top1_fundamental_group_invg U (subspace_topology X TX U) x0)
          (top1_fundamental_group_induced_on
             (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
             U (subspace_topology X TX U) x0 (\<lambda>x. x)
           ` top1_fundamental_group_carrier (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0)))
    (top1_quotient_group_mul_on
       (top1_fundamental_group_mul U (subspace_topology X TX U) x0))"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU x0"
  let ?mulU = "top1_fundamental_group_mul U ?TU x0"
  let ?eU = "top1_fundamental_group_id U ?TU x0"
  let ?invgU = "top1_fundamental_group_invg U ?TU x0"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV x0"
  let ?\<pi>X = "top1_fundamental_group_carrier X TX x0"
  let ?mulX = "top1_fundamental_group_mul X TX x0"
  let ?eX = "top1_fundamental_group_id X TX x0"
  let ?invgX = "top1_fundamental_group_invg X TX x0"
  let ?j_U = "top1_fundamental_group_induced_on U ?TU x0 X TX x0 (\<lambda>x. x)"
  let ?j_UV_U = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x)"
  let ?N = "top1_normal_subgroup_generated_on ?\<pi>U ?mulU ?eU ?invgU
      (?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)"
  \<comment> \<open>Basic topology facts.\<close>
  have hTopX: "is_topology_on X TX" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hUsub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
  have hTopU: "is_topology_on U ?TU" by (rule subspace_topology_is_topology_on[OF hTopX hUsub])
  have hTopV: "is_topology_on V ?TV" by (rule subspace_topology_is_topology_on[OF hTopX hVsub])
  have hx0_U: "x0 \<in> U" using assms(8) by (by100 blast)
  have hx0_V: "x0 \<in> V" using assms(8) by (by100 blast)
  have hx0_X: "x0 \<in> X" using assms(8) assms(4) by (by100 blast)
  \<comment> \<open>Step 1: V is simply connected \<Rightarrow> \<pi>_1(V) = {e_V}.\<close>
  have hV_pc: "top1_path_connected_on V ?TV"
    using assms(7) unfolding top1_simply_connected_on_def by (by100 blast)
  have hPiV_trivial: "?\<pi>V = {top1_fundamental_group_id V ?TV x0}"
    by (rule simply_connected_trivial_carrier[OF assms(7) hx0_V])
  \<comment> \<open>Step 2: Group structures.\<close>
  have h\<pi>U_grp: "top1_is_group_on ?\<pi>U ?mulU ?eU ?invgU"
    by (rule top1_fundamental_group_is_group[OF hTopU hx0_U])
  have h\<pi>X_grp: "top1_is_group_on ?\<pi>X ?mulX ?eX ?invgX"
    by (rule top1_fundamental_group_is_group[OF hTopX hx0_X])
  \<comment> \<open>Step 3: j_U is a group homomorphism.\<close>
  have hincl_U: "top1_continuous_map_on U ?TU X TX (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on U (subspace_topology X TX U) X TX (\<lambda>x. x)"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopX, unfolded id_def]]) (rule hUsub)
    thus ?thesis by (by100 simp)
  qed
  have hj_U_hom: "top1_group_hom_on ?\<pi>U ?mulU ?\<pi>X ?mulX ?j_U"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTopU hTopX hx0_U hx0_X hincl_U])
       (by100 simp)
  \<comment> \<open>Step 4: j_U is surjective. Use SvK + trivial \<pi>_1(V).\<close>
  \<comment> \<open>Get the free product and apply SvK parameterized.\<close>
  have h\<pi>U_GG: "top1_is_group_on ?\<pi>U ?mulU ?eU ?invgU"
    by (rule h\<pi>U_grp)
  have hV_eV: "top1_fundamental_group_id V ?TV x0 \<in> ?\<pi>V"
    using top1_fundamental_group_is_group[OF hTopV hx0_V] unfolding top1_is_group_on_def
    by (by100 blast)
  have h\<pi>V_GG: "top1_is_group_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0)
      (top1_fundamental_group_id V ?TV x0) (top1_fundamental_group_invg V ?TV x0)"
    by (rule top1_fundamental_group_is_group[OF hTopV hx0_V])
  have hGG_grps: "\<forall>\<alpha>\<in>{0::nat,1}. top1_is_group_on
      (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
      (if \<alpha> = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
      (if \<alpha> = 0 then ?eU else top1_fundamental_group_id V ?TV x0)
      (if \<alpha> = 0 then ?invgU else top1_fundamental_group_invg V ?TV x0)"
  proof (intro ballI)
    fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
    hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
    thus "top1_is_group_on
        (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
        (if \<alpha> = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
        (if \<alpha> = 0 then ?eU else top1_fundamental_group_id V ?TV x0)
        (if \<alpha> = 0 then ?invgU else top1_fundamental_group_invg V ?TV x0)"
    proof
      assume "\<alpha> = 0" thus ?thesis using h\<pi>U_grp by (by100 simp)
    next
      assume "\<alpha> = 1" thus ?thesis using h\<pi>V_GG by (by100 simp)
    qed
  qed
  obtain FP :: "(nat \<times> (real \<Rightarrow> 'a) set) list set" and mulFP eFP invgFP \<iota>fam where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V)
        (\<lambda>i. if i = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
        \<iota>fam {0,1}"
  proof -
    from Theorem_68_2_free_product_exists[OF hGG_grps]
    show ?thesis using that by blast
  qed
  \<comment> \<open>Apply SvK parameterized: \<pi>_1(X) \<cong> FP/N'.\<close>
  have hSvK: "top1_groups_isomorphic_on ?\<pi>X ?mulX
      (top1_quotient_group_carrier_on FP mulFP
         (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
            { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
                     (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
             | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }))
      (top1_quotient_group_mul_on mulFP)"
    by (rule Theorem_70_2_SvK_parameterized[OF assms(1-5) assms(6) hV_pc assms(8) hFP])
  \<comment> \<open>Step 4: FP = \<iota>_0(\<pi>_1(U)) since \<pi>_1(V) = {e_V}.
     (Follows from free_product_trivial_factor_surj + if-branch simplification.)\<close>
  have hFP_eq: "FP = \<iota>fam 0 ` ?\<pi>U"
  proof -
    \<comment> \<open>Reformulate FP with explicit factor groups (avoiding if-branches).\<close>
    let ?GG = "\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V"
    let ?mGG = "\<lambda>i::nat. if i = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0"
    have hGG0: "?GG 0 = ?\<pi>U" by (by100 simp)
    have hGG1: "?GG 1 = ?\<pi>V" by (by100 simp)
    have hmGG0: "?mGG 0 = ?mulU" by (by100 simp)
    have hmGG1: "?mGG 1 = top1_fundamental_group_mul V ?TV x0" by (by100 simp)
    \<comment> \<open>FP = subgroup_generated(union of embeddings).\<close>
    have hgen: "FP = top1_subgroup_generated_on FP mulFP eFP invgFP (\<Union>\<alpha>\<in>{0::nat, 1}. \<iota>fam \<alpha> ` ?GG \<alpha>)"
      using hFP unfolding top1_is_free_product_on_def by (by100 blast)
    \<comment> \<open>GG 1 = {\<pi>_1(V)} = {e_V}.\<close>
    have hGG1_triv: "?GG 1 = {top1_fundamental_group_id V ?TV x0}"
      using hPiV_trivial hGG1 by (by100 simp)
    \<comment> \<open>Apply the general lemma.\<close>
    have hgr1: "top1_is_group_on
        (if (1::nat) = 0 then ?\<pi>U else ?\<pi>V)
        (if (1::nat) = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
        (top1_fundamental_group_id V ?TV x0) (top1_fundamental_group_invg V ?TV x0)"
    proof -
      have "(1::nat) \<noteq> 0" by (by100 simp)
      hence "(if (1::nat) = 0 then ?\<pi>U else ?\<pi>V) = ?\<pi>V" by (by100 simp)
      moreover have "(if (1::nat) = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
          = top1_fundamental_group_mul V ?TV x0" by (by100 simp)
      ultimately show ?thesis using h\<pi>V_GG by (by100 simp)
    qed
    have hgr0: "top1_is_group_on
        (if (0::nat) = 0 then ?\<pi>U else ?\<pi>V)
        (if (0::nat) = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
        ?eU ?invgU"
    proof -
      have "(if (0::nat) = 0 then ?\<pi>U else ?\<pi>V) = ?\<pi>U" by (by100 simp)
      moreover have "(if (0::nat) = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0) = ?mulU"
        by (by100 simp)
      ultimately show ?thesis using h\<pi>U_GG by (by100 simp)
    qed
    have "FP = \<iota>fam 0 ` (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V) 0"
      by (rule free_product_trivial_factor_surj[OF hFP hGG1_triv hgr1 hgr0])
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 5: Compose isomorphisms. SvK gives \<pi>_1(X) \<cong> FP/N'.
     When \<pi>_1(V) = {e_V}, FP/N' \<cong> \<pi>_1(U)/N (relators simplify, \<iota>_0 is isomorphism).
     Composition: \<pi>_1(X) \<cong> FP/N' \<cong> \<pi>_1(U)/N.\<close>
  \<comment> \<open>The quotient isomorphism FP/N' \<cong> \<pi>_1(U)/N follows from:
     (a) \<iota>_0: \<pi>_1(U) \<rightarrow> FP is bijective (FP = \<iota>_0(\<pi>_1(U)))
     (b) the relators in N' become \<iota>_0(generators of N) when \<pi>_1(V) = {e_V}
     (c) so FP/N' = \<iota>_0(\<pi>_1(U))/\<iota>_0(N) \<cong> \<pi>_1(U)/N\<close>
  \<comment> \<open>Step 5b: Construct \<psi>: FP \<rightarrow> \<pi>_1(U)/N via extension property.
     \<psi>(\<iota>_0(u)) = [u]_N, \<psi>(\<iota>_1(v)) = e_Q. Then surj, ker = N', 1st iso thm.\<close>
  let ?N' = "top1_normal_subgroup_generated_on FP mulFP eFP invgFP
      { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
  have hN_normal_U: "top1_normal_subgroup_on ?\<pi>U ?mulU ?eU ?invgU ?N"
  proof -
    have hgens_sub_loc: "?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 \<subseteq> ?\<pi>U"
    proof (rule image_subsetI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
      have hUV_sub': "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
      have hTUV': "is_topology_on (U \<inter> V) ?TUV"
        by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub'])
      have hx0_UV': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
      have hincl': "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
      proof -
        have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF
                top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
        moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
          by (rule subspace_topology_trans) (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
          (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U ?mulU ?j_UV_U"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopU hx0_UV' hx0_U hincl'])
           (by100 simp)
      thus "?j_UV_U c \<in> ?\<pi>U" using hc unfolding top1_group_hom_on_def by (by100 blast)
    qed
    show ?thesis by (rule normal_subgroup_generated_is_normal[OF h\<pi>U_grp hgens_sub_loc])
  qed
  \<comment> \<open>Quotient group \<pi>_1(U)/N.\<close>
  let ?Q = "top1_quotient_group_carrier_on ?\<pi>U ?mulU ?N"
  let ?mulQ = "top1_quotient_group_mul_on ?mulU"
  let ?eQ = "top1_group_coset_on ?\<pi>U ?mulU ?N ?eU"
  let ?invgQ = "\<lambda>C. top1_group_coset_on ?\<pi>U ?mulU ?N
      (?invgU (SOME g. g \<in> ?\<pi>U \<and> C = top1_group_coset_on ?\<pi>U ?mulU ?N g))"
  have hQ_grp: "top1_is_group_on ?Q ?mulQ ?eQ ?invgQ"
    by (rule quotient_group_is_group[OF h\<pi>U_grp hN_normal_U])
  \<comment> \<open>The quotient projection \<pi>_1(U) \<rightarrow> \<pi>_1(U)/N is a surjective hom with kernel N.\<close>
  let ?\<phi> = "\<lambda>g. top1_group_coset_on ?\<pi>U ?mulU ?N g"
  have h\<phi>_hom: "top1_group_hom_on ?\<pi>U ?mulU ?Q ?mulQ ?\<phi>"
    by (rule quotient_projection_properties(1)[OF h\<pi>U_grp hN_normal_U])
  have h\<phi>_surj: "?\<phi> ` ?\<pi>U = ?Q"
    by (rule quotient_projection_properties(2)[OF h\<pi>U_grp hN_normal_U])
  have h\<phi>_ker: "top1_group_kernel_on ?\<pi>U ?eQ ?\<phi> = ?N"
    by (rule quotient_projection_properties(3)[OF h\<pi>U_grp hN_normal_U])
  \<comment> \<open>Construct \<psi>: FP \<rightarrow> \<pi>_1(U)/N via extension property.
     \<psi>(\<iota>_0(u)) = \<phi>(u) = [u]_N, \<psi>(\<iota>_1(v)) = e_Q.\<close>
  \<comment> \<open>Define the family of homs for the extension property.\<close>
  let ?\<psi>fam = "\<lambda>i::nat. if i = 0 then ?\<phi> else (\<lambda>v. ?eQ)"
  have h\<psi>fam_hom: "\<forall>\<alpha>\<in>{0::nat, 1}. top1_group_hom_on
      (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
      (if \<alpha> = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
      ?Q ?mulQ (?\<psi>fam \<alpha>)"
  proof (intro ballI)
    fix \<alpha> :: nat assume "\<alpha> \<in> {0, 1}"
    hence "\<alpha> = 0 \<or> \<alpha> = 1" by (by100 blast)
    thus "top1_group_hom_on
        (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)
        (if \<alpha> = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0)
        ?Q ?mulQ (?\<psi>fam \<alpha>)"
    proof
      assume h0: "\<alpha> = 0"
      thus ?thesis using h\<phi>_hom by (by100 simp)
    next
      assume h1: "\<alpha> = 1"
      \<comment> \<open>Trivial map \<pi>_1(V) \<rightarrow> {e_Q} is a hom.\<close>
      show ?thesis unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)"
        have "?\<psi>fam \<alpha> x = ?eQ" using h1 by (by100 simp)
        moreover have "?eQ \<in> ?Q" using hQ_grp unfolding top1_is_group_on_def by (by100 blast)
        ultimately show "?\<psi>fam \<alpha> x \<in> ?Q" by (by100 simp)
      next
        fix x y assume "x \<in> (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)"
            "y \<in> (if \<alpha> = 0 then ?\<pi>U else ?\<pi>V)"
        have heQ_in: "?eQ \<in> ?Q" using hQ_grp unfolding top1_is_group_on_def by (by100 blast)
        show "?\<psi>fam \<alpha> ((if \<alpha> = 0 then ?mulU else top1_fundamental_group_mul V ?TV x0) x y)
            = ?mulQ (?\<psi>fam \<alpha> x) (?\<psi>fam \<alpha> y)"
          using h1 group_id_left[OF hQ_grp heQ_in] by (by100 simp)
      qed
    qed
  qed
  obtain \<psi> where h\<psi>_hom: "top1_group_hom_on FP mulFP ?Q ?mulQ \<psi>"
      and h\<psi>_ext: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V).
          \<psi> (\<iota>fam \<alpha> x) = ?\<psi>fam \<alpha> x"
  proof -
    from Lemma_68_3_extension_property[OF hFP hQ_grp h\<psi>fam_hom hGG_grps]
    obtain h where hh: "top1_group_hom_on FP mulFP ?Q ?mulQ h
        \<and> (\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V).
            h (\<iota>fam \<alpha> x) = ?\<psi>fam \<alpha> x)"
      by blast
    show ?thesis using that[of h] hh by (by100 blast)
  qed
  \<comment> \<open>\<psi> is surjective: for [u]_N \<in> \<pi>_1(U)/N, \<psi>(\<iota>_0(u)) = \<phi>(u) = [u]_N.\<close>
  have h\<psi>_surj: "\<psi> ` FP = ?Q"
  proof (rule set_eqI, rule iffI)
    fix c assume "c \<in> \<psi> ` FP"
    then obtain w where hw: "w \<in> FP" and hc: "c = \<psi> w" by (by100 blast)
    show "c \<in> ?Q" using h\<psi>_hom hw hc unfolding top1_group_hom_on_def by (by100 blast)
  next
    fix c assume hc: "c \<in> ?Q"
    \<comment> \<open>c = \<phi>(u) for some u. And \<psi>(\<iota>_0(u)) = \<phi>(u) = c.\<close>
    from hc obtain u where hu: "u \<in> ?\<pi>U" and hcu: "c = ?\<phi> u"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    have h\<iota>0u_FP: "\<iota>fam 0 u \<in> FP" using hFP_eq hu by (by100 blast)
    have "\<psi> (\<iota>fam 0 u) = ?\<psi>fam 0 u"
      using h\<psi>_ext hu by (by100 force)
    hence "\<psi> (\<iota>fam 0 u) = ?\<phi> u" by (by100 simp)
    hence "\<psi> (\<iota>fam 0 u) = c" using hcu by (by100 simp)
    thus "c \<in> \<psi> ` FP" using h\<iota>0u_FP by (by100 blast)
  qed
  \<comment> \<open>N' is normal in FP (from SvK proof).\<close>
  have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>\<alpha>\<in>{0::nat, 1}. \<forall>x\<in>(if \<alpha> = 0 then ?\<pi>U else ?\<pi>V). \<iota>fam \<alpha> x \<in> FP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hN'_gens_sub: "{ mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 } \<subseteq> FP"
  proof (rule subsetI)
    fix x assume "x \<in> { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        and hx: "x = mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))"
      by (by100 blast)
    have hUV_sub': "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
    have hTUV': "is_topology_on (U \<inter> V) ?TUV"
      by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub'])
    have hx0_UV': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
    have hincl_UV_U': "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
      moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
        by (rule subspace_topology_trans) (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hincl_UV_V: "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF
              top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
      moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
        by (rule subspace_topology_trans) (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hjU_c_in: "?j_UV_U c \<in> ?\<pi>U"
    proof -
      have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
          (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U ?mulU ?j_UV_U"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopU hx0_UV' hx0_U hincl_UV_U'])
           (by100 simp)
      thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
    qed
    let ?j_UV_V' = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x)"
    have hjV_c_in: "?j_UV_V' c \<in> ?\<pi>V"
    proof -
      have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
          (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>V
          (top1_fundamental_group_mul V ?TV x0) ?j_UV_V'"
        by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopV hx0_UV' hx0_V hincl_UV_V])
           (by100 simp)
      thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have h0_in: "\<iota>fam 0 (?j_UV_U c) \<in> FP" using h\<iota>_in hjU_c_in by (by100 force)
    have h1_in: "\<iota>fam 1 (?j_UV_V' c) \<in> FP" using h\<iota>_in hjV_c_in by (by100 force)
    have hinv_in: "invgFP (\<iota>fam 1 (?j_UV_V' c)) \<in> FP"
      by (rule group_inv_closed[OF hFP_grp h1_in])
    have "mulFP (\<iota>fam 0 (?j_UV_U c)) (invgFP (\<iota>fam 1 (?j_UV_V' c))) \<in> FP"
      by (rule group_mul_closed[OF hFP_grp h0_in hinv_in])
    thus "x \<in> FP" using hx by (by100 simp)
  qed
  have hN'_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP ?N'"
    by (rule normal_subgroup_generated_is_normal[OF hFP_grp hN'_gens_sub])
  \<comment> \<open>Common membership facts.\<close>
  have hUV_sub': "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
  have hTUV': "is_topology_on (U \<inter> V) ?TUV"
    by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub'])
  have hx0_UV': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
  have hincl_UV_U': "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
    moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
      by (rule subspace_topology_trans) (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hincl_UV_V': "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
  proof -
    have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF
            top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
    moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
      by (rule subspace_topology_trans) (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hjUVU_hom: "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
      (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U ?mulU ?j_UV_U"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopU hx0_UV' hx0_U hincl_UV_U'])
       (by100 simp)
  have hjUVV_hom: "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
      (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>V
      (top1_fundamental_group_mul V ?TV x0)
      (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x))"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV' hTopV hx0_UV' hx0_V hincl_UV_V'])
       (by100 simp)
  have hjUc_mem: "\<And>c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 \<Longrightarrow> ?j_UV_U c \<in> ?\<pi>U"
    using hjUVU_hom unfolding top1_group_hom_on_def by (by100 blast)
  have hjVc_mem: "\<And>c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 \<Longrightarrow>
      top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c \<in> ?\<pi>V"
    using hjUVV_hom unfolding top1_group_hom_on_def by (by100 blast)
  \<comment> \<open>\<iota>_1(e_V) = eFP and invgFP(eFP) = eFP.\<close>
  have h\<iota>1_hom_grp: "top1_group_hom_on ?\<pi>V (top1_fundamental_group_mul V ?TV x0) FP mulFP (\<iota>fam 1)"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> ?\<pi>V" thus "\<iota>fam 1 x \<in> FP" using h\<iota>_in by (by100 force)
  next
    fix x y assume "x \<in> ?\<pi>V" "y \<in> ?\<pi>V"
    thus "\<iota>fam 1 (top1_fundamental_group_mul V ?TV x0 x y) = mulFP (\<iota>fam 1 x) (\<iota>fam 1 y)"
    proof -
      have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<forall>y\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V).
          \<iota>fam \<alpha> ((if \<alpha>=0 then ?mulU else top1_fundamental_group_mul V ?TV x0) x y) = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
        using hFP unfolding top1_is_free_product_on_def by (by100 blast)
      thus ?thesis using \<open>x \<in> ?\<pi>V\<close> \<open>y \<in> ?\<pi>V\<close> by (by100 force)
    qed
  qed
  have h\<iota>1_eV_fact: "\<iota>fam 1 (top1_fundamental_group_id V ?TV x0) = eFP"
    by (rule hom_preserves_id[OF h\<pi>V_GG hFP_grp h\<iota>1_hom_grp])
  have hinvFP_eFP: "invgFP eFP = eFP"
  proof -
    have "eFP \<in> FP" using group_e_mem[OF hFP_grp] .
    have "mulFP eFP (invgFP eFP) = eFP" by (rule group_inv_right[OF hFP_grp \<open>eFP \<in> FP\<close>])
    moreover have "mulFP eFP (invgFP eFP) = invgFP eFP"
      using group_id_left[OF hFP_grp group_inv_closed[OF hFP_grp \<open>eFP \<in> FP\<close>]] by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>ker(\<psi>) = N': generators of N' map to e_Q, and \<iota>_0(N) \<subseteq> N'.\<close>
  have h\<psi>_ker: "top1_group_kernel_on FP ?eQ \<psi> = ?N'"
  proof (rule set_eqI, rule iffI)
    fix w assume hw: "w \<in> top1_group_kernel_on FP ?eQ \<psi>"
    hence hwFP: "w \<in> FP" and h\<psi>w: "\<psi> w = ?eQ"
      unfolding top1_group_kernel_on_def by (by100 blast)+
    \<comment> \<open>w = \<iota>_0(u) for some u \<in> \<pi>_1(U). \<psi>(\<iota>_0(u)) = \<phi>(u) = e_Q means u \<in> N.
       So w = \<iota>_0(u) with u \<in> N. Need w \<in> N' = normal_closure(\<iota>_0(generators of N)).\<close>
    \<comment> \<open>w \<in> FP = \<iota>_0(\<pi>_1(U)), so w = \<iota>_0(u) for some u.\<close>
    from hwFP obtain u where hu: "u \<in> ?\<pi>U" and hwu: "w = \<iota>fam 0 u"
      using hFP_eq by (by100 blast)
    \<comment> \<open>\<psi>(\<iota>_0(u)) = \<phi>(u) = e_Q means u \<in> N.\<close>
    have h\<psi>u: "\<psi> (\<iota>fam 0 u) = ?\<phi> u"
      using h\<psi>_ext hu by (by100 force)
    hence h\<phi>u: "?\<phi> u = ?eQ" using h\<psi>w hwu by (by100 simp)
    have hu_in_N: "u \<in> ?N"
      using h\<phi>_ker hu h\<phi>u unfolding top1_group_kernel_on_def by (by100 blast)
    \<comment> \<open>Need: \<iota>_0(u) \<in> N'. Since N' = \<Inter>{K normal in FP | gens \<subseteq> K},
       it suffices to show \<iota>_0(u) \<in> K for every such K.
       Given K: the simplified generators {\<iota>_0(j_UV_U(c))} \<subseteq> K.
       So \<iota>_0\<inverse>(K) \<supseteq> {j_UV_U(c)} and is normal in \<pi>_1(U), hence \<iota>_0\<inverse>(K) \<supseteq> N.
       u \<in> N \<subseteq> \<iota>_0\<inverse>(K), so \<iota>_0(u) \<in> K.\<close>
    \<comment> \<open>Since the relators simplify to {\<iota>_0(j_UV_U(c))} when \<pi>_1(V)={e_V},
       and u \<in> N = normal_closure({j_UV_U(c)}), the map \<iota>_0 sends N into N'.
       This is because N' contains all conjugates of \<iota>_0(generators), and \<iota>_0 preserves
       conjugation (being a hom). Formally: N' \<supseteq> \<iota>_0(N) because every normal
       K \<supseteq> generators_of_N' satisfies \<iota>_0\<inverse>(K) \<supseteq> N.\<close>
    \<comment> \<open>Use InterI on N' = normal_subgroup_generated = \<Inter>{K | gens \<subseteq> K \<and> K normal}.\<close>
    have h\<iota>0_hom_loc: "top1_group_hom_on ?\<pi>U ?mulU FP mulFP (\<iota>fam 0)"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> ?\<pi>U" thus "\<iota>fam 0 x \<in> FP" using h\<iota>_in by (by100 force)
    next
      fix x y assume "x \<in> ?\<pi>U" "y \<in> ?\<pi>U"
      thus "\<iota>fam 0 (?mulU x y) = mulFP (\<iota>fam 0 x) (\<iota>fam 0 y)"
      proof -
        have "\<forall>\<alpha>\<in>{0::nat,1}. \<forall>x\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V). \<forall>y\<in>(if \<alpha>=0 then ?\<pi>U else ?\<pi>V).
            \<iota>fam \<alpha> ((if \<alpha>=0 then ?mulU else top1_fundamental_group_mul V ?TV x0) x y) = mulFP (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)"
          using hFP unfolding top1_is_free_product_on_def by (by100 blast)
        thus ?thesis using \<open>x \<in> ?\<pi>U\<close> \<open>y \<in> ?\<pi>U\<close> by (by100 force)
      qed
    qed
    \<comment> \<open>Show: every K with gens_N' \<subseteq> K and K normal in FP contains w = \<iota>_0(u).\<close>
    show "w \<in> ?N'"
      unfolding top1_normal_subgroup_generated_on_def
    proof (rule InterI)
      fix K assume hK_mem: "K \<in> {K'. { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 } \<subseteq> K'
             \<and> top1_normal_subgroup_on FP mulFP eFP invgFP K'}"
      hence hgens_K: "{ mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 } \<subseteq> K"
          and hK_normal: "top1_normal_subgroup_on FP mulFP eFP invgFP K"
        by (by100 blast)+
      \<comment> \<open>Preimage \<iota>_0\<inverse>(K) \<inter> \<pi>_1(U) is normal in \<pi>_1(U).\<close>
      have hpreimg: "top1_normal_subgroup_on ?\<pi>U ?mulU ?eU ?invgU {g \<in> ?\<pi>U. \<iota>fam 0 g \<in> K}"
        by (rule preimage_normal_subgroup[OF h\<pi>U_grp hFP_grp h\<iota>0_hom_loc hK_normal])
      \<comment> \<open>Generators of N lie in preimage: j_UV_U(c) \<in> preimage.\<close>
      have hgens_in_preimg: "?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0
          \<subseteq> {g \<in> ?\<pi>U. \<iota>fam 0 g \<in> K}"
      proof (rule image_subsetI)
        fix c assume hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
        \<comment> \<open>The generator mulFP(\<iota>_0(j_c))(invgFP(\<iota>_1(j'_c))) \<in> K. When \<pi>_1(V) = {e_V},
           this simplifies to \<iota>_0(j_c) \<in> K.\<close>
        have hgen_in_K: "mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
          \<in> K" using hgens_K hc by (by100 blast)
        \<comment> \<open>Simplify: \<iota>_1(j_V(c)) = eFP, invgFP(eFP) = eFP, mulFP(x)(eFP) = x.\<close>
        have "\<iota>fam 0 (?j_UV_U c) \<in> K"
        proof -
          have hjVc_trivial: "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c
              = top1_fundamental_group_id V ?TV x0"
            using hjVc_mem[OF hc] hPiV_trivial by (by100 blast)
          have "invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c))
              = eFP" using hjVc_trivial h\<iota>1_eV_fact hinvFP_eFP by (by100 simp)
          hence "mulFP (\<iota>fam 0 (?j_UV_U c))
              (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
            = mulFP (\<iota>fam 0 (?j_UV_U c)) eFP" by (by100 simp)
          moreover have "\<iota>fam 0 (?j_UV_U c) \<in> FP"
            using h\<iota>_in hjUc_mem[OF hc] by (by100 force)
          hence "mulFP (\<iota>fam 0 (?j_UV_U c)) eFP = \<iota>fam 0 (?j_UV_U c)"
            using group_id_right[OF hFP_grp] by (by100 blast)
          ultimately show ?thesis using hgen_in_K by (by100 simp)
        qed
        thus "?j_UV_U c \<in> {g \<in> ?\<pi>U. \<iota>fam 0 g \<in> K}"
          using hjUc_mem[OF hc] by (by100 blast)
      qed
      \<comment> \<open>N \<subseteq> preimage (N is smallest normal containing generators).\<close>
      have "?N \<subseteq> {g \<in> ?\<pi>U. \<iota>fam 0 g \<in> K}"
        unfolding top1_normal_subgroup_generated_on_def
        using hgens_in_preimg hpreimg by (by100 blast)
      hence "u \<in> {g \<in> ?\<pi>U. \<iota>fam 0 g \<in> K}" using hu_in_N by (by100 blast)
      thus "w \<in> K" using hwu by (by100 blast)
    qed
  next
    fix w assume hw: "w \<in> ?N'"
    \<comment> \<open>N' is generated by elements of the form mulFP(\<iota>_0(j_c))(invgFP(\<iota>_1(j'_c))).
       \<psi> maps each such generator to e_Q (shown below). Since ker is normal, N' \<subseteq> ker.\<close>
    have hN'_sub: "?N' \<subseteq> FP"
      using hN'_normal unfolding top1_normal_subgroup_on_def top1_is_group_on_def by (by100 blast)
    have hwFP: "w \<in> FP" using hw hN'_sub by (by100 blast)
    \<comment> \<open>Generators map to e_Q: \<psi>(mulFP(\<iota>_0(j_c))(invgFP(\<iota>_1(j'_c))))
       = mulQ(\<phi>(j_c))(invgQ(\<psi>(\<iota>_1(j'_c)))) = mulQ([j_c]_N)(invgQ(e_Q))
       = mulQ([j_c]_N)(e_Q) = [j_c]_N. And j_c \<in> N, so [j_c]_N = e_Q.\<close>
    have hgens_in_ker: "\<forall>g \<in> { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }.
       \<psi> g = ?eQ"
    proof (intro ballI)
      fix g assume "g \<in> { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
      then obtain c where hc: "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
          and hg: "g = mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))"
        by (by100 blast)
      let ?jVc = "top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c"
      \<comment> \<open>\<psi> is a hom, so \<psi>(a \<cdot> b) = \<psi>(a) \<cdot> \<psi>(b).\<close>
      have hjUc_in0: "?j_UV_U c \<in> ?\<pi>U"
      proof -
        have hUV_sub'': "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
        have hTUV'': "is_topology_on (U \<inter> V) ?TUV"
          by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub''])
        have hx0_UV'': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
        have hincl'': "top1_continuous_map_on (U \<inter> V) ?TUV U ?TU (\<lambda>x. x)"
        proof -
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) U ?TU (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopU, unfolded id_def]]) (by100 blast)
          moreover have "subspace_topology U ?TU (U \<inter> V) = ?TUV"
            by (rule subspace_topology_trans) (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>U ?mulU ?j_UV_U"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV'' hTopU hx0_UV'' hx0_U hincl''])
             (by100 simp)
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      have hjVc_in0: "?jVc \<in> ?\<pi>V"
      proof -
        have hUV_sub'': "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
        have hTUV'': "is_topology_on (U \<inter> V) ?TUV"
          by (rule subspace_topology_is_topology_on[OF hTopX hUV_sub''])
        have hx0_UV'': "x0 \<in> U \<inter> V" using assms(8) by (by100 blast)
        have hincl_V'': "top1_continuous_map_on (U \<inter> V) ?TUV V ?TV (\<lambda>x. x)"
        proof -
          have "top1_continuous_map_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) V ?TV (\<lambda>x. x)"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF
                  top1_continuous_map_on_id[OF hTopV, unfolded id_def]]) (by100 blast)
          moreover have "subspace_topology V ?TV (U \<inter> V) = ?TUV"
            by (rule subspace_topology_trans) (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "top1_group_hom_on (top1_fundamental_group_carrier (U \<inter> V) ?TUV x0)
            (top1_fundamental_group_mul (U \<inter> V) ?TUV x0) ?\<pi>V
            (top1_fundamental_group_mul V ?TV x0)
            (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x))"
          by (rule top1_fundamental_group_induced_on_is_hom[OF hTUV'' hTopV hx0_UV'' hx0_V hincl_V''])
             (by100 simp)
        thus ?thesis using hc unfolding top1_group_hom_on_def by (by100 blast)
      qed
      have h0_in: "\<iota>fam 0 (?j_UV_U c) \<in> FP" using h\<iota>_in hjUc_in0 by (by100 force)
      have h1_in: "\<iota>fam 1 ?jVc \<in> FP" using h\<iota>_in hjVc_in0 by (by100 force)
      have hinv_in: "invgFP (\<iota>fam 1 ?jVc) \<in> FP"
        by (rule group_inv_closed[OF hFP_grp h1_in])
      \<comment> \<open>\<psi>(\<iota>_0(j_UV_U(c))) = \<phi>(j_UV_U(c)) = [j_UV_U(c)]_N.\<close>
      have hjUc_in: "?j_UV_U c \<in> ?\<pi>U" by (rule hjUc_in0)
      have h\<psi>_0: "\<psi> (\<iota>fam 0 (?j_UV_U c)) = ?\<phi> (?j_UV_U c)"
        using h\<psi>_ext hjUc_in by (by100 force)
      \<comment> \<open>j_UV_U(c) is a generator of N, so [j_UV_U(c)]_N = e_Q.\<close>
      have hjUc_in_N: "?j_UV_U c \<in> ?N"
      proof -
        have "?j_UV_U c \<in> ?j_UV_U ` top1_fundamental_group_carrier (U \<inter> V) ?TUV x0"
          using hc by (by100 blast)
        thus ?thesis
          unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      qed
      have h\<phi>_jUc: "?\<phi> (?j_UV_U c) = ?eQ"
        using hjUc_in_N h\<phi>_ker hjUc_in
        unfolding top1_group_kernel_on_def by (by100 blast)
      \<comment> \<open>\<psi>(\<iota>_1(j_UV_V(c))) = e_Q (trivial map on V-factor).\<close>
      have hjVc_in: "?jVc \<in> ?\<pi>V" by (rule hjVc_in0)
      have h\<psi>_1: "\<psi> (\<iota>fam 1 ?jVc) = ?eQ"
        using h\<psi>_ext hjVc_in by (by100 force)
      have h\<psi>_inv: "\<psi> (invgFP (\<iota>fam 1 ?jVc)) = ?invgQ ?eQ"
      proof -
        have hstep1: "\<psi> (invgFP (\<iota>fam 1 ?jVc)) = ?invgQ (\<psi> (\<iota>fam 1 ?jVc))"
          by (rule hom_preserves_inv[OF hFP_grp hQ_grp h\<psi>_hom h1_in])
        have hstep2: "\<psi> (\<iota>fam 1 ?jVc) = ?eQ" by (rule h\<psi>_1)
        show ?thesis using hstep1 hstep2 by (by100 simp)
      qed
      have hinvQ_eQ: "?invgQ ?eQ = ?eQ"
      proof -
        have heQ_in: "?eQ \<in> ?Q" using hQ_grp unfolding top1_is_group_on_def by (by100 blast)
        have hinvQ_in: "?invgQ ?eQ \<in> ?Q" by (rule group_inv_closed[OF hQ_grp heQ_in])
        have "?invgQ ?eQ = ?mulQ ?eQ (?invgQ ?eQ)"
          using group_id_left[OF hQ_grp hinvQ_in] by (by100 simp)
        also have "\<dots> = ?eQ" by (rule group_inv_right[OF hQ_grp heQ_in])
        finally show ?thesis .
      qed
      \<comment> \<open>Assembly: \<psi>(g) = \<psi>(\<iota>_0(jUc)) \<cdot> \<psi>(invg(\<iota>_1(jVc))) = e_Q \<cdot> e_Q = e_Q.\<close>
      have "\<psi> g = ?mulQ (\<psi> (\<iota>fam 0 (?j_UV_U c))) (\<psi> (invgFP (\<iota>fam 1 ?jVc)))"
        using hg h\<psi>_hom h0_in hinv_in unfolding top1_group_hom_on_def by (by100 blast)
      also have "\<dots> = ?mulQ (?\<phi> (?j_UV_U c)) (\<psi> (invgFP (\<iota>fam 1 ?jVc)))"
        using h\<psi>_0 by (by100 simp)
      also have "\<dots> = ?mulQ ?eQ (\<psi> (invgFP (\<iota>fam 1 ?jVc)))"
        using h\<phi>_jUc by (by100 simp)
      also have "\<dots> = ?mulQ ?eQ (?invgQ ?eQ)"
        using h\<psi>_inv by (by100 simp)
      also have "\<dots> = ?mulQ ?eQ ?eQ" using hinvQ_eQ by (by100 simp)
      also have "\<dots> = ?eQ"
      proof -
        have "?eQ \<in> ?Q" using hQ_grp unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis using group_id_left[OF hQ_grp] by (by100 blast)
      qed
      finally show "\<psi> g = ?eQ" .
    qed
    have hker_normal_FP: "top1_normal_subgroup_on FP mulFP eFP invgFP
        (top1_group_kernel_on FP ?eQ \<psi>)"
      by (rule kernel_is_normal_subgroup[OF hFP_grp hQ_grp h\<psi>_hom])
    have hgens_in_ker2: "{ mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }
       \<subseteq> top1_group_kernel_on FP ?eQ \<psi>"
    proof (rule subsetI)
      fix g assume "g \<in> { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }"
      hence "\<psi> g = ?eQ" using hgens_in_ker by (by100 blast)
      moreover have "g \<in> FP" using hN'_gens_sub \<open>g \<in> _\<close> by (by100 blast)
      ultimately show "g \<in> top1_group_kernel_on FP ?eQ \<psi>"
        unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    show "w \<in> top1_group_kernel_on FP ?eQ \<psi>"
    proof -
      have hN'_def_eq: "?N' = \<Inter>{K. { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 } \<subseteq> K
             \<and> top1_normal_subgroup_on FP mulFP eFP invgFP K}"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      have "w \<in> \<Inter>{K. { mulFP (\<iota>fam 0 (?j_UV_U c))
               (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
       | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 } \<subseteq> K
             \<and> top1_normal_subgroup_on FP mulFP eFP invgFP K}"
        using hw hN'_def_eq by (by100 simp)
      hence "w \<in> top1_group_kernel_on FP ?eQ \<psi>"
        using hgens_in_ker2 hker_normal_FP by (by100 blast)
      thus ?thesis .
    qed
  qed
  \<comment> \<open>Apply first isomorphism theorem.\<close>
  have hFP_N'_iso: "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on FP mulFP ?N')
      (top1_quotient_group_mul_on mulFP)
      (top1_quotient_group_carrier_on ?\<pi>U ?mulU ?N)
      (top1_quotient_group_mul_on ?mulU)"
  proof -
    have "top1_groups_isomorphic_on ?Q ?mulQ
        (top1_quotient_group_carrier_on FP mulFP ?N') (top1_quotient_group_mul_on mulFP)"
      by (rule first_isomorphism_theorem[OF hFP_grp hN'_normal hQ_grp h\<psi>_hom h\<psi>_surj h\<psi>_ker])
    thus ?thesis
      by (rule top1_groups_isomorphic_on_sym[OF _ hQ_grp])
         (rule quotient_group_is_group[OF hFP_grp hN'_normal])
  qed
  show ?thesis
    by (rule groups_isomorphic_trans_fwd[OF hSvK hFP_N'_iso])
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
    fix F' assume "F' \<subseteq> \<U>" "finite F'" "B \<subseteq> \<Union>F'"
    thus thesis using that by (by100 blast)
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
  have hSC_open: "open (- C)" using assms(2) unfolding closed_def by (by100 blast)
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
  \<comment> \<open>The 4n-gon's 1-skeleton is a wedge of 2n circles. By Theorem 72.1,
     attaching the 2-cell gives the presentation ⟨a₁,b₁,...|[a₁,b₁]...[aₙ,bₙ]⟩.\<close>
  show ?thesis sorry
qed

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1\<^sup>2 \<cdots> a_m\<^sup>2\<rangle>.
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
  \<comment> \<open>The 2m-gon's 1-skeleton is a wedge of m circles. By Theorem 72.1,
     attaching the 2-cell gives the presentation ⟨a₁,...,aₘ | a₁²...aₘ²⟩.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 2: Abelianizing kills all commutators, making the relator trivial.
     So H_1(T_n) = Z^{2n} (free abelian on 2n generators).\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 2: Abelianize: H = Z^m / \<langle>2(a_1+...+a_m)\<rangle>.
     Torsion = Z/2Z, free part = Z^{m-1}.\<close>
  show ?thesis sorry
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
        using hp by (by100 blast)
    next
      assume "p \<in> {(x, y) | x y. \<exists>c. (\<forall>i<3. 0 \<le> c i) \<and> (\<Sum>i<3. c i) = 1
          \<and> x = (\<Sum>i<3. c i * ?vx i) \<and> y = (\<Sum>i<3. c i * ?vy i)}"
      then obtain c where hcge: "\<forall>i<3. (0::real) \<le> c i"
          and hcsum: "(\<Sum>i<3. c i) = 1"
          and hpx_raw: "x = (\<Sum>i<3. c i * ?vx i)" and hpy_raw: "y = (\<Sum>i<3. c i * ?vy i)"
        using hp by (by100 auto)
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
  show ?thesis sorry
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
  \<comment> \<open>By Theorem 78.1, X is a quotient of finitely many triangles.\<close>
  \<comment> \<open>Iteratively merge adjacent triangles into a single polygon.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Reduce the scheme via elementary operations to standard form.\<close>
  show ?thesis sorry
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
      by (by100 blast)
    obtain a where ha: "a \<in> U0" using hU0ne by (by100 blast)
    obtain b where hb: "b \<in> V0" using hV0ne by (by100 blast)
    have haX: "a \<in> X" using ha hcover by (by100 blast)
    have hbX: "b \<in> X" using hb hcover by (by100 blast)
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
        hence "top1_loop_equiv_on B TB b0 (p \<circ> ?conj2) k" using hk by (by100 simp)
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
          by (by100 blast)
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
        by (rule subspace_topology_trans) (by100 blast)
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
      \<and> top1_continuous_map_on E TE Y TY q"
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
        "top1_continuous_map_on E TE Y TY q" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain q where hq_Y: "\<forall>e\<in>E. q e \<in> Y" and hq_rp: "\<forall>e\<in>E. r (q e) = p e"
      and hq_cont: "top1_continuous_map_on E TE Y TY q" by (by100 blast)
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.
     For each y \<in> Y, take b = r(y). Take U evenly covered by both p and r.
     Slices of p\<inverse>(U) are {U_\<alpha>}, slices of r\<inverse>(U) are {V_\<beta>}.
     q maps each U_\<alpha> into some V_\<beta> (connectedness).
     q restricted to U_\<alpha> = r_\<beta>\<inverse> \<circ> p_\<alpha>, a homeomorphism.
     So q evenly covers each V_\<beta>.\<close>
  have hq_surj: "q ` E = Y"
    sorry \<comment> \<open>Surjectivity: q(E) open+closed in connected Y, contains y0.\<close>
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
  show ?thesis sorry
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

(** from \<S>83 Theorem 83.2: any covering space of a graph is itself a graph. **)
theorem Theorem_83_2_covering_of_graph_is_graph:
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
  \<comment> \<open>Lift arcs from B to E (sheets over arcs are arcs), inherit Hausdorff + weak topology.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Choose maximal tree T, collapse to wedge of circles X/T, which has
     free π₁ by Theorem 71.3. Homotopy equivalence gives π₁(X) ≅ π₁(X/T).\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 1: Realize G as \<pi>_1 of a wedge of circles X.\<close>
  \<comment> \<open>Step 2: H \<le> G \<cong> \<pi>_1(X) gives a covering space E of X with p_*(\<pi>_1(E)) \<cong> H.\<close>
  \<comment> \<open>Step 3: E is a graph (Theorem 83.2). \<pi>_1(E) is free (Theorem 84.7). H \<cong> \<pi>_1(E) is free.\<close>
  show ?thesis sorry
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
  \<comment> \<open>Step 1: Realize F as \<pi>_1 of wedge X of n+1 circles. Build k-sheeted covering E.\<close>
  \<comment> \<open>Step 2: Euler characteristic computation gives rank kn+1.\<close>
  \<comment> \<open>Step 3: H \<cong> \<pi>_1(E) is free on kn+1 generators.\<close>
  show ?thesis sorry
qed

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


















































































































































































































































































end



























































































































































































































































































 
  
   
    



  



