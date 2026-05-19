theory K5_nonplanar
imports AlgTop.AlgTop
begin

lemma arc_endpoints_subset:
  "top1_arc_endpoints_on A TA \<subseteq> A"
  unfolding top1_arc_endpoints_on_def by blast

text \<open>K4 separation with e14 naming. Calls K4 lemma via [OF assms] (fast).\<close>
lemma K5_K4_sep:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      "card {a1, a2, a3, a4 :: real \<times> real \<times> real} = 4"
      "{a1, a2, a3, a4} \<subseteq> top1_S2"
      "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      "e14 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
      "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      "top1_is_arc_on e14 (subspace_topology top1_S2 top1_S2_topology e14)"
      "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      "top1_arc_endpoints_on e14 (subspace_topology top1_S2 top1_S2_topology e14) = {a4,a1}"
      "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      "e12 \<inter> e34 = {}" "e23 \<inter> e14 = {}"
      "e12 \<inter> e23 = {a2}" "e23 \<inter> e34 = {a3}"
      "e34 \<inter> e14 = {a4}" "e14 \<inter> e12 = {a1}"
      "e13 \<inter> e12 = {a1}" "e13 \<inter> e23 = {a3}"
      "e13 \<inter> e34 = {a3}" "e13 \<inter> e14 = {a1}"
      "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      "e24 \<inter> e12 = {a2}" "e24 \<inter> e23 = {a2}"
      "e24 \<inter> e34 = {a4}" "e24 \<inter> e14 = {a4}"
  shows "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
  by (rule Lemma_64_3_K4_four_components[OF assms])

text \<open>Strengthened K4: same as Lemma\_64\_3 but adds boundary info
  (no component closure contains all 4 vertices).\<close>
lemma K4_four_components_with_boundary:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
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
      \<comment> \<open>K_4 planarity: arcs only intersect at shared vertices.\<close>
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
  shows "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
proof -
  \<comment> \<open>Extract vertex distinctness.\<close>
  have hdist: "a1 \<noteq> a2" "a1 \<noteq> a3" "a1 \<noteq> a4" "a2 \<noteq> a3" "a2 \<noteq> a4" "a3 \<noteq> a4"
  proof -
    from assms(2) have hc4: "card {a1, a2, a3, a4} = 4" .
    { assume h: "a1 = a2"
      have "{a1, a2, a3, a4} = {a1, a3, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a2" by (by100 blast)
    { assume h: "a1 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a3" by (by100 blast)
    { assume h: "a1 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a4" by (by100 blast)
    { assume h: "a2 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a3" by (by100 blast)
    { assume h: "a2 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a4" by (by100 blast)
    { assume h: "a3 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a3 \<noteq> a4" by (by100 blast)
  qed
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule assms(1))
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: Form theta space. A = e12 \<union> e23, B = e13, C = e41 \<union> e34.\<close>
  let ?A = "e12 \<union> e23" and ?B = "e13" and ?C = "e41 \<union> e34"
  let ?Y = "?A \<union> ?B \<union> ?C"
  \<comment> \<open>A is an arc from a1 to a3 (via concatenation at a2).\<close>
  have ha2_ep12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(16) by (by100 blast)
  have ha2_ep23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) by (by100 blast)
  have hA_arc: "top1_is_arc_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23])
  have hA_ep: "top1_arc_endpoints_on ?A (subspace_topology top1_S2 top1_S2_topology ?A) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23 assms(16) assms(17) hdist(1) hdist(4)])
  have hA_sub: "?A \<subseteq> top1_S2" using assms(4,5) by (by100 blast)
  \<comment> \<open>C is an arc from a1 to a3 (via concatenation at a4).\<close>
  have he41_e34_int: "e41 \<inter> e34 = {a4}" using assms(26) by (by100 blast)
  have ha4_ep41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) by (by100 blast)
  have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(18) by (by100 blast)
  have hC_arc: "top1_is_arc_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34])
  have ha4_ne_a3: "a4 \<noteq> a3" using hdist(6) by (by100 blast)
  \<comment> \<open>Reorder endpoints for unification: {a4,a1} \<rightarrow> {a1,a4}, {a3,a4} \<rightarrow> {a4,a3}.\<close>
  have hep_e41: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4}"
    using assms(19) by (by100 force)
  have hep_e34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a4, a3}"
    using assms(18) by (by100 force)
  have hC_ep: "top1_arc_endpoints_on ?C (subspace_topology top1_S2 top1_S2_topology ?C) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34 hep_e41 hep_e34 hdist(3) ha4_ne_a3])
  have hC_sub: "?C \<subseteq> top1_S2" using assms(6,7) by (by100 blast)
  \<comment> \<open>Intersection conditions for theta space.\<close>
  have hAB_int: "?A \<inter> ?B = {a1, a3}"
    using assms(28) assms(29) by (by100 blast)
  have hBC_int: "?B \<inter> ?C = {a1, a3}"
    using assms(31) assms(30) by (by100 blast)
  have hAC_int: "?A \<inter> ?C = {a1, a3}"
    using assms(27) assms(22) assms(23) assms(25) by (by100 blast)
  \<comment> \<open>Step 2: Apply Lemma 64.1 to get 3 components.\<close>
  obtain U V W where hUVW:
      "U \<noteq> {}" "V \<noteq> {}" "W \<noteq> {}"
      "U \<inter> V = {}" "V \<inter> W = {}" "U \<inter> W = {}"
      "U \<union> V \<union> W = top1_S2 - (?A \<union> ?B \<union> ?C)"
      "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      "U \<in> top1_S2_topology" "V \<in> top1_S2_topology" "W \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF assms(1) hA_sub assms(8) hC_sub
        hA_arc assms(14) hC_arc hdist(2) hAB_int hBC_int hAC_int hA_ep assms(20) hC_ep]
    by (by100 metis)
  \<comment> \<open>Step 3: Identify which theta component contains e24-{a2,a4}.
     Use JCT on A\<union>B and B\<union>C to get 2-component decompositions, then boundary arguments.\<close>
  \<comment> \<open>A\<union>B is SCC.\<close>
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus hA_arc hA_sub
        assms(14) assms(8) hAB_int hdist(2) hA_ep assms(20)])
  \<comment> \<open>Apply Theorem_63_5 to A and B (as separate arcs) to get 2 components of S2-(A\<union>B).\<close>
  have hA_closed: "closedin_on top1_S2 top1_S2_topology ?A"
    by (rule arc_in_S2_closed[OF hA_sub hA_arc])
  have hB_closed: "closedin_on top1_S2 top1_S2_topology ?B"
    by (rule arc_in_S2_closed[OF assms(8) assms(14)])
  have hA_conn: "top1_connected_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    using arc_connected[OF hA_arc] .
  have hB_conn: "top1_connected_on ?B (subspace_topology top1_S2 top1_S2_topology ?B)"
    using arc_connected[OF assms(14)] .
  have hA_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?A"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hA_sub hA_arc])
  have hB_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?B"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(8) assms(14)])
  have hAB_card: "card (?A \<inter> ?B) = 2"
    using hAB_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components, then choose labels so C-{a1,a3} \<subseteq> P2.\<close>
  have hCm_conn: "top1_connected_on (?C - {a1, a3})
      (subspace_topology top1_S2 top1_S2_topology (?C - {a1, a3}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hC_sub hC_arc hC_ep hdist(2)])
  have hCm_sub_AB: "?C - {a1, a3} \<subseteq> top1_S2 - (?A \<union> ?B)"
  proof -
    have "?C \<inter> (?A \<union> ?B) \<subseteq> {a1, a3}"
    proof -
      have "?C \<inter> ?A = {a1, a3}" using hAC_int by (by100 blast)
      moreover have "?C \<inter> ?B = {a1, a3}" using hBC_int by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    thus ?thesis using hC_sub by (by100 blast)
  qed
  have hCm_ne: "?C - {a1, a3} \<noteq> {}"
  proof -
    have "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a4 \<in> ?C" by (by100 blast)
    moreover have "a4 \<notin> {a1, a3}" using hdist(3) hdist(6) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  obtain P1_raw P2_raw where hP_raw: "P1_raw \<noteq> {}" "P2_raw \<noteq> {}" "P1_raw \<inter> P2_raw = {}"
      "P1_raw \<union> P2_raw = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1_raw (subspace_topology top1_S2 top1_S2_topology P1_raw)"
      "top1_connected_on P2_raw (subspace_topology top1_S2 top1_S2_topology P2_raw)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hA_closed hB_closed
        hA_conn hB_conn hAB_card hA_no_sep hB_no_sep]
    by (by100 force)
  \<comment> \<open>P1\_raw, P2\_raw are open (via S2\_component helper + maximality from Jordan).\<close>
  have hAB_closed_loc: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_compl_open_loc: "top1_S2 - (?A \<union> ?B) \<in> top1_S2_topology"
    using hAB_closed_loc unfolding closedin_on_def by (by100 blast)
  have hAB_not_conn: "\<not> top1_connected_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    using Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc]
    unfolding top1_separates_on_def by (by100 blast)
  have hP1r_open: "P1_raw \<in> top1_S2_topology" and hP2r_open: "P2_raw \<in> top1_S2_topology"
    using S2_two_component_open[OF hAB_compl_open_loc _ hP_raw(1,2,3,4,5,6) hAB_not_conn]
    by (by100 blast)+
  \<comment> \<open>With P1\_raw, P2\_raw open, form separation and apply Lemma\_23\_2.\<close>
  have hCm_in_raw: "?C - {a1, a3} \<subseteq> P1_raw \<or> ?C - {a1, a3} \<subseteq> P2_raw"
  proof -
    have hTAB_loc: "is_topology_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hP1r_oAB: "P1_raw \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
    proof -
      have "P1_raw = (top1_S2 - (?A \<union> ?B)) \<inter> P1_raw" using hP_raw(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP1r_open by (by100 blast)
    qed
    have hP2r_oAB: "P2_raw \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
    proof -
      have "P2_raw = (top1_S2 - (?A \<union> ?B)) \<inter> P2_raw" using hP_raw(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP2r_open by (by100 blast)
    qed
    have hAB_sep: "top1_is_separation_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1_raw P2_raw"
      unfolding top1_is_separation_on_def
      using hP1r_oAB hP2r_oAB hP_raw(1,2,3,4) by (by100 blast)
    have hCm_sub: "?C - {a1, a3} \<subseteq> top1_S2 - (?A \<union> ?B)"
      using hCm_sub_AB .
    have hCm_conn_AB: "top1_connected_on (?C - {a1, a3})
        (subspace_topology (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
            (?C - {a1, a3}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (?C - {a1, a3}) =
          subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (?C - {a1, a3})"
        using subspace_topology_trans[of "?C - {a1, a3}" "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
            hCm_sub by (by100 simp)
      thus ?thesis using hCm_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTAB_loc hAB_sep hCm_sub hCm_conn_AB]
    show ?thesis by (by100 blast)
  qed
  obtain P1 P2 where hP: "P1 \<noteq> {}" "P2 \<noteq> {}" "P1 \<inter> P2 = {}"
      "P1 \<union> P2 = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1 (subspace_topology top1_S2 top1_S2_topology P1)"
      "top1_connected_on P2 (subspace_topology top1_S2 top1_S2_topology P2)"
      and hCm_in_P2: "?C - {a1, a3} \<subseteq> P2"
  proof -
    from hCm_in_raw show ?thesis
    proof
      assume "?C - {a1, a3} \<subseteq> P1_raw"
      show ?thesis
        by (rule that[of P2_raw P1_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P1_raw\<close> in \<open>by100 blast\<close>)+
    next
      assume "?C - {a1, a3} \<subseteq> P2_raw"
      show ?thesis
        by (rule that[of P1_raw P2_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P2_raw\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Both P1, P2 are open (components of open set S2-(A\<union>B)).\<close>
  have hAB_closed_S2: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_compl_open: "top1_S2 - (?A \<union> ?B) \<in> top1_S2_topology"
    using hAB_closed_S2 unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>Components P1, P2 are open: they are path components of the open set S2-(A\<union>B),
     which is lpc (S2 is lpc, open subsets of lpc are lpc).\<close>
  \<comment> \<open>Key: S2-(A\<union>B) is open lpc, so connected components are open.\<close>
  have hAB_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hAB_compl_open])
       (by100 blast)
  have hTAB: "is_topology_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_P where hx_P: "x_P \<in> P1" using hP(1) by (by100 blast)
  have hx_P_W: "x_P \<in> top1_S2 - (?A \<union> ?B)" using hx_P hP(4) by (by100 blast)
  \<comment> \<open>Establish P1 = path\_component(x\_P) at outer scope for reuse.\<close>
  have hP1_sub_AB: "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
  have hP1_conn_AB: "top1_connected_on P1
      (subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1)"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology P1 =
        subspace_topology (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1"
      using subspace_topology_trans[of P1 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
          hP1_sub_AB by (by100 simp)
    thus ?thesis using hP(5) by (by100 simp)
  qed
  have hP1_eq_comp: "P1 = top1_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    have hP1_sub_comp: "P1 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_AB hx_P hP1_conn_AB])
    have hcomp_sub_P1: "top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq> P1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P" "y \<notin> P1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?A \<union> ?B)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?A \<union> ?B)"] by (by100 blast)
      hence "y \<in> P2" using hP(4) hy(2) by (by100 blast)
      have hP2_sub: "P2 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
      have hP2_conn_sub: "top1_connected_on P2
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P2 =
            subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2"
          using subspace_topology_trans[of P2 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
              hP2_sub by (by100 simp)
        thus ?thesis using hP(6) by (by100 simp)
      qed
      have "P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y"
        by (rule top1_connected_subspace_subset_component_of[OF hP2_sub \<open>y \<in> P2\<close> hP2_conn_sub])
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y =
          top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        by (rule top1_component_of_on_eq_of_mem[OF hTAB hy(1)])
      ultimately have "P1 \<union> P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP1_sub_comp by (by100 blast)
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq>
          top1_S2 - (?A \<union> ?B)"
        by (rule top1_component_of_on_subset)
      ultimately have "top1_S2 - (?A \<union> ?B) = top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP(4) by (by100 blast)
      have hcomp_conn: "top1_connected_on
          (top1_component_of_on (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P)
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_component_of_on (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P))"
        by (rule top1_component_of_on_connected[OF hTAB hx_P_W])
      hence "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_S2 - (?A \<union> ?B)))"
        using \<open>top1_S2 - (?A \<union> ?B) = top1_component_of_on _ _ x_P\<close> by (by100 simp)
      moreover have "subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
          (top1_S2 - (?A \<union> ?B)) =
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
        using subspace_topology_trans[of "top1_S2 - (?A \<union> ?B)" "top1_S2 - (?A \<union> ?B)"
            top1_S2 top1_S2_topology] by (by100 simp)
      ultimately have "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))" by (by100 simp)
      moreover have "\<not> top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    from hP1_sub_comp hcomp_sub_P1 show ?thesis by (by100 blast)
  qed
  have hP1_eq_pc: "P1 = top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTAB]]
    have "\<forall>z \<in> top1_S2 - (?A \<union> ?B).
        top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z" by (by100 blast)
    hence "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hAB_open_lpc hx_P_W by (by100 metis)
    thus ?thesis using hP1_eq_comp by (by100 simp)
  qed
  \<comment> \<open>Helper: open-in-subspace-of-open implies open-in-S2.\<close>
  have open_in_sub_imp_open: "\<And>W P. W \<in> top1_S2_topology \<Longrightarrow>
      P \<in> subspace_topology top1_S2 top1_S2_topology W \<Longrightarrow> P \<in> top1_S2_topology"
  proof -
    fix W P assume hW: "W \<in> top1_S2_topology" and hP_sub: "P \<in> subspace_topology top1_S2 top1_S2_topology W"
    from hP_sub obtain V where hV: "V \<in> top1_S2_topology" "P = W \<inter> V"
      unfolding subspace_topology_def by (by100 blast)
    have "finite {W, V}" by (by100 simp)
    moreover have "{W, V} \<noteq> {}" by (by100 simp)
    moreover have "{W, V} \<subseteq> top1_S2_topology" using hW hV(1) by (by100 blast)
    ultimately have "\<Inter>{W, V} \<in> top1_S2_topology"
      using hTopS2 unfolding is_topology_on_def by (by100 blast)
    moreover have "\<Inter>{W, V} = W \<inter> V" by (by100 blast)
    ultimately show "P \<in> top1_S2_topology" using hV(2) by (by100 simp)
  qed
  have hP1_open: "P1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>P2 = complement of P1 in S2-(A\<union>B). Since P1 is a path component and lpc, complement is open.\<close>
  have hP2_open: "P2 \<in> top1_S2_topology"
  proof -
    have hP2_eq: "P2 = (top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hP(3,4) hP1_eq_pc by (by100 blast)
    have "(top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP2_eq by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>C-{a1,a3} \<subseteq> P2 was established in the obtain above.\<close>
  \<comment> \<open>closure(P1) = P1 \<union> (A\<union>B), using simple_closed_curve_boundary_meets_component.\<close>
  have hcl_P1: "closure_on top1_S2 top1_S2_topology P1 = P1 \<union> (?A \<union> ?B)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology P1"
    \<comment> \<open>cl(P1) \<subseteq> P1 \<union> (A\<union>B): P2 open \<Rightarrow> S2-P2 closed \<Rightarrow> cl(P1) \<subseteq> S2-P2 = P1\<union>(A\<union>B).\<close>
    have hP1_AB_eq: "P1 \<union> (?A \<union> ?B) = top1_S2 - P2"
    proof -
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have "top1_S2 - P2 = (top1_S2 - (P1 \<union> P2)) \<union> P1" using hP(3) hP1_sub_S2 by (by100 force)
      also have "\<dots> = (?A \<union> ?B) \<union> P1"
      proof -
        have "top1_S2 - (P1 \<union> P2) = top1_S2 - (top1_S2 - (?A \<union> ?B))" using hP(4) by (by100 blast)
        also have "\<dots> = ?A \<union> ?B"
        proof -
          have "?A \<union> ?B \<subseteq> top1_S2" using hA_sub assms(8) by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    moreover have hcl_S2_P2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - P2)"
    proof -
      have hP2_sub_S2: "P2 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have hsub: "top1_S2 - P2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - P2) = P2" using hP2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hP2_open by (by100 simp)
    qed
    moreover have "P1 \<subseteq> top1_S2 - P2"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2 - P2"
      using closure_on_subset_of_closed[OF hcl_S2_P2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology P1 \<subseteq> P1 \<union> (?A \<union> ?B)"
      using hP1_AB_eq by (by100 blast)
    thus "z \<in> P1 \<union> (?A \<union> ?B)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology P1\<close> by (by100 blast)
  next
    fix z assume "z \<in> P1 \<union> (?A \<union> ?B)"
    hence "z \<in> P1 \<or> z \<in> ?A \<union> ?B" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology P1"
    proof
      assume "z \<in> P1"
      thus ?thesis using subset_closure_on[of P1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?A \<union> ?B"
      hence "z \<in> top1_S2" using hA_sub assms(8) by (by100 blast)
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology P1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hP1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U P1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> P1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hAB_scc hP(5) hP(6)
                hP(3) hP(4) hP(1) hP(2) hP1_open hP2_open \<open>z \<in> ?A \<union> ?B\<close> hV_open hzV])
          thus "intersects V P1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a4 \<notin> A\<union>B: from intersection assumptions and distinctness.\<close>
  have ha4_not_AB: "a4 \<notin> ?A \<union> ?B"
  proof -
    \<comment> \<open>a4 \<in> e34, e12\<inter>e34 = {}, so a4 \<notin> e12.\<close>
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have "a4 \<notin> e12" using assms(22) ha4_e34 by (by100 blast)
    \<comment> \<open>a4 \<in> e23\<inter>e34 = {a3}, but a4 \<noteq> a3, so a4 \<notin> e23.\<close>
    moreover have "a4 \<notin> e23"
    proof assume "a4 \<in> e23"
      hence "a4 \<in> e23 \<inter> e34" using ha4_e34 by (by100 blast)
      hence "a4 = a3" using assms(25) by (by100 blast)
      thus False using hdist(6) by (by100 blast)
    qed
    \<comment> \<open>a4 \<in> e41, e13\<inter>e41 = {a1}, a4 \<noteq> a1, so a4 \<notin> e13.\<close>
    moreover have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a4 \<notin> e13"
    proof assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using ha4_e41 by (by100 blast)
      hence "a4 = a1" using assms(31) by (by100 blast)
      thus False using hdist(3) by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} cannot lie in P1: a4 \<in> closure(e24-{a2,a4}) but a4 \<notin> P1\<union>(A\<union>B).\<close>
  have ha4_in_cl_e24: "a4 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_P1: "\<not>(e24 - {a2, a4} \<subseteq> P1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> P1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology P1"
      by (rule closure_on_mono[OF h])
    hence "a4 \<in> closure_on top1_S2 top1_S2_topology P1"
      using ha4_in_cl_e24 by (by100 blast)
    hence "a4 \<in> P1 \<union> (?A \<union> ?B)" using hcl_P1 by (by100 blast)
    moreover have "a4 \<notin> P1"
    proof -
      have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a4 \<in> ?C - {a1, a3}" using ha4_e41 hdist(3) hdist(6) by (by100 blast)
      hence "a4 \<in> P2" using hCm_in_P2 by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "a4 \<in> ?A \<union> ?B" by (by100 blast)
    thus False using ha4_not_AB by (by100 blast)
  qed
  \<comment> \<open>Similarly for B\<union>C: get R1, R2 from Theorem_63_5.\<close>
  have hBC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus assms(14) assms(8)
        hC_arc hC_sub hBC_int hdist(2) assms(20) hC_ep])
  have hC_closed: "closedin_on top1_S2 top1_S2_topology ?C"
    by (rule arc_in_S2_closed[OF hC_sub hC_arc])
  have hC_conn: "top1_connected_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    using arc_connected[OF hC_arc] .
  have hC_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hC_sub hC_arc])
  have hBC_card: "card (?B \<inter> ?C) = 2"
    using hBC_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components for S2-(B\<union>C), then choose labels so A-{a1,a3} \<subseteq> R2.\<close>
  have hAm_sub_BC: "?A - {a1, a3} \<subseteq> top1_S2 - (?B \<union> ?C)"
  proof -
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    thus ?thesis using hA_sub by (by100 blast)
  qed
  have hAm_in_raw_pre: "\<exists>R1' R2'. R1' \<noteq> {} \<and> R2' \<noteq> {} \<and> R1' \<inter> R2' = {}
      \<and> R1' \<union> R2' = top1_S2 - (?B \<union> ?C)
      \<and> top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')
      \<and> top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')"
    using Theorem_63_5_two_closed_connected[OF assms(1) hB_closed hC_closed
        hB_conn hC_conn hBC_card hB_no_sep hC_no_sep] by (by100 metis)
  obtain R1 R2 where hR: "R1 \<noteq> {}" "R2 \<noteq> {}" "R1 \<inter> R2 = {}"
      "R1 \<union> R2 = top1_S2 - (?B \<union> ?C)"
      "top1_connected_on R1 (subspace_topology top1_S2 top1_S2_topology R1)"
      "top1_connected_on R2 (subspace_topology top1_S2 top1_S2_topology R2)"
      and hAm_in_R2: "?A - {a1, a3} \<subseteq> R2"
  proof -
    from hAm_in_raw_pre obtain R1' R2' where hR': "R1' \<noteq> {}" "R2' \<noteq> {}" "R1' \<inter> R2' = {}"
        "R1' \<union> R2' = top1_S2 - (?B \<union> ?C)"
        "top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')"
        "top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')" by (by100 metis)
    have hBC_closed_loc: "closedin_on top1_S2 top1_S2_topology (?B \<union> ?C)"
      by (rule closedin_on_Un[OF hTopS2 hB_closed hC_closed])
    have hBC_compl_open_loc: "top1_S2 - (?B \<union> ?C) \<in> top1_S2_topology"
      using hBC_closed_loc unfolding closedin_on_def by (by100 blast)
    have hBC_not_conn: "\<not> top1_connected_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      using Theorem_61_3_JordanSeparation_S2[OF assms(1) hBC_scc]
      unfolding top1_separates_on_def by (by100 blast)
    have hR1'_open: "R1' \<in> top1_S2_topology" and hR2'_open: "R2' \<in> top1_S2_topology"
      using S2_two_component_open[OF hBC_compl_open_loc _ hR'(1,2,3,4,5,6) hBC_not_conn]
      by (by100 blast)+
    have hTBC_loc: "is_topology_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hR1'_oBC: "R1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
    proof -
      have "R1' = (top1_S2 - (?B \<union> ?C)) \<inter> R1'" using hR'(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hR1'_open by (by100 blast)
    qed
    have hR2'_oBC: "R2' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
    proof -
      have "R2' = (top1_S2 - (?B \<union> ?C)) \<inter> R2'" using hR'(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hR2'_open by (by100 blast)
    qed
    have hBC_sep: "top1_is_separation_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1' R2'"
      unfolding top1_is_separation_on_def
      using hR1'_oBC hR2'_oBC hR'(1,2,3,4) by (by100 blast)
    have hAm_conn_BC: "top1_connected_on (?A - {a1, a3})
        (subspace_topology (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
            (?A - {a1, a3}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (?A - {a1, a3}) =
          subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
              (?A - {a1, a3})"
        using subspace_topology_trans[of "?A - {a1, a3}" "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
            hAm_sub_BC by (by100 simp)
      thus ?thesis using arc_minus_endpoints_connected[OF hS2_strict hS2_haus hA_sub hA_arc hA_ep hdist(2)]
        by (by100 simp)
    qed
    have hAm_raw: "?A - {a1, a3} \<subseteq> R1' \<or> ?A - {a1, a3} \<subseteq> R2'"
      using Lemma_23_2[OF hTBC_loc hBC_sep hAm_sub_BC hAm_conn_BC] by (by100 blast)
    from hAm_raw show ?thesis
    proof
      assume "?A - {a1, a3} \<subseteq> R1'"
      show ?thesis
        by (rule that[of R2' R1'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R1'\<close> in \<open>by100 blast\<close>)+
    next
      assume "?A - {a1, a3} \<subseteq> R2'"
      show ?thesis
        by (rule that[of R1' R2'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R2'\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  have hBC_closed_S2: "closedin_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule closedin_on_Un[OF hTopS2 hB_closed hC_closed])
  have hBC_compl_open: "top1_S2 - (?B \<union> ?C) \<in> top1_S2_topology"
    using hBC_closed_S2 unfolding closedin_on_def by (by100 blast)
  have hBC_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hBC_compl_open])
       (by100 blast)
  have hTBC: "is_topology_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_R where hx_R: "x_R \<in> R1" using hR(1) by (by100 blast)
  have hx_R_W: "x_R \<in> top1_S2 - (?B \<union> ?C)" using hx_R hR(4) by (by100 blast)
  \<comment> \<open>R1 = component\_of(x\_R) in S2-(B\<union>C). Same contradiction argument as for P1.\<close>
  have hR1_eq_comp: "R1 = top1_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    have hR1_sub_BC: "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    have hR1_conn_BC: "top1_connected_on R1
        (subspace_topology (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1"
        using subspace_topology_trans[of R1 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
            hR1_sub_BC by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    have "R1 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      by (rule top1_connected_subspace_subset_component_of[OF hR1_sub_BC hx_R hR1_conn_BC])
    moreover have "top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<subseteq> R1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R" "y \<notin> R1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?B \<union> ?C)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "y \<in> R2" using hR(4) hy(2) by (by100 blast)
      have hR2_sub: "R2 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
      have hR2_conn_sub: "top1_connected_on R2
          (subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R2 =
            subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2"
          using subspace_topology_trans[of R2 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
              hR2_sub by (by100 simp)
        thus ?thesis using hR(6) by (by100 simp)
      qed
      have "R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using top1_connected_subspace_subset_component_of[OF hR2_sub \<open>y \<in> R2\<close> hR2_conn_sub]
            top1_component_of_on_eq_of_mem[OF hTBC hy(1)] by (by100 simp)
      hence "R1 \<union> R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using \<open>R1 \<subseteq> top1_component_of_on _ _ x_R\<close> by (by100 blast)
      hence "top1_S2 - (?B \<union> ?C) = top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using hR(4) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      proof -
        have "top1_connected_on
            (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R)
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
                (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R))"
          by (rule top1_component_of_on_connected[OF hTBC hx_R_W])
        thus ?thesis
          using \<open>top1_S2 - (?B \<union> ?C) = top1_component_of_on _ _ x_R\<close>
              subspace_topology_trans[of "top1_S2 - (?B \<union> ?C)" "top1_S2 - (?B \<union> ?C)"
                  top1_S2 top1_S2_topology] by (by100 simp)
      qed
      moreover have "\<not> top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hBC_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_eq_pc: "R1 = top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTBC]]
    have "\<forall>z \<in> top1_S2 - (?B \<union> ?C).
        top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z =
        top1_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z" by (by100 blast)
    thus ?thesis using hR1_eq_comp hBC_open_lpc hx_R_W by (by100 metis)
  qed
  have hR1_open: "R1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    hence "R1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      using hR1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  have hR2_open: "R2 \<in> top1_S2_topology"
  proof -
    have "R2 = (top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      using hR(3,4) hR1_eq_pc by (by100 blast)
    moreover have "(top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    ultimately have "R2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  \<comment> \<open>hAm\_in\_R2 was established in the obtain above.\<close>
  have hcl_R1: "closure_on top1_S2 top1_S2_topology R1 = R1 \<union> (?B \<union> ?C)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology R1"
    have hR1_BC_eq: "R1 \<union> (?B \<union> ?C) = top1_S2 - R2"
    proof -
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have "top1_S2 - R2 = (top1_S2 - (R1 \<union> R2)) \<union> R1" using hR(3) hR1_sub_S2 by (by100 force)
      also have "\<dots> = (?B \<union> ?C) \<union> R1"
      proof -
        have "top1_S2 - (R1 \<union> R2) = top1_S2 - (top1_S2 - (?B \<union> ?C))" using hR(4) by (by100 blast)
        also have "\<dots> = ?B \<union> ?C"
        proof -
          have "?B \<union> ?C \<subseteq> top1_S2" using assms(8) hC_sub by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    have hcl_S2_R2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - R2)"
    proof -
      have hR2_sub_S2: "R2 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have hsub: "top1_S2 - R2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - R2) = R2" using hR2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hR2_open by (by100 simp)
    qed
    have "R1 \<subseteq> top1_S2 - R2"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2 - R2"
      using closure_on_subset_of_closed[OF hcl_S2_R2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> R1 \<union> (?B \<union> ?C)"
      using hR1_BC_eq by (by100 blast)
    thus "z \<in> R1 \<union> (?B \<union> ?C)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology R1\<close> by (by100 blast)
  next
    fix z assume "z \<in> R1 \<union> (?B \<union> ?C)"
    hence "z \<in> R1 \<or> z \<in> ?B \<union> ?C" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology R1"
    proof
      assume "z \<in> R1"
      thus ?thesis using subset_closure_on[of R1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?B \<union> ?C"
      hence "z \<in> top1_S2" using assms(8) hC_sub by (by100 blast)
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology R1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hR1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U R1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> R1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hBC_scc hR(5) hR(6)
                hR(3) hR(4) hR(1) hR(2) hR1_open hR2_open \<open>z \<in> ?B \<union> ?C\<close> hV_open hzV])
          thus "intersects V R1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a2 \<notin> B\<union>C.\<close>
  have ha2_not_BC: "a2 \<notin> ?B \<union> ?C"
  proof -
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>a2 \<in> e12, e13\<inter>e12 = {a1}, a2 \<noteq> a1, so a2 \<notin> e13.\<close>
    have "a2 \<notin> e13"
    proof assume "a2 \<in> e13"
      hence "a2 \<in> e13 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(28) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    moreover have "a2 \<notin> e41"
    proof assume "a2 \<in> e41"
      hence "a2 \<in> e41 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(27) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    \<comment> \<open>a2 \<in> e12, e12\<inter>e34 = {}, so a2 \<notin> e34.\<close>
    moreover have "a2 \<notin> e34" using assms(22) ha2_e12 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have ha2_in_cl_e24: "a2 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_R1: "\<not>(e24 - {a2, a4} \<subseteq> R1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> R1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology R1"
      by (rule closure_on_mono[OF h])
    hence "a2 \<in> closure_on top1_S2 top1_S2_topology R1"
      using ha2_in_cl_e24 by (by100 blast)
    hence "a2 \<in> R1 \<union> (?B \<union> ?C)" using hcl_R1 by (by100 blast)
    moreover have "a2 \<notin> R1"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a2 \<in> ?A - {a1, a3}" using ha2_e12 hdist(1) hdist(4) by (by100 blast)
      hence "a2 \<in> R2" using hAm_in_R2 by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    ultimately have "a2 \<in> ?B \<union> ?C" by (by100 blast)
    thus False using ha2_not_BC by (by100 blast)
  qed
  \<comment> \<open>Step 4: P1 and R1 are each theta components, and they are distinct.\<close>
  \<comment> \<open>P1 \<subseteq> S2-(A\<union>B) and P1 \<inter> (C-{a1,a3}) = {} (since C-{a1,a3} \<subseteq> P2), so P1 \<subseteq> S2-Y.\<close>
  have hP1_sub_Y_compl: "P1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
    moreover have "P1 \<inter> (?C - {a1, a3}) = {}" using hCm_in_P2 hP(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?A \<union> ?B" using hAB_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_sub_Y_compl: "R1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    moreover have "R1 \<inter> (?A - {a1, a3}) = {}" using hAm_in_R2 hR(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?B \<union> ?C" using hBC_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>P1 is connected \<subseteq> S2-Y = U\<union>V\<union>W (disjoint open), so P1 \<subseteq> one of U,V,W.\<close>
  \<comment> \<open>Since P1 is a component of S2-(A\<union>B) \<supseteq> S2-Y, and U,V,W are components of S2-Y,
     P1 is exactly one of U,V,W. Similarly R1.\<close>
  \<comment> \<open>U, V, W are open in S2: Y is closed, S2-Y is open lpc, components are open.\<close>
  have hY_closed: "closedin_on top1_S2 top1_S2_topology ?Y"
  proof -
    have hAC_closed: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?C)"
      by (rule closedin_on_Un[OF hTopS2 hA_closed hC_closed])
    have hABC_closed: "closedin_on top1_S2 top1_S2_topology ((?A \<union> ?C) \<union> ?B)"
      by (rule closedin_on_Un[OF hTopS2 hAC_closed hB_closed])
    moreover have "?Y = (?A \<union> ?C) \<union> ?B" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hY_compl_open: "top1_S2 - ?Y \<in> top1_S2_topology"
    using hY_closed unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>NEW APPROACH: P1 is a connected component of S2-Y, hence equals one of U,V,W.
     Key: S2-Y = P1 \<union> (P2 \<inter> (S2-Y)) where both pieces are open in S2-Y.\<close>
  have hP2_cap_Y: "P2 \<inter> (top1_S2 - ?Y) = (top1_S2 - ?Y) - P1"
    using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
  have hP1_open_in_Y: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "P1 = (top1_S2 - ?Y) \<inter> P1" using hP1_sub_Y_compl by (by100 blast)
    thus ?thesis unfolding subspace_topology_def using hP1_open by (by100 blast)
  qed
  have hVW_open_in_Y: "(top1_S2 - ?Y) - P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "(top1_S2 - ?Y) - P1 = (top1_S2 - ?Y) \<inter> P2"
      using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
    also have "\<dots> = (top1_S2 - ?Y) \<inter> (top1_S2 \<inter> P2)" using hP(4) by (by100 blast)
    finally show ?thesis unfolding subspace_topology_def using hP2_open by (by100 blast)
  qed
  \<comment> \<open>P1 is a connected component of S2-Y (maximal connected: any connected superset
     in S2-Y would cross the P1/(P2\<inter>S2-Y) separation).\<close>
  have hP1_is_comp: "P1 = U \<or> P1 = V \<or> P1 = W"
  proof -
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W. By partition, P1 \<subseteq> U or V or W.\<close>
    \<comment> \<open>Conversely, if P1 \<subseteq> U and U \<noteq> P1, then \<exists>z \<in> U-P1. z \<in> P2\<inter>(S2-Y).
       But U is connected and meets both P1 and P2\<inter>(S2-Y), which are open in S2-Y.
       That contradicts U's connectivity.\<close>
    have hP1_in_UVW: "P1 \<subseteq> U \<union> V \<union> W" using hP1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>P1 is connected, P1 \<subseteq> S2-Y which is separated as P1 \<union> (S2-Y-P1).
       Any connected subset of S2-Y is in P1 or in S2-Y-P1.\<close>
    have hTY: "is_topology_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_ne: "(top1_S2 - ?Y) - P1 \<noteq> {}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hP1_eq_Y: "top1_S2 - ?Y \<subseteq> P1" by (by100 blast)
      \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W (disjoint open). Lemma\_23\_2 on {U, V\<union>W}: P1 \<subseteq> U or V\<union>W.\<close>
      have hVW_open_loc: "V \<union> W \<in> top1_S2_topology"
      proof -
        from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
          unfolding is_topology_on_def by (by100 blast)
        from this[of "{V, W}"] hUVW(12,13) have "\<Union>{V, W} \<in> top1_S2_topology" by (by100 blast)
        moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hU_oY: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
      proof -
        have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        hence "U = (top1_S2 - ?Y) \<inter> U" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
      qed
      have hVW_oY: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
      proof -
        have "V \<union> W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        hence "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hVW_open_loc by (by100 blast)
      qed
      have hU_VW_sep: "top1_is_separation_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
      proof -
        have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
        moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
        ultimately show ?thesis unfolding top1_is_separation_on_def
          using hU_oY hVW_oY hUVW(1) by (by100 blast)
      qed
      have hP1_conn_Y: "top1_connected_on P1
          (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
              hP1_sub_Y_compl by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTY hU_VW_sep hP1_sub_Y_compl hP1_conn_Y]
      have "P1 \<subseteq> U \<or> P1 \<subseteq> V \<union> W" by (by100 blast)
      thus False
      proof
        assume "P1 \<subseteq> U"
        hence "V \<subseteq> P1" using hP1_eq_Y hUVW(7) by (by100 blast)
        hence "V \<subseteq> U" using \<open>P1 \<subseteq> U\<close> by (by100 blast)
        hence "V \<inter> U \<noteq> {}" using hUVW(2) by (by100 blast)
        thus False using hUVW(4) by (by100 blast)
      next
        assume "P1 \<subseteq> V \<union> W"
        hence "U \<subseteq> P1" using hP1_eq_Y hUVW(7) by (by100 blast)
        hence "U \<subseteq> V \<union> W" using \<open>P1 \<subseteq> V \<union> W\<close> by (by100 blast)
        hence "U \<inter> (V \<union> W) \<noteq> {}" using hUVW(1) by (by100 blast)
        moreover have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
        ultimately show False by (by100 blast)
      qed
    qed
    have hY_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
        P1 ((top1_S2 - ?Y) - P1)"
      unfolding top1_is_separation_on_def
      using hP1_open_in_Y hVW_open_in_Y hP(1) hVW_ne hP1_sub_Y_compl by (by100 blast)
    \<comment> \<open>Each of U, V, W is connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or \<subseteq> (S2-Y)-P1.\<close>
    \<comment> \<open>Each of U,V,W connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or (S2-Y)-P1.\<close>
    have hU_conn_Y: "top1_connected_on U
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology U =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U"
        using subspace_topology_trans[of U "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(8) by (by100 simp)
    qed
    have hU_sub_Y: "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hU_side: "U \<subseteq> P1 \<or> U \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hU_sub_Y hU_conn_Y] by (by100 blast)
    have hV_conn_Y: "top1_connected_on V
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V)"
    proof -
      have "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology V =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V"
        using subspace_topology_trans[of V "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(9) by (by100 simp)
    qed
    have hV_sub_Y: "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hV_side: "V \<subseteq> P1 \<or> V \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hV_sub_Y hV_conn_Y] by (by100 blast)
    have hW_conn_Y: "top1_connected_on W
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W)"
    proof -
      have "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology W =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W"
        using subspace_topology_trans[of W "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(10) by (by100 simp)
    qed
    have hW_sub_Y: "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hW_side: "W \<subseteq> P1 \<or> W \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hW_sub_Y hW_conn_Y] by (by100 blast)
    \<comment> \<open>P1 = component\_of\_{S2-Y}(x\_P): use containment in P1's component of S2-(A\<union>B).\<close>
    have hP1_comp_Y: "P1 = top1_component_of_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
    proof -
      have hP1_sub_Y: "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      have hP1_conn_Y: "top1_connected_on P1
          (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology] hP1_sub_Y
          by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      have "P1 \<subseteq> top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
        by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_Y hx_P hP1_conn_Y])
      moreover have "top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> P1"
      proof -
        \<comment> \<open>comp\_{S2-Y}(x\_P) \<subseteq> comp\_{S2-(A\<union>B)}(x\_P) = P1.\<close>
        have "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq>
            top1_S2 - ?Y" by (rule top1_component_of_on_subset)
        moreover have "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have hconn_sub: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
              (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
            by (rule top1_component_of_on_connected[OF hTY])
               (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
          thus ?thesis
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - ?Y" top1_S2 top1_S2_topology]
                top1_component_of_on_subset[of "top1_S2 - ?Y"] by (by100 simp)
        qed
        moreover have "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (rule top1_component_of_on_self_mem[OF hTY]) (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
        moreover have "top1_S2 - ?Y \<subseteq> top1_S2 - (?A \<union> ?B)" by (by100 blast)
        ultimately have hsub_AB: "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> top1_S2 - (?A \<union> ?B)"
          and hconn_AB: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
          and hxP_in_comp: "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (by100 blast)+
        have hconn_AB': "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                (top1_component_of_on (top1_S2 - ?Y)
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P) =
              subspace_topology (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)"
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology] hsub_AB by (by100 simp)
          thus ?thesis using hconn_AB by (by100 simp)
        qed
        show ?thesis
          using top1_connected_subspace_subset_component_of[OF hsub_AB hxP_in_comp hconn_AB']
              hP1_eq_comp by (by100 simp)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>U,V,W open (hUVW(11,12,13)) + disjoint + P1 connected \<subseteq> U\<union>V\<union>W \<Rightarrow> P1 \<subseteq> one.
       Then that one \<subseteq> P1 (from hU/V/W\_side). So P1 = that one.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W with U,V,W pairwise disjoint and open in S2.
       By connectivity, P1 must be \<subseteq> one of them. Then that one \<subseteq> P1 from side facts.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W (disjoint open). By Lemma\_23\_2 applied twice.\<close>
    \<comment> \<open>Form separation {U, V\<union>W} of S2-Y.\<close>
    have hU_open_Y: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U = (top1_S2 - ?Y) \<inter> U" using hU_sub_Y by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_open_Y: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" using hV_sub_Y hW_sub_Y by (by100 blast)
      moreover have "V \<union> W \<in> top1_S2_topology"
      proof -
        from hTopS2 have hunion: "\<And>U. U \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>U \<in> top1_S2_topology"
          unfolding is_topology_on_def by (by100 blast)
        have "{V, W} \<subseteq> top1_S2_topology" using hUVW(12,13) by (by100 blast)
        from hunion[OF this] have "\<Union>{V, W} \<in> top1_S2_topology" .
        moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hUVW_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_open_Y hVW_open_Y hUVW(1) by (by100 blast)
    qed
    \<comment> \<open>P1 connected in S2-Y, Lemma\_23\_2 gives P1 \<subseteq> U or P1 \<subseteq> V\<union>W.\<close>
    have hP1_conn_Y_full: "top1_connected_on P1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology P1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
        using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hP1_sub_Y_compl by (by100 simp)
      thus ?thesis using hP(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTY hUVW_sep hP1_sub_Y_compl hP1_conn_Y_full]
    have "P1 \<subseteq> U \<or> P1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hPU: "P1 \<subseteq> U"
      \<comment> \<open>U \<subseteq> P1: from hU\_side, x\_P \<in> U (since P1 \<subseteq> U and x\_P \<in> P1).\<close>
      have "x_P \<in> U" using hPU hx_P by (by100 blast)
      hence "U \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
      hence "U \<subseteq> P1" using hU_side by (by100 force)
      thus ?thesis using hPU by (by100 blast)
    next
      assume "P1 \<subseteq> V \<union> W"
      \<comment> \<open>Apply Lemma\_23\_2 again: separation {V, W} of V\<union>W.\<close>
      have hV_open_VW: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(12) by (by100 blast)
      qed
      have hW_open_VW: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(13) by (by100 blast)
      qed
      have hTVW: "is_topology_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hV_sub_Y hW_sub_Y in \<open>by100 blast\<close>)
      have hVW_sep: "top1_is_separation_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
        unfolding top1_is_separation_on_def
        using hV_open_VW hW_open_VW hUVW(2,3,5) by (by100 blast)
      have hP1_sub_VW: "P1 \<subseteq> V \<union> W" by (rule \<open>P1 \<subseteq> V \<union> W\<close>)
      have hP1_conn_VW: "top1_connected_on P1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1"
          using subspace_topology_trans[of P1 "V \<union> W" top1_S2 top1_S2_topology]
              hP1_sub_VW by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVW hVW_sep hP1_sub_VW hP1_conn_VW]
      have "P1 \<subseteq> V \<or> P1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume hPV: "P1 \<subseteq> V"
        have "x_P \<in> V" using hPV hx_P by (by100 blast)
        hence "V \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "V \<subseteq> P1" using hV_side by (by100 force)
        thus ?thesis using hPV by (by100 blast)
      next
        assume hPW: "P1 \<subseteq> W"
        have "x_P \<in> W" using hPW hx_P by (by100 blast)
        hence "W \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "W \<subseteq> P1" using hW_side by (by100 force)
        thus ?thesis using hPW by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Same argument for R1.\<close>
  have hR1_is_comp: "R1 = U \<or> R1 = V \<or> R1 = W"
  proof -
    have hR1_in_UVW: "R1 \<subseteq> U \<union> V \<union> W" using hR1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>Same 2\<times>Lemma\_23\_2 approach. Re-derive shared infrastructure.\<close>
    have hTYr: "is_topology_on (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_open_r: "V \<union> W \<in> top1_S2_topology"
    proof -
      from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
        unfolding is_topology_on_def by (by100 blast)
      from this[of "{V, W}"] hUVW(12,13) have "\<Union>{V, W} \<in> top1_S2_topology" by (by100 blast)
      moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hU_oY: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "U = (top1_S2 - ?Y) \<inter> U" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_oY: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hVW_open_r by (by100 blast)
    qed
    have hUVW_sr: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_oY hVW_oY hUVW(1) by (by100 blast)
    qed
    have hR1_cY: "top1_connected_on R1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1"
        using subspace_topology_trans[of R1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hR1_sub_Y_compl by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTYr hUVW_sr hR1_sub_Y_compl hR1_cY]
    have "R1 \<subseteq> U \<or> R1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hRU: "R1 \<subseteq> U"
      have "U \<subseteq> R1"
      proof -
        have "x_R \<in> U" using hRU hx_R by (by100 blast)
        have hU_sub_BC: "U \<subseteq> top1_S2 - (?B \<union> ?C)"
          using hR1_sub_Y_compl hUVW(7) by (by100 blast)
        have hU_conn_BC: "top1_connected_on U
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology U =
              subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U"
            using subspace_topology_trans[of U "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                hU_sub_BC by (by100 simp)
          thus ?thesis using hUVW(8) by (by100 simp)
        qed
        from top1_connected_subspace_subset_component_of[OF hU_sub_BC \<open>x_R \<in> U\<close> hU_conn_BC]
        show ?thesis using hR1_eq_comp by (by100 simp)
      qed
      thus ?thesis using hRU by (by100 blast)
    next
      assume "R1 \<subseteq> V \<union> W"
      have hTVWr: "is_topology_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hUVW(7) in \<open>by100 blast\<close>)
      have hVW_sr: "top1_is_separation_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        hence hVo: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(12) by (by100 blast)
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        hence hWo: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(13) by (by100 blast)
        show ?thesis unfolding top1_is_separation_on_def
          using hVo hWo hUVW(2,3,5) by (by100 blast)
      qed
      have hR1_cVW: "top1_connected_on R1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1"
          using subspace_topology_trans[of R1 "V \<union> W" top1_S2 top1_S2_topology]
              \<open>R1 \<subseteq> V \<union> W\<close> by (by100 simp)
        thus ?thesis using hR(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVWr hVW_sr \<open>R1 \<subseteq> V \<union> W\<close> hR1_cVW]
      have "R1 \<subseteq> V \<or> R1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume "R1 \<subseteq> V"
        have "V \<subseteq> R1"
        proof -
          have "x_R \<in> V" using \<open>R1 \<subseteq> V\<close> hx_R by (by100 blast)
          have hV_sub_BC: "V \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hV_conn_BC: "top1_connected_on V
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology V =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V"
              using subspace_topology_trans[of V "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hV_sub_BC by (by100 simp)
            thus ?thesis using hUVW(9) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hV_sub_BC \<open>x_R \<in> V\<close> hV_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> V\<close> by (by100 blast)
      next
        assume "R1 \<subseteq> W"
        have "W \<subseteq> R1"
        proof -
          have "x_R \<in> W" using \<open>R1 \<subseteq> W\<close> hx_R by (by100 blast)
          have hW_sub_BC: "W \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hW_conn_BC: "top1_connected_on W
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology W =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W"
              using subspace_topology_trans[of W "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hW_sub_BC by (by100 simp)
            thus ?thesis using hUVW(10) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hW_sub_BC \<open>x_R \<in> W\<close> hW_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> W\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>P1 \<noteq> R1: closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C).
     If P1 = R1 then closure(P1) \<subseteq> (A\<union>B) \<inter> (B\<union>C) gives boundary \<subseteq> B, contradicting
     that an open nonempty subset of S2 has boundary larger than an arc.\<close>
  have hP1_ne_R1: "P1 \<noteq> R1"
  proof
    assume "P1 = R1"
    \<comment> \<open>closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C). If equal:
       P1\<union>(A\<union>B) = P1\<union>(B\<union>C), so (A\<union>B) \<subseteq> P1\<union>(B\<union>C) and (B\<union>C) \<subseteq> P1\<union>(A\<union>B).
       Hence A-B \<subseteq> P1\<union>C and C-B \<subseteq> P1\<union>A. But P1 \<subseteq> S2-Y, A,C \<subseteq> Y, P1 \<inter> Y = {}.
       So A-B \<subseteq> C and C-B \<subseteq> A. Combined with A\<inter>C = {a1,a3} and B endpoints = {a1,a3}:
       A-{a1,a3} \<subseteq> C, but A \<inter> C = {a1,a3}, so A-{a1,a3} \<subseteq> C \<inter> A = {a1,a3}.
       Hence A \<subseteq> {a1,a3} \<union> B. But A is an arc with \<ge> 3 points. Contradiction.\<close>
    have "closure_on top1_S2 top1_S2_topology P1 = closure_on top1_S2 top1_S2_topology R1"
      using \<open>P1 = R1\<close> by (by100 simp)
    hence "P1 \<union> (?A \<union> ?B) = P1 \<union> (?B \<union> ?C)" using hcl_P1 hcl_R1 \<open>P1 = R1\<close> by (by100 simp)
    hence "?A \<subseteq> P1 \<union> ?B \<union> ?C" by (by100 blast)
    moreover have "P1 \<inter> ?A = {}" using hP1_sub_Y_compl by (by100 blast)
    ultimately have hA_sub_BC: "?A \<subseteq> ?B \<union> ?C" by (by100 blast)
    \<comment> \<open>But A \<inter> (B\<union>C) = (A\<inter>B) \<union> (A\<inter>C) = {a1,a3} \<union> {a1,a3} = {a1,a3}.\<close>
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    hence "?A \<subseteq> {a1, a3}" using hA_sub_BC by (by100 blast)
    \<comment> \<open>But A = e12 \<union> e23 has \<ge> 3 points (it's an arc).\<close>
    moreover have "a2 \<in> ?A" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a2 \<notin> {a1, a3}" using hdist(1,4) by (by100 blast)
    ultimately show False by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} lies in the third component (not P1, not R1).\<close>
  have he24_conn: "top1_connected_on (e24 - {a2, a4})
      (subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  \<comment> \<open>e24 \<inter> Y = {a2, a4}: from intersection assumptions.\<close>
  have he24_Y_int: "e24 \<inter> ?Y = {a2, a4}"
  proof -
    \<comment> \<open>e24 \<inter> (e12\<union>e23\<union>e13\<union>e41\<union>e34)
       = (e24\<inter>e12) \<union> (e24\<inter>e23) \<union> (e24\<inter>e13) \<union> (e24\<inter>e41) \<union> (e24\<inter>e34)\<close>
    have "e24 \<inter> e13 = {}"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_not_e24: "a1 \<notin> e24"
      proof assume "a1 \<in> e24"
        hence "a1 \<in> e24 \<inter> e12" using ha1_e12 by (by100 blast)
        hence "a1 = a2" using assms(33) by (by100 blast)
        thus False using hdist(1) by (by100 blast)
      qed
      have ha3_e23: "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha3_not_e24: "a3 \<notin> e24"
      proof assume "a3 \<in> e24"
        hence "a3 \<in> e24 \<inter> e23" using ha3_e23 by (by100 blast)
        hence "a3 = a2" using assms(34) by (by100 blast)
        thus False using hdist(4) by (by100 blast)
      qed
      \<comment> \<open>a2 \<notin> e13: from ha2_not_BC. a4 \<notin> e13: from ha4_not_AB.\<close>
      have "a2 \<notin> e13" using ha2_not_BC by (by100 blast)
      moreover have "a4 \<notin> e13" using ha4_not_AB by (by100 blast)
      ultimately have "\<forall>x \<in> {a1,a2,a3,a4}. x \<notin> e24 \<inter> e13"
        using ha1_not_e24 ha3_not_e24 by (by100 blast)
      thus ?thesis using assms(32) by (by100 blast)
    qed
    hence he24_e13: "e24 \<inter> e13 = {}" .
    have "e24 \<inter> ?Y = (e24 \<inter> e12) \<union> (e24 \<inter> e23) \<union> (e24 \<inter> e13) \<union> (e24 \<inter> e41) \<union> (e24 \<inter> e34)"
      by (by100 blast)
    also have "\<dots> = {a2} \<union> {a2} \<union> {} \<union> {a4} \<union> {a4}"
      using assms(33,34,35,36) he24_e13 by (by100 simp)
    also have "\<dots> = {a2, a4}" by (by100 blast)
    finally show ?thesis .
  qed
  have ha2_in_Y: "a2 \<in> ?Y"
    using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha4_in_Y: "a4 \<in> ?Y"
    using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have he24_in_Y_compl: "e24 - {a2, a4} \<subseteq> top1_S2 - ?Y"
    using he24_Y_int assms(9) by (by100 blast)
  \<comment> \<open>Let T be the theta component \<noteq> P1, \<noteq> R1.\<close>
  obtain T where hT_is: "T \<in> {U, V, W}" "T \<noteq> P1" "T \<noteq> R1"
      and hT_conn: "top1_connected_on T (subspace_topology top1_S2 top1_S2_topology T)"
      and hT_ne: "T \<noteq> {}"
      and hT_union: "P1 \<union> R1 \<union> T = top1_S2 - ?Y"
      and hT_disj: "P1 \<inter> T = {}" "R1 \<inter> T = {}"
  proof -
    \<comment> \<open>Define T as (S2-Y) - P1 - R1. Show it has all required properties.\<close>
    define T0 where "T0 = (top1_S2 - ?Y) - P1 - R1"
    have hT0_in: "T0 \<in> {U, V, W}"
    proof -
      have hUVW_union: "top1_S2 - ?Y = U \<union> V \<union> W" using hUVW(7) by (by100 blast)
      have hT0_alt: "T0 = (U \<union> V \<union> W) - P1 - R1" unfolding T0_def using hUVW_union by (by100 blast)
      \<comment> \<open>Case split: P1=U,V,W and R1=U,V,W; the remainder is T0.\<close>
      from hP1_is_comp show ?thesis
      proof (elim disjE)
        assume "P1 = U" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U" thus ?thesis using \<open>P1 = U\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = V"
          have "T0 = W" using hT0_alt \<open>P1 = U\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W"
          have "T0 = V" using hT0_alt \<open>P1 = U\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = V" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = W" using hT0_alt \<open>P1 = V\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V" thus ?thesis using \<open>P1 = V\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = W"
          have "T0 = U" using hT0_alt \<open>P1 = V\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = W" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = V" using hT0_alt \<open>P1 = W\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V"
          have "T0 = U" using hT0_alt \<open>P1 = W\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W" thus ?thesis using \<open>P1 = W\<close> hP1_ne_R1 by (by100 blast)
        qed
      qed
    qed
    have hT0_ne_P1: "T0 \<noteq> P1"
    proof -
      have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hP(1) by (by100 blast)
    qed
    have hT0_ne_R1: "T0 \<noteq> R1"
    proof -
      have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hR(1) by (by100 blast)
    qed
    have "top1_connected_on T0 (subspace_topology top1_S2 top1_S2_topology T0)"
      using hT0_in hUVW(8,9,10) by (by100 blast)
    moreover have "T0 \<noteq> {}" using hT0_in hUVW(1,2,3) by (by100 blast)
    moreover have "P1 \<union> R1 \<union> T0 = top1_S2 - ?Y"
    proof -
      have hT0e: "T0 = (top1_S2 - ?Y) - P1 - R1" by (rule T0_def)
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> P1 \<union> R1 \<union> T0"
        hence "x \<in> P1 \<or> x \<in> R1 \<or> x \<in> T0" by (by100 blast)
        thus "x \<in> top1_S2 - ?Y"
        proof (elim disjE)
          assume "x \<in> P1" thus ?thesis using hP1_sub_Y_compl by (by100 blast)
        next assume "x \<in> R1" thus ?thesis using hR1_sub_Y_compl by (by100 blast)
        next assume "x \<in> T0" thus ?thesis using hT0e by (by100 blast)
        qed
      next
        fix x assume "x \<in> top1_S2 - ?Y"
        thus "x \<in> P1 \<union> R1 \<union> T0" using hT0e by (by100 blast)
      qed
    qed
    moreover have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
    moreover have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
    ultimately show ?thesis by (rule that[OF hT0_in hT0_ne_P1 hT0_ne_R1])
  qed
  have hP1R1_disj: "P1 \<inter> R1 = {}"
  proof -
    from hP1_is_comp show ?thesis
    proof (elim disjE)
      assume "P1 = U" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using hP1_ne_R1 \<open>P1 = U\<close> by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = U\<close> hUVW(4) by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = U\<close> hUVW(6) by (by100 blast)
      qed
    next
      assume "P1 = V" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = V\<close> hUVW(4) by (by100 blast)
      next assume "R1 = V" thus ?thesis using hP1_ne_R1 \<open>P1 = V\<close> by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = V\<close> hUVW(5) by (by100 blast)
      qed
    next
      assume "P1 = W" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = W\<close> hUVW(6) by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = W\<close> hUVW(5) by (by100 blast)
      next assume "R1 = W" thus ?thesis using hP1_ne_R1 \<open>P1 = W\<close> by (by100 blast)
      qed
    qed
  qed
  have he24_in_T: "e24 - {a2, a4} \<subseteq> T"
  proof -
    \<comment> \<open>e24-{a2,a4} connected \<subseteq> P1\<union>R1\<union>T (disjoint open). By Lemma\_23\_2 approach: in one.\<close>
    have "e24 - {a2, a4} \<subseteq> P1 \<union> R1 \<union> T" using he24_in_Y_compl hT_union by (by100 blast)
    \<comment> \<open>Not \<subseteq> P1 (he24\_not\_P1). Not \<subseteq> R1 (he24\_not\_R1). Hence \<subseteq> T.\<close>
    \<comment> \<open>P1, R1, T are pairwise disjoint open. Connected e24-{a2,a4} must be in one.\<close>
    have hT_open: "T \<in> top1_S2_topology" using hT_is(1) hUVW(11,12,13) by (by100 blast)
    \<comment> \<open>e24-{a2,a4} \<subseteq> P1 or \<subseteq> R1\<union>T (separation {P1, R1\<union>T}).\<close>
    \<comment> \<open>Form separation {P1, R1\<union>T} of S2-Y = P1\<union>R1\<union>T.\<close>
    have hRT_open: "R1 \<union> T \<in> top1_S2_topology"
    proof -
      from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
        unfolding is_topology_on_def by (by100 blast)
      from this[of "{R1, T}"] hR1_open hT_open have "\<Union>{R1, T} \<in> top1_S2_topology" by (by100 blast)
      moreover have "\<Union>{R1, T} = R1 \<union> T" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hTY_loc: "is_topology_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hP1_oY: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "P1 = (top1_S2 - ?Y) \<inter> P1" using hP1_sub_Y_compl by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP1_open by (by100 blast)
    qed
    have hRT_oY: "R1 \<union> T \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "R1 \<union> T \<subseteq> top1_S2 - ?Y" using hT_union by (by100 blast)
      hence "R1 \<union> T = (top1_S2 - ?Y) \<inter> (R1 \<union> T)" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hRT_open by (by100 blast)
    qed
    have hPRT_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1 (R1 \<union> T)"
    proof -
      have "P1 \<inter> (R1 \<union> T) = {}"
      proof -
        \<comment> \<open>P1 \<inter> T = {} (hT\_disj). P1 \<inter> R1 = {} needs case split.
           But P1, R1, T are pairwise disjoint (they're 3 distinct elements of {U,V,W}).\<close>
        have "P1 \<inter> R1 = {}" by (rule hP1R1_disj)
        thus ?thesis using hT_disj(1) by (by100 blast)
      qed
      moreover have "P1 \<union> (R1 \<union> T) = top1_S2 - ?Y" using hT_union by (by100 blast)
      moreover have "R1 \<union> T \<noteq> {}" using hR(1) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hP1_oY hRT_oY hP(1) by (by100 blast)
    qed
    have he24_conn_Y: "top1_connected_on (e24 - {a2, a4})
        (subspace_topology (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) (e24 - {a2, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}) =
          subspace_topology (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) (e24 - {a2, a4})"
        using subspace_topology_trans[of "e24 - {a2, a4}" "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            he24_in_Y_compl by (by100 simp)
      thus ?thesis using he24_conn by (by100 simp)
    qed
    have "e24 - {a2, a4} \<subseteq> P1 \<or> e24 - {a2, a4} \<subseteq> R1 \<union> T"
      using Lemma_23_2[OF hTY_loc hPRT_sep he24_in_Y_compl he24_conn_Y] by (by100 blast)
    hence "e24 - {a2, a4} \<subseteq> R1 \<union> T" using he24_not_P1 by (by100 blast)
    \<comment> \<open>Then separation {R1, T} of R1\<union>T.\<close>
    moreover have "e24 - {a2, a4} \<subseteq> R1 \<or> e24 - {a2, a4} \<subseteq> T"
    proof -
      have hTRT: "is_topology_on (R1 \<union> T)
          (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hT_union in \<open>by100 blast\<close>)
      have hR_oRT: "R1 \<in> subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)"
      proof -
        have "R1 = (R1 \<union> T) \<inter> R1" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hR1_open by (by100 blast)
      qed
      have hT_oRT: "T \<in> subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)"
      proof -
        have "T = (R1 \<union> T) \<inter> T" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hT_open by (by100 blast)
      qed
      have hRT_sep: "top1_is_separation_on (R1 \<union> T)
          (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) R1 T"
        unfolding top1_is_separation_on_def
        using hR_oRT hT_oRT hR(1) hT_ne hT_disj(2) by (by100 blast)
      have he24_sub_RT: "e24 - {a2, a4} \<subseteq> R1 \<union> T"
        using \<open>e24 - {a2, a4} \<subseteq> R1 \<union> T\<close> .
      have he24_conn_RT: "top1_connected_on (e24 - {a2, a4})
          (subspace_topology (R1 \<union> T)
              (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) (e24 - {a2, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}) =
            subspace_topology (R1 \<union> T)
                (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) (e24 - {a2, a4})"
          using subspace_topology_trans[of "e24 - {a2, a4}" "R1 \<union> T" top1_S2 top1_S2_topology]
              he24_sub_RT by (by100 simp)
        thus ?thesis using he24_conn by (by100 simp)
      qed
      from Lemma_23_2[OF hTRT hRT_sep he24_sub_RT he24_conn_RT]
      show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis using he24_not_R1 by (by100 blast)
  qed
  \<comment> \<open>Step 5: Apply Theorem_63_5 to split T using cl(P1)\<union>cl(R1) and e24.\<close>
  let ?C1 = "closure_on top1_S2 top1_S2_topology P1
        \<union> closure_on top1_S2 top1_S2_topology R1"
  have hC1_eq: "?C1 = P1 \<union> R1 \<union> ?Y"
    using hcl_P1 hcl_R1 by (by100 blast)
  have hC1_closed: "closedin_on top1_S2 top1_S2_topology ?C1"
  proof -
    have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    moreover have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1)"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    ultimately show ?thesis by (rule closedin_on_Un[OF hTopS2])
  qed
  have hC1_conn: "top1_connected_on ?C1 (subspace_topology top1_S2 top1_S2_topology ?C1)"
  proof -
    \<comment> \<open>cl(P1) connected (closure of connected set, Theorem 23.4).\<close>
    have hclP1_sub: "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2"
      using hcl_P1 hP1_sub_AB hA_sub assms(8) by (by100 blast)
    have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
    have hclP1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology P1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1))"
      by (rule Theorem_23_4[OF hTopS2 hP1_sub_S2 hclP1_sub subset_closure_on
          closure_on_mono[OF order_refl] hP(5)])
    \<comment> \<open>cl(R1) connected.\<close>
    have hclR1_sub: "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2"
      using hcl_R1 hR(4) assms(8) hC_sub by (by100 blast)
    have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
    have hclR1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1))"
      by (rule Theorem_23_4[OF hTopS2 hR1_sub_S2 hclR1_sub subset_closure_on
          closure_on_mono[OF order_refl] hR(5)])
    \<comment> \<open>They share B = e13. B \<subseteq> cl(P1) \<inter> cl(R1).\<close>
    have hB_in_both: "?B \<subseteq> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1"
      using hcl_P1 hcl_R1 by (by100 blast)
    obtain p where hp: "p \<in> ?B" using assms(20) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1" using hB_in_both by (by100 blast)
    \<comment> \<open>Apply Theorem 23.3: indexed family with common point.\<close>
    have "top1_connected_on (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1))"
    proof -
      let ?I = "{True, False}" and ?A = "\<lambda>b. if b then closure_on top1_S2 top1_S2_topology P1
          else closure_on top1_S2 top1_S2_topology R1"
      have "?I \<noteq> {}" by (by100 simp)
      moreover have "\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2"
        using hclP1_sub hclR1_sub by (by100 simp)
      moreover have "\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))"
        using hclP1_conn hclR1_conn by (by100 simp)
      moreover have "p \<in> \<Inter>(?A ` ?I)"
        using \<open>p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
            closure_on top1_S2 top1_S2_topology R1\<close> by (by100 simp)
      moreover have "(\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 force)
      ultimately have hpremises: "?I \<noteq> {} \<and> (\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2) \<and>
          (\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))) \<and>
          p \<in> \<Inter>(?A ` ?I) \<and> (\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 blast)
      from Theorem_23_3[OF hTopS2, of ?I ?A p] hpremises
      show ?thesis by metis
    qed
    thus ?thesis .
  qed
  have hC1_compl: "top1_S2 - ?C1 = T"
  proof -
    have "top1_S2 - ?C1 = top1_S2 - (P1 \<union> R1 \<union> ?Y)" using hC1_eq by (by100 simp)
    also have "\<dots> = (top1_S2 - ?Y) - P1 - R1" by (by100 blast)
    also have "\<dots> = (P1 \<union> R1 \<union> T) - P1 - R1" using hT_union by (by100 simp)
    also have "\<dots> = T" using hT_disj(1,2) by (by100 blast)
    finally show ?thesis .
  qed
  have hC1_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C1"
    unfolding top1_separates_on_def using hC1_compl hT_conn by (by100 simp)
  have he24_closed: "closedin_on top1_S2 top1_S2_topology e24"
    by (rule arc_in_S2_closed[OF assms(9) assms(15)])
  have he24_conn_full: "top1_connected_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using arc_connected[OF assms(15)] .
  have he24_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology e24"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(9) assms(15)])
  have hC1_e24_int: "?C1 \<inter> e24 = {a2, a4}"
  proof -
    \<comment> \<open>(P1 \<union> R1 \<union> Y) \<inter> e24 = (P1 \<inter> e24) \<union> (R1 \<inter> e24) \<union> (Y \<inter> e24).
       P1 \<inter> e24 = {} and R1 \<inter> e24 = {} (both \<subseteq> S2-Y, e24\<setminus>{a2,a4} \<subseteq> T).\<close>
    have "P1 \<inter> e24 = {}"
    proof -
      have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "R1 \<inter> e24 = {}"
    proof -
      have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately have h_e24_fact: "(P1 \<union> R1) \<inter> e24 = {}" by (by100 blast)
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> ?C1 \<inter> e24"
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" using hC1_eq by (by100 blast)
      hence "x \<in> ?Y \<inter> e24" using h_e24_fact by (by100 blast)
      hence "x \<in> e24 \<inter> ?Y" by (by100 blast)
      thus "x \<in> {a2, a4}"
      proof -
        from he24_Y_int have "\<And>z. z \<in> e24 \<inter> ?Y \<Longrightarrow> z \<in> {a2, a4}" by (by100 blast)
        thus ?thesis using \<open>x \<in> e24 \<inter> ?Y\<close> by (by100 blast)
      qed
    next
      fix x assume "x \<in> {a2, a4}"
      hence "x \<in> ?Y \<inter> e24" using he24_Y_int by (by100 blast)
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" by (by100 blast)
      thus "x \<in> ?C1 \<inter> e24" using hC1_eq by (by100 blast)
    qed
  qed
  have hC1_e24_card: "card (?C1 \<inter> e24) = 2"
    using hC1_e24_int hdist(5) by (by100 simp)
  obtain W1 W2 where hW: "W1 \<noteq> {}" "W2 \<noteq> {}" "W1 \<inter> W2 = {}"
      "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)"
      "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      "top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hC1_closed he24_closed
        hC1_conn he24_conn_full hC1_e24_card hC1_no_sep he24_no_sep]
    by (by100 metis)
  \<comment> \<open>Step 6: Package the 4 components P1, R1, W1, W2.\<close>
  have hfour_union: "P1 \<union> R1 \<union> W1 \<union> W2 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
  proof -
    have "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)" by (rule hW(4))
    hence "W1 \<union> W2 = top1_S2 - ((P1 \<union> R1 \<union> ?Y) \<union> e24)" using hC1_eq by (by100 simp)
    hence "P1 \<union> R1 \<union> W1 \<union> W2 = P1 \<union> R1 \<union> (top1_S2 - (P1 \<union> R1 \<union> ?Y \<union> e24))" by (by100 blast)
    also have "\<dots> = top1_S2 - (?Y \<union> e24)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      moreover have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      moreover have "P1 \<inter> ?Y = {}" using hP1_sub_Y_compl by (by100 blast)
      moreover have "R1 \<inter> ?Y = {}" using hR1_sub_Y_compl by (by100 blast)
      moreover have "P1 \<inter> e24 = {}"
      proof -
        have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "R1 \<inter> e24 = {}"
      proof -
        have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    also have "\<dots> = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)" by blast
    finally show ?thesis .
  qed
  have hfour_disj: "P1 \<inter> R1 = {}" "P1 \<inter> W1 = {}" "P1 \<inter> W2 = {}"
      "R1 \<inter> W1 = {}" "R1 \<inter> W2 = {}" "W1 \<inter> W2 = {}"
  proof -
    show "P1 \<inter> R1 = {}" by (rule hP1R1_disj)
    \<comment> \<open>W1, W2 \<subseteq> S2-(C1\<union>e24) = T-e24_inner, which is disjoint from P1, R1.\<close>
    have hW12_sub: "W1 \<union> W2 \<subseteq> top1_S2 - ?C1" using hW(4) by (by100 blast)
    hence "W1 \<subseteq> top1_S2 - ?C1" by (by100 blast)
    hence "P1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    thus "P1 \<inter> W1 = {}" .
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "P1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    have "W1 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    show "W1 \<inter> W2 = {}" by (rule hW(3))
  qed
  have hbd_P1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology P1)"
  proof -
    have "a4 \<in> P2" using hCm_in_P2 hdist(3,6) arc_endpoints_subset[of e41] assms(19) by (by100 blast)
    have "a4 \<notin> P1" using \<open>a4 \<in> P2\<close> hP(3) by (by100 blast)
    hence "a4 \<notin> P1 \<union> (?A \<union> ?B)" using ha4_not_AB by (by100 blast)
    hence "a4 \<notin> closure_on top1_S2 top1_S2_topology P1" using hcl_P1 by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
  have hbd_R1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology R1)"
  proof -
    have "a2 \<in> R2" using hAm_in_R2 hdist(1,4) arc_endpoints_subset[of e12] assms(16) by (by100 blast)
    have "a2 \<notin> R1" using \<open>a2 \<in> R2\<close> hR(3) by (by100 blast)
    hence "a2 \<notin> R1 \<union> (?B \<union> ?C)" using ha2_not_BC by (by100 blast)
    hence "a2 \<notin> closure_on top1_S2 top1_S2_topology R1" using hcl_R1 by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
  have hbd_W1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology W1)"
    sorry
  have hbd_W2: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology W2)"
    sorry
  show ?thesis
    apply (rule exI[of _ P1])
    apply (rule exI[of _ R1])
    apply (rule exI[of _ W1])
    apply (rule exI[of _ W2])
    apply (intro conjI)
    apply (fact hP(1)) apply (fact hR(1)) apply (fact hW(1)) apply (fact hW(2))
    apply (fact hfour_disj(1)) apply (fact hfour_disj(2)) apply (fact hfour_disj(3))
    apply (fact hfour_disj(4)) apply (fact hfour_disj(5)) apply (fact hfour_disj(6))
    apply (fact hfour_union)
    apply (fact hP(5)) apply (fact hR(5)) apply (fact hW(5)) apply (fact hW(6))
    apply (fact hbd_P1) apply (fact hbd_R1) apply (fact hbd_W1) apply (fact hbd_W2)
    done
qed

text \<open>Theorem 64.4 (K5 non-planarity). Assumptions ordered so K4-compatible ones come first.\<close>
theorem Theorem_64_4_K5_not_planar:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcard5: "card {a1, a2, a3, a4, a5 :: real \<times> real \<times> real} = 5"
      and hvert: "{a1, a2, a3, a4, a5} \<subseteq> top1_S2"
      \<comment> \<open>K4-compatible subset of assumptions (matching K5\_K4\_sep exactly):\<close>
      and hsub12: "e12 \<subseteq> top1_S2" and hsub23: "e23 \<subseteq> top1_S2" and hsub34: "e34 \<subseteq> top1_S2"
      and hsub14: "e14 \<subseteq> top1_S2" and hsub13: "e13 \<subseteq> top1_S2" and hsub24: "e24 \<subseteq> top1_S2"
      and harc12: "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and harc23: "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and harc34: "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and harc14: "top1_is_arc_on e14 (subspace_topology top1_S2 top1_S2_topology e14)"
      and harc13: "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and harc24: "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and hep12: "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and hep23: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and hep34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and hep14: "top1_arc_endpoints_on e14 (subspace_topology top1_S2 top1_S2_topology e14) = {a4,a1}"
      and hep13: "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and hep24: "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and hi_12_34: "e12 \<inter> e34 = {}" and hi_23_14: "e23 \<inter> e14 = {}"
      and hi_12_23: "e12 \<inter> e23 = {a2}" and hi_23_34: "e23 \<inter> e34 = {a3}"
      and hi_34_14: "e34 \<inter> e14 = {a4}" and hi_14_12: "e14 \<inter> e12 = {a1}"
      and hi_13_12: "e13 \<inter> e12 = {a1}" and hi_13_23: "e13 \<inter> e23 = {a3}"
      and hi_13_34: "e13 \<inter> e34 = {a3}" and hi_13_14: "e13 \<inter> e14 = {a1}"
      and hi_13_24: "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and hi_24_12: "e24 \<inter> e12 = {a2}" and hi_24_23: "e24 \<inter> e23 = {a2}"
      and hi_24_34: "e24 \<inter> e34 = {a4}" and hi_24_14: "e24 \<inter> e14 = {a4}"
      \<comment> \<open>Remaining K5-specific assumptions:\<close>
      and harc15: "top1_is_arc_on e15 (subspace_topology top1_S2 top1_S2_topology e15)"
      and harc25: "top1_is_arc_on e25 (subspace_topology top1_S2 top1_S2_topology e25)"
      and harc35: "top1_is_arc_on e35 (subspace_topology top1_S2 top1_S2_topology e35)"
      and harc45: "top1_is_arc_on e45 (subspace_topology top1_S2 top1_S2_topology e45)"
      and hsub15: "e15 \<subseteq> top1_S2" and hsub25: "e25 \<subseteq> top1_S2"
      and hsub35: "e35 \<subseteq> top1_S2" and hsub45: "e45 \<subseteq> top1_S2"
      and hep15: "top1_arc_endpoints_on e15 (subspace_topology top1_S2 top1_S2_topology e15) = {a1,a5}"
      and hep25: "top1_arc_endpoints_on e25 (subspace_topology top1_S2 top1_S2_topology e25) = {a2,a5}"
      and hep35: "top1_arc_endpoints_on e35 (subspace_topology top1_S2 top1_S2_topology e35) = {a3,a5}"
      and hep45: "top1_arc_endpoints_on e45 (subspace_topology top1_S2 top1_S2_topology e45) = {a4,a5}"
      \<comment> \<open>Intersections involving a5-edges:\<close>
      and hi_12_15: "e12 \<inter> e15 = {a1}" and hi_13_15: "e13 \<inter> e15 = {a1}"
      and hi_14_15: "e14 \<inter> e15 = {a1}" and hi_15_23: "e15 \<inter> e23 = {}"
      and hi_15_24: "e15 \<inter> e24 = {}" and hi_15_34: "e15 \<inter> e34 = {}"
      and hi_12_25: "e12 \<inter> e25 = {a2}" and hi_13_25: "e13 \<inter> e25 = {}"
      and hi_14_25: "e14 \<inter> e25 = {}" and hi_23_25: "e23 \<inter> e25 = {a2}"
      and hi_24_25: "e24 \<inter> e25 = {a2}" and hi_25_34: "e25 \<inter> e34 = {}"
      and hi_12_35: "e12 \<inter> e35 = {}" and hi_13_35: "e13 \<inter> e35 = {a3}"
      and hi_14_35: "e14 \<inter> e35 = {}" and hi_23_35: "e23 \<inter> e35 = {a3}"
      and hi_24_35: "e24 \<inter> e35 = {}" and hi_34_35: "e34 \<inter> e35 = {a3}"
      and hi_12_45: "e12 \<inter> e45 = {}" and hi_13_45: "e13 \<inter> e45 = {}"
      and hi_14_45: "e14 \<inter> e45 = {a4}" and hi_23_45: "e23 \<inter> e45 = {}"
      and hi_24_45: "e24 \<inter> e45 = {a4}" and hi_34_45: "e34 \<inter> e45 = {a4}"
      and hi_15_25: "e15 \<inter> e25 = {a5}" and hi_15_35: "e15 \<inter> e35 = {a5}"
      and hi_15_45: "e15 \<inter> e45 = {a5}" and hi_25_35: "e25 \<inter> e35 = {a5}"
      and hi_25_45: "e25 \<inter> e45 = {a5}" and hi_35_45: "e35 \<inter> e45 = {a5}"
  shows False
proof -
  have hcard4: "card {a1, a2, a3, a4} = 4"
    using hcard5 by (auto simp: card_insert_if split: if_splits)
  have hvert4: "{a1, a2, a3, a4} \<subseteq> top1_S2" using hvert by blast
  have ha5_ne: "a5 \<noteq> a1" "a5 \<noteq> a2" "a5 \<noteq> a3" "a5 \<noteq> a4"
    using hcard5 by (auto simp: card_insert_if split: if_splits)+
  \<comment> \<open>a5 \<in> e15 (from endpoints).\<close>
  have ha5_e15: "a5 \<in> e15"
    using arc_endpoints_subset[of e15 "subspace_topology top1_S2 top1_S2_topology e15"] hep15
    by blast
  \<comment> \<open>K4 graph X. a5 \<notin> X.\<close>
  define X where "X = e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24"
  have ha5_not_in_X: "a5 \<notin> X"
    unfolding X_def using ha5_e15 ha5_ne
      hi_12_15 hi_13_15 hi_14_15 hi_15_23 hi_15_24 hi_15_34
    by blast
  \<comment> \<open>Apply strengthened K4 separation (with boundary info).\<close>
  have hK4_sep: "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - X
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)
      \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
    unfolding X_def
    apply (rule K4_four_components_with_boundary)
    apply (fact hS2) apply (fact hcard4) apply (fact hvert4)
    apply (fact hsub12) apply (fact hsub23) apply (fact hsub34)
    apply (fact hsub14) apply (fact hsub13) apply (fact hsub24)
    apply (fact harc12) apply (fact harc23) apply (fact harc34)
    apply (fact harc14) apply (fact harc13) apply (fact harc24)
    apply (fact hep12) apply (fact hep23) apply (fact hep34)
    apply (fact hep14) apply (fact hep13) apply (fact hep24)
    apply (fact hi_12_34) apply (fact hi_23_14)
    apply (fact hi_12_23) apply (fact hi_23_34) apply (fact hi_34_14) apply (fact hi_14_12)
    apply (fact hi_13_12) apply (fact hi_13_23) apply (fact hi_13_34) apply (fact hi_13_14)
    apply (fact hi_13_24)
    apply (fact hi_24_12) apply (fact hi_24_23) apply (fact hi_24_34) apply (fact hi_24_14)
    done
  from hK4_sep obtain U1 U2 U3 U4 where hU:
      "U1 \<noteq> {}" "U2 \<noteq> {}" "U3 \<noteq> {}" "U4 \<noteq> {}"
      "U1 \<inter> U2 = {}" "U1 \<inter> U3 = {}" "U1 \<inter> U4 = {}"
      "U2 \<inter> U3 = {}" "U2 \<inter> U4 = {}" "U3 \<inter> U4 = {}"
      "U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - X"
      "top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)"
      "top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)"
      "top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)"
      "top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
      "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)"
      "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)"
      "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)"
      "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
    apply (elim exE conjE)
    apply (intro that; assumption)
    done
  have ha5_in_comp: "a5 \<in> U1 \<union> U2 \<union> U3 \<union> U4"
    using ha5_not_in_X hvert hU(11) X_def by (by100 blast)
  have hU_boundary: "\<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
    using hU(16,17,18,19) by (by100 blast)
  \<comment> \<open>Each X\_i = 3 edges not incident to a\_i forms an SCC.
     By JCT, X\_i separates S2. Since e\_{i,5} \<inter> X\_i = {} and e\_{i,5} connects
     a5 to a\_i, they are on the same side of X\_i.
     But a5 being in one K4 component means a5 is on one specific side of each X\_i,
     and being on a\_i's side for ALL i is impossible (the 4 faces are disjoint).\<close>
  \<comment> \<open>X1 = e23 \<union> e24 \<union> e34 (SCC, missing a1).
     X2 = e13 \<union> e14 \<union> e34 (SCC, missing a2).
     X3 = e12 \<union> e14 \<union> e24 (SCC, missing a3).
     X4 = e12 \<union> e13 \<union> e23 (SCC, missing a4).\<close>
  \<comment> \<open>e15 \<inter> X1 = e15 \<inter> (e23\<union>e24\<union>e34) = {}\<union>{}\<union>{} = {} (from intersection assumptions).
     Similarly for e25 \<inter> X2, e35 \<inter> X3, e45 \<inter> X4.\<close>
  have he15_X1: "e15 \<inter> (e23 \<union> e24 \<union> e34) = {}"
    using hi_15_23 hi_15_24 hi_15_34 by (by100 blast)
  have he25_X2: "e25 \<inter> (e13 \<union> e14 \<union> e34) = {}"
    using hi_13_25 hi_14_25 hi_25_34 by (by100 blast)
  have he35_X3: "e35 \<inter> (e12 \<union> e14 \<union> e24) = {}"
    using hi_12_35 hi_14_35 hi_24_35 by (by100 blast)
  have he45_X4: "e45 \<inter> (e12 \<union> e13 \<union> e23) = {}"
    using hi_12_45 hi_13_45 hi_23_45 by (by100 blast)
  \<comment> \<open>Step A+B: for each component Ui containing a5, all 4 vertices are in closure(Ui).
     Generic argument for each vertex aj:
     - e\_{j,5} \<inter> X = {a\_j} (proved above)
     - e\_{j,5} - {a\_j} \<subseteq> S2-X
     - e\_{j,5} - {a\_j} is connected (arc minus one endpoint)
     - a5 \<in> e\_{j,5} - {a\_j} (a5 is endpoint, a5 \<noteq> a\_j)
     - a5 \<in> Ui, Ui is component of S2-X
     - connected subset of S2-X meeting Ui \<Rightarrow> \<subseteq> Ui
     - a\_j \<in> closure(e\_{j,5} - {a\_j, a5}) \<subseteq> closure(Ui)\<close>
  \<comment> \<open>Generic: if a5 \<in> Ui and Ui is one of the 4 components, all vertices in closure(Ui).\<close>
  have hall_generic: "\<And>Ui. Ui \<in> {U1,U2,U3,U4} \<Longrightarrow> a5 \<in> Ui \<Longrightarrow>
      {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology Ui"
    sorry
  have hall1: "a5 \<in> U1 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1"
    by (rule hall_generic) (by100 blast)
  have hall2: "a5 \<in> U2 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2"
    by (rule hall_generic) (by100 blast)
  have hall3: "a5 \<in> U3 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3"
    by (rule hall_generic) (by100 blast)
  have hall4: "a5 \<in> U4 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4"
    by (rule hall_generic) (by100 blast)
  \<comment> \<open>But hU\_boundary says no component has all 4 vertices in its closure.\<close>
  show False using ha5_in_comp hall1 hall2 hall3 hall4 hU_boundary by (by100 blast)
qed

end
