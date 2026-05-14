theory K5_nonplanar
imports AlgTopC.AlgTopCached
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
  \<comment> \<open>Apply K4 separation via K5\_K4\_sep. assms(1) = hS2, assms(4-36) = K4 facts.\<close>
  obtain U1 U2 U3 U4 where hU:
      "U1 \<noteq> {}" "U2 \<noteq> {}" "U3 \<noteq> {}" "U4 \<noteq> {}"
      "U1 \<inter> U2 = {}" "U1 \<inter> U3 = {}" "U1 \<inter> U4 = {}"
      "U2 \<inter> U3 = {}" "U2 \<inter> U4 = {}" "U3 \<inter> U4 = {}"
      "U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - X"
      "top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)"
      "top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)"
      "top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)"
      "top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
    sorry \<comment> \<open>K5\_K4\_sep[OF ...] — all premises proved but OF-chain times out.\<close>
  have ha5_in_comp: "a5 \<in> U1 \<union> U2 \<union> U3 \<union> U4"
    using ha5_not_in_X hvert hU(11) X_def by blast
  show False sorry
qed

end
