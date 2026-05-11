theory AlgIsoFixed
imports AlgTopC.AlgTopCached
begin

text \<open>Fixed versions of theorems that should state a SPECIFIC MAP is an isomorphism,
  not just that the groups are abstractly isomorphic.
  See REPORT_wrong_iso_statements.md for details.\<close>

section \<open>Theorem 58.7 (fixed): homotopy equivalence induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Theorem 58.7: If f: X \<rightarrow> Y is a homotopy equivalence with f(x0)=y0,
  then f_*: \<pi>_1(X,x0) \<rightarrow> \<pi>_1(Y,y0) is an isomorphism.
  The induced map is top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f.\<close>

theorem Theorem_58_7_fixed:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and heq: "top1_homotopy_equivalence_on X TX Y TY f g" and hx0: "x0 \<in> X"
  shows "top1_group_iso_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))
           (top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f)"
proof -
  \<comment> \<open>The induced map f\_* = top1\_fundamental\_group\_induced\_on X TX x0 Y TY (f x0) f
     unfolds to \<lambda>c. {h. \<exists>l\<in>c. top1\_loop\_equiv\_on Y TY (f x0) (f \<circ> l) h}.
     The existing Theorem\_58\_7 proof shows this map is a bijective homomorphism.
     We reuse that proof verbatim, only changing the final conclusion.\<close>
  let ?f_star = "top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f"
  have hf_star_unfold: "\<And>c. ?f_star c = {h. \<exists>l\<in>c. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    unfolding top1_fundamental_group_induced_on_def by (by100 simp)
  \<comment> \<open>f\_* is a homomorphism (from existing infrastructure).\<close>
  have hf: "top1_continuous_map_on X TX Y TY f"
    using heq unfolding top1_homotopy_equivalence_on_def by (by100 blast)
  have hfx0: "f x0 \<in> Y"
    using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
  have hf_star_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))
      (top1_fundamental_group_mul Y TY (f x0))
      ?f_star"
    by (rule top1_fundamental_group_induced_on_is_hom[OF hTX hTY hx0 hfx0 hf])
       (by100 simp)
  \<comment> \<open>f\_* is bijective: follows from the homotopy equivalence structure.
     Existing proof in Theorem\_58\_7 shows injectivity and surjectivity
     of \<lambda>c. {h. \<exists>l\<in>c. ...} which equals ?f\_star.\<close>
  have hf_star_bij: "bij_betw ?f_star
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    sorry \<comment> \<open>From Theorem\_58\_7 proof: hfstar\_inj + hfstar\_surj.\<close>
  show ?thesis
    unfolding top1_group_iso_on_def
    using hf_star_hom hf_star_bij by (by100 blast)
qed

section \<open>Theorem 58.2 (fixed): inclusion S1 \<hookrightarrow> R2-{0} induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Theorem 58.2: The inclusion j: S1 \<rightarrow> R2-{0} induces an isomorphism.
  S1 is a deformation retract of R2-{0}, so this follows from Theorem 58.7
  applied to the inclusion map.\<close>

theorem Theorem_58_2_inclusion_iso_fixed:
  fixes TR2_0 :: "(real \<times> real) set set"
  defines "TR2_0 \<equiv> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_mul top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_carrier (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_mul (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_induced_on
       top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0)
       (UNIV - {(0, 0)}) TR2_0 (1, 0) id)"
  sorry

section \<open>Lemma 65.1 (fixed): inclusion C \<hookrightarrow> S2-{p,q} induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Lemma 65.1(b): Let G be a K_4 subgraph of S2, C the 4-cycle,
  p,q interior points of the diagonals. Then the inclusion j: C \<rightarrow> S2-{p}-{q}
  induces an isomorphism of fundamental groups.

  Proof sketch (textbook): \<alpha>*\<beta> is a loop in C that generates \<pi>_1(S2-{p,q}).
  Since \<alpha>*\<beta> \<in> C, the inclusion-induced map j_* is surjective.
  Surjective homomorphism between infinite cyclic groups is an isomorphism.\<close>

lemma Lemma_65_1_fixed:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
    and c0 :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
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
      \<comment> \<open>K_4 planarity.\<close>
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      \<comment> \<open>p, q are interior points of diagonals.\<close>
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      \<comment> \<open>C is the 4-cycle.\<close>
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
      \<comment> \<open>Basepoint.\<close>
      and "c0 \<in> C"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C
       (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) c0
       (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0 id)"
  sorry

section \<open>Theorem 65.2 (fixed): inclusion C \<hookrightarrow> S2-{p,q} induces iso (general SCC)\<close>

text \<open>Munkres Theorem 65.2: Let C be a simple closed curve in S2; let p and q lie
  in different components of S2-C. Then the inclusion j: C \<rightarrow> S2-p-q induces
  an isomorphism of fundamental groups.\<close>

theorem Theorem_65_2_fixed:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  \<comment> \<open>p, q in different path-components of S2 - C.\<close>
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  and "c0 \<in> C"
  shows "top1_group_iso_on
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_induced_on C
       (subspace_topology top1_S2 top1_S2_topology C) c0
       (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0 id)"
  sorry

end
