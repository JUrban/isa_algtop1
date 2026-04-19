theory AlgTop
  imports "Top0.Top1_Ch5_8"
begin

ML \<open>
  fun method_evaluate text ctxt facts =
    NO_CONTEXT_TACTIC ctxt (Method.evaluate_runtime text ctxt facts)

  fun timed_seq name limit seq =
    Seq.make (fn () =>
      (case
         (Timeout.apply limit (fn () => Seq.pull seq) ()
           handle Timeout.TIMEOUT _ =>
             error (name ^ ": timeout after " ^
               string_of_int (Time.toMilliseconds limit) ^ " ms"))
       of
         NONE => NONE
       | SOME (st, seq') => SOME (st, timed_seq name limit seq')))
\<close>

method_setup by100 =
  \<open>
    Method.text_closure >> (fn text => fn ctxt => fn facts =>
      let
        val limit = Time.fromMilliseconds 100
        fun tac st = timed_seq "by100" limit (method_evaluate text ctxt facts st)
      in
        SIMPLE_METHOD tac facts
      end)
  \<close>
  "apply a proof method with 100ms timeout per result step"


text \<open>
  Formalization of algebraic topology from Munkres (algtop.tex), Chapters 9-14.

  Chapter 9: The Fundamental Group (§51-60)
  Chapter 10: Separation Theorems in the Plane (§61-66)
  Chapter 11: The Seifert-van Kampen Theorem (§67-73)
  Chapter 12: Classification of Surfaces (§74-78)
  Chapter 13: Classification of Covering Spaces (§79-82)
  Chapter 14: Applications to Group Theory (§83-85)

  Built on the general topology library (Top0 = Top1_Ch2 through Top1_Ch5_8).
  Uses top1_unit_interval, top1_is_path_on, top1_path_connected_on, etc.
\<close>

section \<open>\<S>51 Homotopy of Paths\<close>

text \<open>I = [0,1] is top1_unit_interval (defined in Top1_Ch3).
  We use I\<times>I with the product topology as the domain of path homotopies.\<close>

abbreviation (input) "I_top \<equiv> top1_unit_interval_topology"
abbreviation (input) "I_set \<equiv> top1_unit_interval"

text \<open>The product of euclidean open sets is the euclidean open sets on the product.\<close>
lemma product_topology_on_open_sets:
  "product_topology_on (top1_open_sets :: 'a::topological_space set set)
                       (top1_open_sets :: 'b::topological_space set set)
   = (top1_open_sets :: ('a \<times> 'b) set set)"
proof (rule set_eqI, rule iffI)
  fix W :: "('a \<times> 'b) set"
  assume hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
  have hTX: "is_topology_on (UNIV :: 'a set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTY: "is_topology_on (UNIV :: 'b set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hUU: "(UNIV :: 'a set) \<times> (UNIV :: 'b set) = (UNIV :: ('a \<times> 'b) set)" by simp
  have hTP: "is_topology_on (UNIV :: ('a \<times> 'b) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTX hTY] unfolding hUU .
  have "open W"
  proof (rule open_prod_intro)
    fix x assume hx: "x \<in> W"
    \<comment> \<open>W is in a product topology, so it contains a basis element around x.\<close>
    have "W \<subseteq> UNIV" by simp
    obtain U V where hU: "U \<in> top1_open_sets" and hV: "V \<in> top1_open_sets"
        and hxUV: "x \<in> U \<times> V" and hUVW: "U \<times> V \<subseteq> W"
    proof -
      have "W \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
        using hW unfolding product_topology_on_def .
      hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. x \<in> b \<and> b \<subseteq> W"
        using hx unfolding topology_generated_by_basis_def by blast
      then obtain b where hb: "b \<in> product_basis top1_open_sets top1_open_sets"
          and hxb: "x \<in> b" and hbW: "b \<subseteq> W" by blast
      obtain U' V' where hUV: "b = U' \<times> V'" and hU': "U' \<in> top1_open_sets" and hV': "V' \<in> top1_open_sets"
        using hb unfolding product_basis_def by blast
      show ?thesis using that[of U' V'] hU' hV' hxb hbW hUV by blast
    qed
    have "open U" using hU unfolding top1_open_sets_def by blast
    moreover have "open V" using hV unfolding top1_open_sets_def by blast
    ultimately show "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> W"
      using hxUV hUVW by blast
  qed
  thus "W \<in> top1_open_sets" unfolding top1_open_sets_def by blast
next
  fix W :: "('a \<times> 'b) set"
  assume hW: "W \<in> top1_open_sets"
  hence "open W" unfolding top1_open_sets_def by blast
  have hTX: "is_topology_on (UNIV :: 'a set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTY: "is_topology_on (UNIV :: 'b set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hUU: "(UNIV :: 'a set) \<times> (UNIV :: 'b set) = (UNIV :: ('a \<times> 'b) set)" by simp
  have hTP: "is_topology_on (UNIV :: ('a \<times> 'b) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTX hTY] unfolding hUU .
  \<comment> \<open>W = \<Union>{A \<times> B | A B. open A \<and> open B \<and> A \<times> B \<subseteq> W}.\<close>
  let ?cover = "{R. \<exists>A B. R = A \<times> B \<and> open A \<and> open B \<and> R \<subseteq> W}"
  have hW_eq: "W = \<Union>?cover"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> W"
    then obtain A B where "open A" "open B" "x \<in> A \<times> B" "A \<times> B \<subseteq> W"
      using \<open>open W\<close> open_prod_elim by blast
    thus "x \<in> \<Union>?cover" by blast
  next
    fix x assume "x \<in> \<Union>?cover" thus "x \<in> W" by auto
  qed
  \<comment> \<open>Each A \<times> B \<in> ?cover is in product_topology_on.\<close>
  have "\<forall>R\<in>?cover. R \<in> product_topology_on top1_open_sets top1_open_sets"
  proof
    fix R assume "R \<in> ?cover"
    then obtain A B where "R = A \<times> B" "open A" "open B" by blast
    hence "A \<in> top1_open_sets" "B \<in> top1_open_sets" unfolding top1_open_sets_def by blast+
    thus "R \<in> product_topology_on top1_open_sets top1_open_sets"
      using \<open>R = A \<times> B\<close> product_rect_open by blast
  qed
  \<comment> \<open>Union of topology members is in the topology.\<close>
  hence "\<Union>?cover \<in> product_topology_on top1_open_sets top1_open_sets"
    using hTP unfolding is_topology_on_def by blast
  thus "W \<in> product_topology_on top1_open_sets top1_open_sets"
    using hW_eq by simp
qed

lemmas product_topology_on_open_sets_real2 =
  product_topology_on_open_sets[where ?'a = real and ?'b = real]

text \<open>Continuity transfer: continuous_on UNIV for R \<rightarrow> subspace of R².\<close>
lemma top1_continuous_map_on_R_to_R2_subspace:
  fixes T :: "(real \<times> real) set"
  assumes hmap: "\<And>x::real. f x \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on (UNIV::real set) top1_open_sets T
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix x :: real show "f x \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by (by100 blast)
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by metis
    thus ?thesis unfolding top1_open_sets_def by blast
  qed
  have hfU_open: "open (f -` U)" by (rule open_vimage[OF hU_open hcont])
  have "{x. f x \<in> V} = f -` U"
  proof (rule set_eqI)
    fix x show "(x \<in> {x. f x \<in> V}) = (x \<in> f -` U)"
      using hVeq hmap[of x] by (by100 blast)
  qed
  hence "open {x. f x \<in> V}" using hfU_open by simp
  hence "{x. f x \<in> V} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
  thus "{x \<in> UNIV. f x \<in> V} \<in> top1_open_sets" by simp
qed

text \<open>Continuity transfer: continuous_on S on ℝ² implies top1_continuous_map_on
  on subspace topologies. Works for any S (not just UNIV).\<close>
lemma top1_continuous_map_on_real2_subspace_general:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
  assumes hmap: "\<And>p. p \<in> S \<Longrightarrow> f p \<in> T"
      and hcont: "continuous_on S f"
  shows "top1_continuous_map_on S
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
           T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "f p \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by (by100 auto)
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by (by100 metis)
    thus ?thesis unfolding top1_open_sets_def by (by100 simp)
  qed
  \<comment> \<open>continuous_on S f + open U gives open W with f\<inverse>(U) \<inter> S = W \<inter> S.\<close>
  obtain W where hW_open: "open W" and hfW: "W \<inter> S = f -` U \<inter> S"
    using hcont hU_open unfolding continuous_on_open_invariant by blast
  have "{p \<in> S. f p \<in> V} = S \<inter> W"
  proof -
    have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U \<inter> f -` T)" unfolding hVeq by (by100 auto)
    also have "\<dots> = S \<inter> (f -` U)" using hmap by (by100 auto)
    also have "\<dots> = W \<inter> S" using hfW by (by100 blast)
    also have "\<dots> = S \<inter> W" by (by100 blast)
    finally show ?thesis .
  qed
  moreover have "W \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hW_open unfolding top1_open_sets_def by (by100 blast)
    thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
  qed
  ultimately show "{p \<in> S. f p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def by (by100 blast)
qed

text \<open>Continuity transfer: continuous_on UNIV on ℝ² implies top1_continuous_map_on
  on subspace topologies (special case of the general version).\<close>
lemma top1_continuous_map_on_real2_subspace:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
  assumes hmap: "\<And>p. p \<in> S \<Longrightarrow> f p \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on S
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
           T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "f p \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by blast
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by metis
    thus ?thesis unfolding top1_open_sets_def by blast
  qed
  have hfU_open: "open (f -` U)" by (rule open_vimage[OF hU_open hcont])
  have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U \<inter> f -` T)"
    unfolding hVeq by auto
  also have "... = S \<inter> (f -` U)"
    using hmap by auto
  finally have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U)" .
  moreover have "f -` U \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "f -` U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hfU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  ultimately show "{p \<in> S. f p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def by blast
qed

text \<open>Transfer from continuous_on on I\<times>I to top1_continuous_map_on with II_topology.
  Uses openin + subspace topology equivalence.\<close>
lemma top1_continuous_map_on_II_to_I:
  assumes hmap: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> f p \<in> I_set"
      and hcont: "continuous_on (I_set \<times> I_set) f"
  shows "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top f"
proof -
  show ?thesis unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p assume "p \<in> I_set \<times> I_set" thus "f p \<in> I_set" by (rule hmap)
  next
    fix V assume hV: "V \<in> I_top"
    \<comment> \<open>V = I \<inter> W for some open W.\<close>
    obtain W where hW: "open W" and hVW: "V = I_set \<inter> W"
      using hV unfolding top1_unit_interval_topology_def subspace_topology_def
                        top1_open_sets_def by auto
    \<comment> \<open>By continuous_on_open_invariant, there exists open U with U \<inter> (I\<times>I) = f^{-1}(W) \<inter> (I\<times>I).\<close>
    obtain U where hU: "open U" and hfW: "U \<inter> (I_set \<times> I_set) = f -` W \<inter> (I_set \<times> I_set)"
      using hcont hW unfolding continuous_on_open_invariant by blast
    \<comment> \<open>U is open in R^2, so U \<in> product_topology_on top1_open_sets top1_open_sets.\<close>
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU unfolding top1_open_sets_def by blast
    hence "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
      using product_topology_on_open_sets_real2 by metis
    \<comment> \<open>(I\<times>I) \<inter> U \<in> II_topology (subspace of R^2 on I\<times>I).\<close>
    hence hU_II: "(I_set \<times> I_set) \<inter> U \<in> product_topology_on I_top I_top"
    proof -
      have "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using \<open>U \<in> top1_open_sets\<close> product_topology_on_open_sets_real2 by metis
      moreover have hIeq: "product_topology_on I_top I_top
        = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      proof -
        have hTR: "is_topology_on (UNIV :: real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
        have "product_topology_on (subspace_topology UNIV top1_open_sets I_set)
                (subspace_topology UNIV top1_open_sets I_set)
              = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
          by (rule Theorem_16_3[OF hTR hTR])
        moreover have "(UNIV :: real set) \<times> (UNIV :: real set) = (UNIV :: (real\<times>real) set)" by simp
        moreover have "I_top = subspace_topology UNIV top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by rule
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis unfolding hIeq subspace_topology_def by blast
    qed
    have "{p \<in> I_set \<times> I_set. f p \<in> V} = (I_set \<times> I_set) \<inter> U"
    proof -
      have "{p \<in> I_set \<times> I_set. f p \<in> V} = {p \<in> I_set \<times> I_set. f p \<in> I_set \<and> f p \<in> W}"
        unfolding hVW by auto
      also have "... = f -` W \<inter> (I_set \<times> I_set)" using hmap by auto
      also have "... = U \<inter> (I_set \<times> I_set)" using hfW by simp
      also have "... = (I_set \<times> I_set) \<inter> U" by (rule Int_commute)
      finally show ?thesis .
    qed
    thus "{p \<in> I_set \<times> I_set. f p \<in> V} \<in> product_topology_on I_top I_top" using hU_II by simp
  qed
qed

text \<open>II_topology equals the subspace of R^2 on I × I.\<close>
lemma II_topology_eq_subspace:
  "product_topology_on I_top I_top =
   subspace_topology (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
proof -
  have hTR: "is_topology_on (UNIV :: real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have "product_topology_on
          (subspace_topology UNIV top1_open_sets I_set)
          (subspace_topology UNIV top1_open_sets I_set)
        = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets)
            (I_set \<times> I_set)"
    by (rule Theorem_16_3[OF hTR hTR])
  moreover have "(UNIV :: real set) \<times> (UNIV :: real set) = (UNIV :: (real \<times> real) set)" by simp
  moreover have "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by rule
  ultimately show ?thesis by simp
qed

text \<open>The product space I \<times> I with the product topology.\<close>
definition II_topology :: "(real \<times> real) set set" where
  "II_topology = product_topology_on I_top I_top"

text \<open>Homotopy between continuous maps X \<rightarrow> Y: a continuous F: X \<times> I \<rightarrow> Y
  with F(x,0) = f(x) and F(x,1) = f'(x).\<close>
definition top1_homotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_homotopic_on X TX Y TY f f' \<longleftrightarrow>
     top1_continuous_map_on X TX Y TY f \<and>
     top1_continuous_map_on X TX Y TY f' \<and>
     (\<exists>F. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F
          \<and> (\<forall>x\<in>X. F (x, 0) = f x) \<and> (\<forall>x\<in>X. F (x, 1) = f' x))"

text \<open>Path homotopy: a stronger relation between paths with fixed endpoints.
  F: I \<times> I \<rightarrow> X continuous with F(s,0) = f(s), F(s,1) = f'(s),
  F(0,t) = x0, F(1,t) = x1.\<close>
definition top1_path_homotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_path_homotopic_on X TX x0 x1 f f' \<longleftrightarrow>
     top1_is_path_on X TX x0 x1 f \<and>
     top1_is_path_on X TX x0 x1 f' \<and>
     (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F
          \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = f' s)
          \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x1))"

text \<open>Nulhomotopic: homotopic to a constant map.\<close>
definition top1_nulhomotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_nulhomotopic_on X TX Y TY f \<longleftrightarrow>
     (\<exists>c\<in>Y. top1_homotopic_on X TX Y TY f (\<lambda>_. c))"

text \<open>Helper: f \<circ> pi_1 is continuous from X \<times> I \<rightarrow> Y when f: X \<rightarrow> Y is continuous.\<close>
lemma homotopy_const_continuous:
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  and hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. f (fst p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  have hid: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> id)"
    using iffD1[OF Theorem_18_4[OF hTP hTX hTI] hid] by blast
  have hpi1': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
    using hpi1 by (simp add: comp_def)
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1' hf])
  thus ?thesis by (simp add: comp_def pi1_def)
qed

(** from \<S>51 Lemma 51.1: \<simeq> and \<simeq>_p are equivalence relations **)
lemma Lemma_51_1_homotopic_refl:
  assumes hf: "top1_continuous_map_on X TX Y TY f" and hTX: "is_topology_on X TX"
  shows "top1_homotopic_on X TX Y TY f f"
proof -
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. f (fst p))"
    by (rule homotopy_const_continuous[OF hf hTX])
  moreover have "\<forall>x\<in>X. f (fst (x, 0)) = f x" by simp
  moreover have "\<forall>x\<in>X. f (fst (x, 1)) = f x" by simp
  ultimately show ?thesis
    unfolding top1_homotopic_on_def using hf by blast
qed

text \<open>The function t \<mapsto> 1-t is continuous I \<rightarrow> I.\<close>
lemma op_minus_continuous_on_interval:
  "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
proof -
  have hmap: "\<And>x. x \<in> I_set \<Longrightarrow> 1 - x \<in> I_set"
    unfolding top1_unit_interval_def by simp
  have hcont: "continuous_on UNIV (\<lambda>t::real. 1 - t)"
    by (rule continuous_on_op_minus)
  show ?thesis
    unfolding top1_unit_interval_topology_def
    by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
qed

text \<open>Helper: (x,t) \<mapsto> (x, 1-t) is continuous X\<times>I \<rightarrow> X\<times>I.
  Uses Theorem 18.4: map into product is continuous iff components are.\<close>
lemma flip_t_continuous_product:
  assumes hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, 1 - snd p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  let ?g = "\<lambda>p::'a \<times> real. (fst p, 1 - snd p)"
  have hid: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi12: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> id)
            \<and> top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> id)"
    using iffD1[OF Theorem_18_4[OF hTP hTX hTI] hid] by blast
  have hpi1_eq: "(pi1 :: 'a \<times> real \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 :: 'a \<times> real \<Rightarrow> real) = snd" unfolding pi2_def by (rule ext) simp
  have hpi1fst: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX fst"
    using hpi12 unfolding hpi1_eq by (simp add: comp_def)
  have hpi2snd: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top snd"
    using hpi12 unfolding hpi2_eq by (simp add: comp_def)
  have hc1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?g)"
  proof -
    have "pi1 \<circ> ?g = fst" unfolding hpi1_eq by auto
    thus ?thesis using hpi1fst by simp
  qed
  have hrev_snd: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (\<lambda>p. 1 - snd p)"
  proof -
    have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      by (rule op_minus_continuous_on_interval)
    have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
      ((\<lambda>t. 1 - t) \<circ> snd)"
      by (rule top1_continuous_map_on_comp[OF hpi2snd hrev])
    thus ?thesis by (simp add: comp_def)
  qed
  have hc2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?g)"
  proof -
    have "pi2 \<circ> ?g = (\<lambda>p. 1 - snd p)" unfolding hpi2_eq by auto
    thus ?thesis using hrev_snd by simp
  qed
  show ?thesis
    using iffD2[OF Theorem_18_4[OF hTP hTX hTI]] hc1 hc2 by blast
qed

lemma homotopy_reverse_continuous:
  assumes hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. F (fst p, 1 - snd p))"
proof -
  have hflip: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, 1 - snd p))"
    by (rule flip_t_continuous_product[OF hTX])
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (F \<circ> (\<lambda>p. (fst p, 1 - snd p)))"
    by (rule top1_continuous_map_on_comp[OF hflip hF])
  thus ?thesis by (simp add: comp_def)
qed

lemma Lemma_51_1_homotopic_sym:
  assumes h: "top1_homotopic_on X TX Y TY f f'" and hTX: "is_topology_on X TX"
  shows "top1_homotopic_on X TX Y TY f' f"
proof -
  obtain F where hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hF0: "\<forall>x\<in>X. F (x, 0) = f x" and hF1: "\<forall>x\<in>X. F (x, 1) = f' x"
    using h unfolding top1_homotopic_on_def by blast
  let ?G = "\<lambda>p. F (fst p, 1 - snd p)"
  have hG: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_reverse_continuous[OF hF hTX])
  have hG0: "\<forall>x\<in>X. ?G (x, 0) = f' x" using hF1 by simp
  have hG1: "\<forall>x\<in>X. ?G (x, 1) = f x" using hF0 by simp
  show ?thesis
    unfolding top1_homotopic_on_def
    using h hG hG0 hG1 unfolding top1_homotopic_on_def by blast
qed

text \<open>If two functions agree on S, and one is continuous on S, so is the other.\<close>
lemma top1_continuous_map_on_agree':
  assumes "top1_continuous_map_on S TS Y TY f" and "\<forall>x\<in>S. f x = g x"
  shows "top1_continuous_map_on S TS Y TY g"
proof -
  have "\<forall>x\<in>S. g x \<in> Y" using assms unfolding top1_continuous_map_on_def by auto
  moreover have "\<forall>V\<in>TY. {x \<in> S. g x \<in> V} \<in> TS"
  proof (intro ballI)
    fix V assume "V \<in> TY"
    have "{x \<in> S. g x \<in> V} = {x \<in> S. f x \<in> V}" using assms(2) by auto
    thus "{x \<in> S. g x \<in> V} \<in> TS" using assms(1) \<open>V \<in> TY\<close> unfolding top1_continuous_map_on_def by simp
  qed
  ultimately show ?thesis unfolding top1_continuous_map_on_def by blast
qed

text \<open>Helper: concatenation of homotopies via pasting lemma.
  Given F: X\<times>I \<rightarrow> Y and F': X\<times>I \<rightarrow> Y with F(x,1) = F'(x,0), define
  G(x,t) = F(x,2t) for t\<le>1/2, G(x,t) = F'(x,2t-1) for t\<ge>1/2.\<close>
lemma homotopy_concat_continuous:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
      and hF': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
      and hmatch: "\<forall>x\<in>X. F (x, 1) = F' (x, 0)"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
proof -
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hTXI: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  let ?A = "X \<times> {t\<in>I_set. t \<le> 1/2}"
  let ?B = "X \<times> {t\<in>I_set. t \<ge> 1/2}"
  have hX_open: "X \<in> TX" using hTX unfolding is_topology_on_def by blast
  have hA_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> X \<times> I_set" by auto
    have "X \<times> I_set - ?A = X \<times> {t\<in>I_set. t > 1/2}" unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> product_topology_on TX I_top"
    proof -
      have "open {t :: real. t > 1/2}" by (rule open_Collect_less[OF continuous_on_const continuous_on_id])
      hence "{t :: real. t > 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
      hence "I_set \<inter> {t. t > 1/2} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by blast
      moreover have "{t\<in>I_set. t > 1/2} = I_set \<inter> {t. t > 1/2}" by auto
      ultimately have "{t\<in>I_set. t > 1/2} \<in> I_top" by simp
      thus ?thesis by (rule product_rect_open[OF hX_open])
    qed
    finally show "X \<times> I_set - ?A \<in> product_topology_on TX I_top" .
  qed
  have hB_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> X \<times> I_set" by auto
    have "X \<times> I_set - ?B = X \<times> {t\<in>I_set. t < 1/2}" unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> product_topology_on TX I_top"
    proof -
      have "open {t :: real. t < 1/2}" by (rule open_Collect_less[OF continuous_on_id continuous_on_const])
      hence "{t :: real. t < 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
      hence "I_set \<inter> {t. t < 1/2} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by blast
      moreover have "{t\<in>I_set. t < 1/2} = I_set \<inter> {t. t < 1/2}" by auto
      ultimately have "{t\<in>I_set. t < 1/2} \<in> I_top" by simp
      thus ?thesis by (rule product_rect_open[OF hX_open])
    qed
    finally show "X \<times> I_set - ?B \<in> product_topology_on TX I_top" .
  qed
  have hcover: "?A \<union> ?B = X \<times> I_set" unfolding top1_unit_interval_def by auto
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hF_range: "\<forall>p\<in>X \<times> I_set. F p \<in> Y" using hF unfolding top1_continuous_map_on_def by blast
  have hF'_range: "\<forall>p\<in>X \<times> I_set. F' p \<in> Y" using hF' unfolding top1_continuous_map_on_def by blast
  have hG_range: "\<forall>p\<in>X \<times> I_set. ?G p \<in> Y"
  proof
    fix p assume hp: "p \<in> X \<times> I_set"
    show "?G p \<in> Y"
    proof (cases "snd p \<le> 1/2")
      case True
      have "(fst p, 2 * snd p) \<in> X \<times> I_set" using hp True unfolding top1_unit_interval_def by auto
      thus ?thesis using True hF_range by simp
    next
      case False
      have "(fst p, 2 * snd p - 1) \<in> X \<times> I_set" using hp False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hF'_range by simp
    qed
  qed
  \<comment> \<open>Reparametrize only 2nd component: (id_X, \<phi>) continuous from subspace to product.\<close>
  have reparam_full: "\<And>\<phi>. top1_continuous_map_on I_set I_top I_set I_top \<phi> \<Longrightarrow>
    top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
  proof -
    fix \<phi> assume h\<phi>: "top1_continuous_map_on I_set I_top I_set I_top \<phi>"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
      by (rule product_topology_on_is_topology_on[OF hTX hTI])
    have hpi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
      by (rule top1_continuous_pi1[OF hTX hTI])
    have hpi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
      by (rule top1_continuous_pi2[OF hTX hTI])
    have hphi_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (\<phi> \<circ> pi2)"
      by (rule top1_continuous_map_on_comp[OF hpi2 h\<phi>])
    have hp1_eq: "pi1 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))) = pi1"
      unfolding pi1_def by (rule ext) auto
    have hp2_eq: "pi2 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))) = \<phi> \<circ> pi2"
      unfolding pi2_def comp_def by (rule ext) auto
    have hp1_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
        (pi1 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))))"
      unfolding hp1_eq by (rule hpi1)
    have hp2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
        (pi2 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))))"
      unfolding hp2_eq by (rule hphi_pi2)
    show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
      using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of "\<lambda>p. (fst p, \<phi> (snd p))"]]
      hp1_cont hp2_cont by blast
  qed
  have reparam_snd: "\<And>S \<phi>. \<lbrakk>S \<subseteq> I_set;
    top1_continuous_map_on I_set I_top I_set I_top \<phi>\<rbrakk> \<Longrightarrow>
    top1_continuous_map_on (X \<times> S) (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> S))
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
    by (intro top1_continuous_map_on_restrict_domain_simple[OF reparam_full]) auto \<comment> \<open>Preimage of U1\<times>U2: (X\<times>S) \<inter> (U1 \<times> \<phi>⁻¹(U2)), where \<phi>⁻¹(U2) = S \<inter> V for V \<in> I_top.
           So preimage = (X\<times>S) \<inter> (U1 \<times> V) \<in> sub (X\<times>I) (product TX I_top) (X\<times>S).\<close>
  \<comment> \<open>Clamped scaling maps I \<rightarrow> I.\<close>
  have hscale2c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. min 1 (2*t))"
  proof -
    have hmap: "\<And>t. t \<in> I_set \<Longrightarrow> min 1 (2*t) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. min 1 (2*t))" by (intro continuous_intros)
    have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
            I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. min 1 (2*t))"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  have hscale2m1c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. max 0 (2*t - 1))"
  proof -
    have hmap: "\<And>t. t \<in> I_set \<Longrightarrow> max 0 (2*t - 1) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. max 0 (2*t - 1))" by (intro continuous_intros)
    have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
            I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. max 0 (2*t - 1))"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  have hscale2: "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
    (subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}) I_set I_top (\<lambda>t. 2*t)"
  proof -
    have hmap: "\<And>t. t \<in> {t\<in>I_set. t \<le> 1/2} \<Longrightarrow> 2*t \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV ((*) (2::real))" by (intro continuous_intros)
    have hraw: "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
      (subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<le> 1/2})
      I_set (subspace_topology UNIV top1_open_sets I_set) ((*) 2)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    have hdom: "subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}
              = subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<le> 1/2}"
      unfolding top1_unit_interval_topology_def by (rule subspace_topology_trans) auto
    have hcod: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
      (subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}) I_set I_top ((*) 2)"
      using hraw hdom hcod by simp
    moreover have "((*) (2::real)) = (\<lambda>t. 2*t)" by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have hscale2m1: "top1_continuous_map_on {t\<in>I_set. t \<ge> 1/2}
    (subspace_topology I_set I_top {t\<in>I_set. t \<ge> 1/2}) I_set I_top (\<lambda>t. 2*t - 1)"
  proof -
    have hmap: "\<And>t. t \<in> {t\<in>I_set. t \<ge> 1/2} \<Longrightarrow> 2*t - 1 \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. 2*t - 1)" by (intro continuous_intros)
    have hraw: "top1_continuous_map_on {t\<in>I_set. t \<ge> 1/2}
      (subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<ge> 1/2})
      I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 2*t - 1)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    have hdom: "subspace_topology I_set I_top {t\<in>I_set. t \<ge> 1/2}
              = subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<ge> 1/2}"
      unfolding top1_unit_interval_topology_def by (rule subspace_topology_trans) auto
    have hcod: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    show ?thesis using hraw hdom hcod by simp
  qed
  have hFA: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
    Y TY (\<lambda>p. F (fst p, 2 * snd p))"
  proof -
    have "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, min 1 (2 * snd p)))"
      by (rule reparam_snd[OF _ hscale2c]) auto
    hence hFA_c: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
      Y TY (\<lambda>p. F (fst p, min 1 (2 * snd p)))"
      using top1_continuous_map_on_comp[of ?A _ _ _ "(\<lambda>p. (fst p, min 1 (2 * snd p)))" _ _ F] hF
      by (simp add: comp_def)
    show ?thesis by (rule top1_continuous_map_on_agree'[OF hFA_c])
      (auto simp: top1_unit_interval_def)
  qed
  have hGA: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A) Y TY ?G"
    by (rule top1_continuous_map_on_agree'[OF hFA]) auto
  have hFB: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
    Y TY (\<lambda>p. F' (fst p, 2 * snd p - 1))"
  proof -
    have "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, max 0 (2 * snd p - 1)))"
      by (rule reparam_snd[OF _ hscale2m1c]) auto
    hence hFB_c: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
      Y TY (\<lambda>p. F' (fst p, max 0 (2 * snd p - 1)))"
      using top1_continuous_map_on_comp[of ?B _ _ _ "(\<lambda>p. (fst p, max 0 (2 * snd p - 1)))" _ _ F'] hF'
      by (simp add: comp_def)
    show ?thesis by (rule top1_continuous_map_on_agree'[OF hFB_c])
      (auto simp: top1_unit_interval_def)
  qed
  have hGB: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B) Y TY ?G"
  proof (rule top1_continuous_map_on_agree'[OF hFB])
    show "\<forall>p\<in>?B. F' (fst p, 2 * snd p - 1) = ?G p"
    proof
      fix p assume hp: "p \<in> ?B"
      show "F' (fst p, 2 * snd p - 1) = ?G p"
      proof (cases "snd p > 1/2")
        case True thus ?thesis by simp
      next
        case False hence "snd p = 1/2" using hp by auto
        hence "2 * snd p = 1" "2 * snd p - 1 = 0" by simp_all
        thus ?thesis using hmatch hp by auto
      qed
    qed
  qed
  show ?thesis
    by (rule pasting_lemma_two_closed[OF hTXI hTY hA_closed hB_closed hcover hG_range hGA hGB])
qed

lemma Lemma_51_1_homotopic_trans:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and h1: "top1_homotopic_on X TX Y TY f f'"
      and h2: "top1_homotopic_on X TX Y TY f' f''"
  shows "top1_homotopic_on X TX Y TY f f''"
proof -
  obtain F where hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hF0: "\<forall>x\<in>X. F (x, 0) = f x" and hF1: "\<forall>x\<in>X. F (x, 1) = f' x"
    using h1 unfolding top1_homotopic_on_def by blast
  obtain F' where hF': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
    and hF'0: "\<forall>x\<in>X. F' (x, 0) = f' x" and hF'1: "\<forall>x\<in>X. F' (x, 1) = f'' x"
    using h2 unfolding top1_homotopic_on_def by blast
  have hmatch: "\<forall>x\<in>X. F (x, 1) = F' (x, 0)" using hF1 hF'0 by simp
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hG: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_concat_continuous[OF hTX hTY hF hF' hmatch])
  have hG0: "\<forall>x\<in>X. ?G (x, 0) = f x" using hF0 by simp
  have hG1: "\<forall>x\<in>X. ?G (x, 1) = f'' x" using hF'1 by simp
  show ?thesis
    unfolding top1_homotopic_on_def
    using h1 h2 hG hG0 hG1 unfolding top1_homotopic_on_def by blast
qed

text \<open>Helper: f \<circ> pi_1 continuous from I \<times> I \<rightarrow> X when f: I \<rightarrow> X is continuous.\<close>
lemma path_homotopy_const_continuous:
  assumes hf: "top1_continuous_map_on I_set I_top X TX f"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  have hid: "top1_continuous_map_on (I_set \<times> I_set) II_topology
    (I_set \<times> I_set) II_topology id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> id)"
    unfolding II_topology_def
    using iffD1[OF Theorem_18_4[OF hTP[unfolded II_topology_def] hTI hTI] hid[unfolded II_topology_def]]
    by blast
  have hpi1': "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
    using hpi1 by (simp add: comp_def)
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1' hf])
  thus ?thesis by (simp add: comp_def pi1_def)
qed

lemma Lemma_51_1_path_homotopic_refl:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1 f f"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
    by (rule path_homotopy_const_continuous[OF hfc])
  moreover have "\<forall>s\<in>I_set. f (fst (s, 0)) = f s" by simp
  moreover have "\<forall>s\<in>I_set. f (fst (s, 1)) = f s" by simp
  moreover have "\<forall>t\<in>I_set. f (fst (0, t)) = x0"
    using hf unfolding top1_is_path_on_def by simp
  moreover have "\<forall>t\<in>I_set. f (fst (1, t)) = x1"
    using hf unfolding top1_is_path_on_def by simp
  ultimately show ?thesis
    unfolding top1_path_homotopic_on_def using hf by blast
qed

text \<open>Helper: if F: I\<times>I\<rightarrow>X is continuous, so is G(s,t) = F(s, 1-t).\<close>
lemma path_homotopy_reverse_continuous:
  assumes hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. F (fst p, 1 - snd p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hflip: "top1_continuous_map_on (I_set \<times> I_set) II_topology
    (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 1 - snd p))"
    unfolding II_topology_def
    by (rule flip_t_continuous_product[OF hTI])
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (F \<circ> (\<lambda>p. (fst p, 1 - snd p)))"
    by (rule top1_continuous_map_on_comp[OF hflip hF])
  thus ?thesis by (simp add: comp_def)
qed

lemma Lemma_51_1_path_homotopic_sym:
  assumes h: "top1_path_homotopic_on X TX x0 x1 f f'"
  shows "top1_path_homotopic_on X TX x0 x1 f' f"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = f' s"
    and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using h unfolding top1_path_homotopic_on_def by blast
  let ?G = "\<lambda>p. F (fst p, 1 - snd p)"
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
    by (rule path_homotopy_reverse_continuous[OF hF])
  have hG0: "\<forall>s\<in>I_set. ?G (s, 0) = f' s" using hF1 by simp
  have hG1: "\<forall>s\<in>I_set. ?G (s, 1) = f s" using hF0 by simp
  have hGleft: "\<forall>t\<in>I_set. ?G (0, t) = x0"
    using hFleft unfolding top1_unit_interval_def by simp
  have hGright: "\<forall>t\<in>I_set. ?G (1, t) = x1"
    using hFright unfolding top1_unit_interval_def by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using h hG hG0 hG1 hGleft hGright unfolding top1_path_homotopic_on_def by blast
qed

text \<open>Helper: concatenation of path homotopies.

  Proof via pasting lemma (Theorem 18.3):
  A = I \<times> [0, 1/2] and B = I \<times> [1/2, 1] are closed in I \<times> I;
  F(fst p, 2\<cdot>snd p) is continuous on A; F'(fst p, 2\<cdot>snd p - 1) is
  continuous on B; they agree on A \<inter> B (where snd p = 1/2) by hmatch.\<close>

lemma top1_continuous_map_on_codomain_shrink:
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
      and himg: "f ` X \<subseteq> W" and hWY: "W \<subseteq> Y"
  shows "top1_continuous_map_on X TX W (subspace_topology Y TY W) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI)
  show "\<forall>x\<in>X. f x \<in> W" using himg by blast
next
  show "\<forall>V\<in>subspace_topology Y TY W. {x \<in> X. f x \<in> V} \<in> TX"
  proof
    fix V assume "V \<in> subspace_topology Y TY W"
    then obtain U where hU: "U \<in> TY" and hVeq: "V = W \<inter> U"
      unfolding subspace_topology_def by blast
    have "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> U}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> {x \<in> X. f x \<in> V}" thus "x \<in> {x \<in> X. f x \<in> U}" using hVeq by blast
    next
      fix x assume hx: "x \<in> {x \<in> X. f x \<in> U}"
      hence "f x \<in> W" using himg by blast
      thus "x \<in> {x \<in> X. f x \<in> V}" using hx hVeq by blast
    qed
    also have "\<dots> \<in> TX" using hcont hU unfolding top1_continuous_map_on_def by blast
    finally show "{x \<in> X. f x \<in> V} \<in> TX" .
  qed
qed

lemma path_homotopy_concat_continuous:
  assumes hTX: "is_topology_on X TX"
      and hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
      and hmatch: "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
proof -
  \<comment> \<open>Close sets A = I \<times> [0, 1/2] and B = I \<times> [1/2, 1].\<close>
  let ?A = "I_set \<times> {t\<in>I_set. t \<le> 1/2}"
  let ?B = "I_set \<times> {t\<in>I_set. t \<ge> 1/2}"
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
  have hA_half_closed: "closedin_on I_set I_top {t\<in>I_set. t \<le> 1/2}"
    unfolding closedin_on_def
  proof (intro conjI)
    show "{t\<in>I_set. t \<le> 1/2} \<subseteq> I_set" by auto
    have "I_set - {t\<in>I_set. t \<le> 1/2} = I_set \<inter> {s :: real. s > 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> I_top"
      unfolding top1_unit_interval_topology_def subspace_topology_def
      using open_greaterThan[of "1/2::real"]
      unfolding top1_open_sets_def greaterThan_def by blast
    finally show "I_set - {t\<in>I_set. t \<le> 1/2} \<in> I_top" .
  qed
  have hB_half_closed: "closedin_on I_set I_top {t\<in>I_set. t \<ge> 1/2}"
    unfolding closedin_on_def
  proof (intro conjI)
    show "{t\<in>I_set. t \<ge> 1/2} \<subseteq> I_set" by auto
    have "I_set - {t\<in>I_set. t \<ge> 1/2} = I_set \<inter> {s :: real. s < 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> I_top"
      unfolding top1_unit_interval_topology_def subspace_topology_def
      using open_lessThan[of "1/2::real"]
      unfolding top1_open_sets_def lessThan_def by blast
    finally show "I_set - {t\<in>I_set. t \<ge> 1/2} \<in> I_top" .
  qed
  have hA_closed: "closedin_on (I_set \<times> I_set) II_topology ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> I_set \<times> I_set" by auto
    have "I_set \<times> I_set - ?A = I_set \<times> {t\<in>I_set. t > 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> II_topology"
    proof -
      have "{t\<in>I_set. t > 1/2} = I_set - {t\<in>I_set. t \<le> 1/2}"
        unfolding top1_unit_interval_def by auto
      hence "{t\<in>I_set. t > 1/2} \<in> I_top"
        using hA_half_closed unfolding closedin_on_def by simp
      thus ?thesis
        unfolding II_topology_def by (rule product_rect_open[OF hI_open])
    qed
    finally show "I_set \<times> I_set - ?A \<in> II_topology" .
  qed
  have hB_closed: "closedin_on (I_set \<times> I_set) II_topology ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> I_set \<times> I_set" by auto
    have "I_set \<times> I_set - ?B = I_set \<times> {t\<in>I_set. t < 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> II_topology"
    proof -
      have "{t\<in>I_set. t < 1/2} = I_set - {t\<in>I_set. t \<ge> 1/2}"
        unfolding top1_unit_interval_def by auto
      hence "{t\<in>I_set. t < 1/2} \<in> I_top"
        using hB_half_closed unfolding closedin_on_def by simp
      thus ?thesis
        unfolding II_topology_def by (rule product_rect_open[OF hI_open])
    qed
    finally show "I_set \<times> I_set - ?B \<in> II_topology" .
  qed
  have hcover: "I_set \<times> I_set = ?A \<union> ?B"
    unfolding top1_unit_interval_def by auto
  \<comment> \<open>On A, (s,t) \<mapsto> F(s, 2t) is continuous via composition with reparametrization.\<close>
  have h\<phi>A: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
               (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 2 * snd (p::real\<times>real)))"
  proof -
    let ?\<phi> = "\<lambda>p :: real \<times> real. (fst p, 2 * snd p)"
    have hcont: "continuous_on UNIV ?\<phi>" by (intro continuous_intros)
    have hmap: "\<And>p. p \<in> ?A \<Longrightarrow> ?\<phi> p \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by auto
    have hraw: "top1_continuous_map_on ?A
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A)
                 (I_set \<times> I_set)
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                 ?\<phi>"
      by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
    have hAsub: "?A \<subseteq> I_set \<times> I_set" by auto
    have hdom_eq: "subspace_topology (I_set \<times> I_set) II_topology ?A
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A"
    proof -
      have "subspace_topology (I_set \<times> I_set)
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
              ?A
            = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A"
        by (rule subspace_topology_trans[OF hAsub])
      thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
    qed
    have hcod_eq: "II_topology
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      unfolding II_topology_def by (rule II_topology_eq_subspace)
    show ?thesis using hraw hdom_eq hcod_eq by simp
  qed
  have hfA: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
                                   X TX (\<lambda>p. F (fst p, 2 * snd p))"
  proof -
    have hcomp: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
            X TX (F \<circ> (\<lambda>p. (fst p, 2 * snd p)))"
      by (rule top1_continuous_map_on_comp[OF h\<phi>A hF])
    moreover have "F \<circ> (\<lambda>p. (fst p, 2 * snd p)) = (\<lambda>p. F (fst p, 2 * snd p))"
      by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have h\<phi>B: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
               (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 2 * snd (p::real\<times>real) - 1))"
  proof -
    let ?\<psi> = "\<lambda>p :: real \<times> real. (fst p, 2 * snd p - 1)"
    have hcont: "continuous_on UNIV ?\<psi>" by (intro continuous_intros)
    have hmap: "\<And>p. p \<in> ?B \<Longrightarrow> ?\<psi> p \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by auto
    have hraw: "top1_continuous_map_on ?B
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B)
                 (I_set \<times> I_set)
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                 ?\<psi>"
      by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
    have hBsub: "?B \<subseteq> I_set \<times> I_set" by auto
    have hdom_eq: "subspace_topology (I_set \<times> I_set) II_topology ?B
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B"
    proof -
      have "subspace_topology (I_set \<times> I_set)
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
              ?B
            = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B"
        by (rule subspace_topology_trans[OF hBsub])
      thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
    qed
    have hcod_eq: "II_topology
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      unfolding II_topology_def by (rule II_topology_eq_subspace)
    show ?thesis using hraw hdom_eq hcod_eq by simp
  qed
  have hfB: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
                                   X TX (\<lambda>p. F' (fst p, 2 * snd p - 1))"
  proof -
    have hcomp: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
            X TX (F' \<circ> (\<lambda>p. (fst p, 2 * snd p - 1)))"
      by (rule top1_continuous_map_on_comp[OF h\<phi>B hF'])
    moreover have "F' \<circ> (\<lambda>p. (fst p, 2 * snd p - 1)) = (\<lambda>p. F' (fst p, 2 * snd p - 1))"
      by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Agreement on A \<inter> B (where snd p = 1/2).\<close>
  have hagree: "\<forall>p\<in>?A \<inter> ?B. F (fst p, 2 * snd p) = F' (fst p, 2 * snd p - 1)"
  proof (intro ballI)
    fix p assume hp: "p \<in> ?A \<inter> ?B"
    have ht_half: "snd p = 1/2" using hp by force
    have hs: "fst p \<in> I_set" using hp by force
    have h2t: "2 * snd p = 1" using ht_half by simp
    have h2tm1: "2 * snd p - 1 = 0" using ht_half by simp
    show "F (fst p, 2 * snd p) = F' (fst p, 2 * snd p - 1)"
      using h2t h2tm1 hmatch[rule_format, OF hs] by simp
  qed
  \<comment> \<open>Apply pasting lemma.\<close>
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. F p \<in> X"
    using hF unfolding top1_continuous_map_on_def by blast
  have hF'_range: "\<forall>p\<in>I_set \<times> I_set. F' p \<in> X"
    using hF' unfolding top1_continuous_map_on_def by blast
  have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
  proof (intro ballI)
    fix p assume hp: "p \<in> I_set \<times> I_set"
    show "?G p \<in> X"
    proof (cases "snd p \<le> 1/2")
      case True
      have hmem: "(fst p, 2 * snd p) \<in> I_set \<times> I_set"
        using hp True unfolding top1_unit_interval_def by auto
      have "?G p = F (fst p, 2 * snd p)" using True by simp
      moreover have "F (fst p, 2 * snd p) \<in> X" by (rule bspec[OF hF_range hmem])
      ultimately show ?thesis by simp
    next
      case False
      have hmem: "(fst p, 2 * snd p - 1) \<in> I_set \<times> I_set"
        using hp False unfolding top1_unit_interval_def by auto
      have "?G p = F' (fst p, 2 * snd p - 1)" using False by simp
      moreover have "F' (fst p, 2 * snd p - 1) \<in> X" by (rule bspec[OF hF'_range hmem])
      ultimately show ?thesis by simp
    qed
  qed
  have hGA: "\<forall>p\<in>?A. ?G p = F (fst p, 2 * snd p)" by auto
  have hGB: "\<forall>p\<in>?B. ?G p = F' (fst p, 2 * snd p - 1)"
  proof
    fix p assume hp: "p \<in> ?B"
    hence hge: "snd p \<ge> 1/2" by auto
    show "?G p = F' (fst p, 2 * snd p - 1)"
    proof (cases "snd p > 1/2")
      case True thus ?thesis by simp
    next
      case False
      hence "snd p = 1/2" using hge by simp
      hence h2t: "2 * snd p = 1" and h2tm1: "2 * snd p - 1 = 0" by simp_all
      have hs: "fst p \<in> I_set" using hp by auto
      show ?thesis using h2t h2tm1 hmatch[rule_format, OF hs] by simp
    qed
  qed
  have hgA: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A) X TX ?G"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>?A. ?G x \<in> X"
    proof
      fix x assume "x \<in> ?A"
      hence "x \<in> I_set \<times> I_set" by auto
      thus "?G x \<in> X" using hG_range by blast
    qed
  next
    show "\<forall>V\<in>TX. {x \<in> ?A. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?A"
    proof
      fix V assume hV: "V \<in> TX"
      have "{x \<in> ?A. ?G x \<in> V} = {x \<in> ?A. F (fst x, 2 * snd x) \<in> V}"
        using hGA by auto
      also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?A"
        using hfA hV unfolding top1_continuous_map_on_def by blast
      finally show "{x \<in> ?A. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?A" .
    qed
  qed
  have hgB: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B) X TX ?G"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>?B. ?G x \<in> X"
    proof
      fix x assume "x \<in> ?B"
      hence "x \<in> I_set \<times> I_set" by auto
      thus "?G x \<in> X" using hG_range by blast
    qed
  next
    show "\<forall>V\<in>TX. {x \<in> ?B. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?B"
    proof
      fix V assume hV: "V \<in> TX"
      have "{x \<in> ?B. ?G x \<in> V} = {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> ?B. ?G x \<in> V}"
        hence hxB: "x \<in> ?B" and hGV: "?G x \<in> V" by auto
        have "?G x = F' (fst x, 2 * snd x - 1)" using hGB hxB by blast
        hence "F' (fst x, 2 * snd x - 1) \<in> V" using hGV by simp
        thus "x \<in> {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}" using hxB by blast
      next
        fix x assume "x \<in> {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}"
        hence hxB: "x \<in> ?B" and hFV: "F' (fst x, 2 * snd x - 1) \<in> V" by auto
        have "?G x = F' (fst x, 2 * snd x - 1)" using hGB hxB by blast
        hence "?G x \<in> V" using hFV by simp
        thus "x \<in> {x \<in> ?B. ?G x \<in> V}" using hxB by blast
      qed
      also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?B"
        using hfB hV unfolding top1_continuous_map_on_def by blast
      finally show "{x \<in> ?B. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?B" .
    qed
  qed
  show ?thesis
  proof (rule pasting_lemma_two_closed[where
      X = "I_set \<times> I_set" and TX = II_topology and Y = X and TY = TX
      and A = ?A and B = ?B and f = ?G])
    show "is_topology_on (I_set \<times> I_set) II_topology" by (rule hTII)
    show "is_topology_on X TX" by (rule hTX)
    show "closedin_on (I_set \<times> I_set) II_topology ?A" by (rule hA_closed)
    show "closedin_on (I_set \<times> I_set) II_topology ?B" by (rule hB_closed)
    show "?A \<union> ?B = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    show "\<forall>x\<in>I_set \<times> I_set. ?G x \<in> X" by (rule hG_range)
    show "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A) X TX ?G"
      by (rule hgA)
    show "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B) X TX ?G"
      by (rule hgB)
  qed
qed

lemma Lemma_51_1_path_homotopic_trans:
  assumes hTX: "is_topology_on X TX"
      and h1: "top1_path_homotopic_on X TX x0 x1 f f'"
      and h2: "top1_path_homotopic_on X TX x0 x1 f' f''"
  shows "top1_path_homotopic_on X TX x0 x1 f f''"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = f' s"
    and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using h1 unfolding top1_path_homotopic_on_def by blast
  obtain F' where hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
    and hF'0: "\<forall>s\<in>I_set. F' (s, 0) = f' s" and hF'1: "\<forall>s\<in>I_set. F' (s, 1) = f'' s"
    and hF'left: "\<forall>t\<in>I_set. F' (0, t) = x0" and hF'right: "\<forall>t\<in>I_set. F' (1, t) = x1"
    using h2 unfolding top1_path_homotopic_on_def by blast
  have hmatch: "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)" using hF1 hF'0 by simp
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
    by (rule path_homotopy_concat_continuous[OF hTX hF hF' hmatch])
  have hG0: "\<forall>s\<in>I_set. ?G (s, 0) = f s" using hF0 by simp
  have hG1: "\<forall>s\<in>I_set. ?G (s, 1) = f'' s" using hF'1 by simp
  have hGleft: "\<forall>t\<in>I_set. ?G (0, t) = x0"
  proof (intro ballI)
    fix t assume ht: "t \<in> I_set"
    have htpos: "0 \<le> t" using ht unfolding top1_unit_interval_def by simp
    have htle1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    show "?G (0, t) = x0"
    proof (cases "t \<le> 1/2")
      case True
      have h2t: "2 * t \<in> I_set" using htpos True unfolding top1_unit_interval_def by simp
      have "?G (0, t) = F (0, 2 * t)" using True by simp
      also have "... = x0" using hFleft h2t by simp
      finally show ?thesis .
    next
      case False
      have h2t: "2 * t - 1 \<in> I_set"
        using False htle1 unfolding top1_unit_interval_def by simp
      have "?G (0, t) = F' (0, 2 * t - 1)" using False by simp
      also have "... = x0" using hF'left h2t by simp
      finally show ?thesis .
    qed
  qed
  have hGright: "\<forall>t\<in>I_set. ?G (1, t) = x1"
  proof (intro ballI)
    fix t assume ht: "t \<in> I_set"
    have htpos: "0 \<le> t" using ht unfolding top1_unit_interval_def by simp
    have htle1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    show "?G (1, t) = x1"
    proof (cases "t \<le> 1/2")
      case True
      have h2t: "2 * t \<in> I_set" using htpos True unfolding top1_unit_interval_def by simp
      have "?G (1, t) = F (1, 2 * t)" using True by simp
      also have "... = x1" using hFright h2t by simp
      finally show ?thesis .
    next
      case False
      have h2t: "2 * t - 1 \<in> I_set"
        using False htle1 unfolding top1_unit_interval_def by simp
      have "?G (1, t) = F' (1, 2 * t - 1)" using False by simp
      also have "... = x1" using hF'right h2t by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using h1 h2 hG hG0 hG1 hGleft hGright unfolding top1_path_homotopic_on_def by blast
qed

text \<open>Product of paths: f*g is f followed by g, reparameterized to [0,1].\<close>
definition top1_path_product :: "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_product f g = (\<lambda>s. if s \<le> 1/2 then f (2 * s) else g (2 * s - 1))"

text \<open>Reverse of a path: \<bar>f(s) = f(1-s).\<close>
definition top1_path_reverse :: "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_reverse f = (\<lambda>s. f (1 - s))"

text \<open>Constant path at a point x.\<close>
definition top1_constant_path :: "'a \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_constant_path x = (\<lambda>_. x)"

lemma top1_path_product_at_start:
  "top1_path_product f g 0 = f 0"
  unfolding top1_path_product_def by simp

lemma top1_path_product_at_end:
  "top1_path_product f g 1 = g 1"
  unfolding top1_path_product_def by simp

lemma top1_path_product_at_half:
  "top1_path_product f g (1/2) = f 1"
  unfolding top1_path_product_def by simp

lemma top1_path_reverse_at_start:
  "top1_path_reverse f 0 = f 1"
  unfolding top1_path_reverse_def by simp

lemma top1_path_reverse_at_end:
  "top1_path_reverse f 1 = f 0"
  unfolding top1_path_reverse_def by simp

lemma top1_path_reverse_twice:
  "top1_path_reverse (top1_path_reverse f) = f"
  unfolding top1_path_reverse_def by auto

lemma top1_constant_path_value:
  "top1_constant_path x t = x"
  unfolding top1_constant_path_def by simp

text \<open>The product of paths is well-defined when endpoints match.\<close>

text \<open>Helper: the reverse path is continuous.\<close>
lemma top1_path_reverse_continuous:
  assumes hf: "top1_continuous_map_on I_set I_top X TX f"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_reverse f)"
proof -
  have hr: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
    by (rule op_minus_continuous_on_interval)
  have "top1_continuous_map_on I_set I_top X TX (f \<circ> (\<lambda>t. 1 - t))"
    by (rule top1_continuous_map_on_comp[OF hr hf])
  thus ?thesis
    unfolding top1_path_reverse_def by (simp add: comp_def)
qed

lemma top1_path_reverse_is_path:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_reverse f)"
    by (rule top1_path_reverse_continuous[OF hfc])
  have hstart: "top1_path_reverse f 0 = x1"
    unfolding top1_path_reverse_def using hf1 by simp
  have hend: "top1_path_reverse f 1 = x0"
    unfolding top1_path_reverse_def using hf0 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

text \<open>Helper: constant path is continuous.\<close>
lemma top1_constant_path_continuous:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_continuous_map_on I_set I_top X TX (top1_constant_path x)"
  unfolding top1_constant_path_def
  by (rule top1_continuous_map_on_const[OF top1_unit_interval_topology_is_topology_on assms])

lemma top1_constant_path_is_path:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_is_path_on X TX x x (top1_constant_path x)"
  unfolding top1_is_path_on_def top1_constant_path_def
  using top1_constant_path_continuous[OF assms]
  unfolding top1_constant_path_def by simp

text \<open>Helper: the concatenated path is continuous via the pasting lemma on [0,1/2] \<union> [1/2,1].\<close>
lemma top1_path_product_continuous:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on I_set I_top X TX f"
      and hg: "top1_continuous_map_on I_set I_top X TX g"
      and hmatch: "f 1 = g 0"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
proof -
  let ?A = "{s\<in>I_set. s \<le> 1/2}"
  let ?B = "{s\<in>I_set. s \<ge> 1/2}"
  let ?h = "top1_path_product f g"
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hAB: "?A \<union> ?B = I_set"
    unfolding top1_unit_interval_def by auto
  \<comment> \<open>Range: f*g maps into X.\<close>
  have hf_range: "\<forall>s\<in>I_set. f s \<in> X"
    using hf unfolding top1_continuous_map_on_def by blast
  have hg_range: "\<forall>s\<in>I_set. g s \<in> X"
    using hg unfolding top1_continuous_map_on_def by blast
  have hh_range: "\<forall>s\<in>I_set. ?h s \<in> X"
  proof (intro ballI)
    fix s assume hs: "s \<in> I_set"
    show "?h s \<in> X"
    proof (cases "s \<le> 1/2")
      case True
      have "2 * s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      thus ?thesis unfolding top1_path_product_def using True hf_range by simp
    next
      case False
      have "2 * s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by simp
      thus ?thesis unfolding top1_path_product_def using False hg_range by simp
    qed
  qed
  \<comment> \<open>Closedness of A and B in I, and continuity on each piece — requires pasting infrastructure.\<close>
  have hA_closed: "closedin_on I_set I_top ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> I_set" by auto
  next
    show "I_set - ?A \<in> I_top"
    proof -
      have heq: "I_set - ?A = I_set \<inter> {s :: real. s > 1/2}"
        unfolding top1_unit_interval_def by auto
      have hopen: "{s :: real. s > 1/2} \<in> top1_open_sets"
        unfolding top1_open_sets_def
        using open_greaterThan[of "1/2 :: real"]
        by (simp add: greaterThan_def Collect_mono_iff)
      show ?thesis
        unfolding heq top1_unit_interval_topology_def subspace_topology_def
        using hopen by blast
    qed
  qed
  have hB_closed: "closedin_on I_set I_top ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> I_set" by auto
  next
    show "I_set - ?B \<in> I_top"
    proof -
      have heq: "I_set - ?B = I_set \<inter> {s :: real. s < 1/2}"
        unfolding top1_unit_interval_def by auto
      have hopen: "{s :: real. s < 1/2} \<in> top1_open_sets"
        unfolding top1_open_sets_def
        using open_lessThan[of "1/2 :: real"]
        by (simp add: lessThan_def Collect_mono_iff)
      show ?thesis
        unfolding heq top1_unit_interval_topology_def subspace_topology_def
        using hopen by blast
    qed
  qed
  have hhA: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A) X TX ?h"
  proof -
    \<comment> \<open>On A, h = f \<circ> (2\<cdot>). Scale is continuous A \<rightarrow> I.\<close>
    have hscale_map: "\<And>s. s \<in> ?A \<Longrightarrow> 2 * s \<in> I_set"
      unfolding top1_unit_interval_def by auto
    have hscale_cont: "continuous_on UNIV (\<lambda>s :: real. 2 * s)"
      by (intro continuous_intros)
    have hsub_eq: "subspace_topology I_set I_top ?A = subspace_topology UNIV top1_open_sets ?A"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_trans, auto)
    have hItop_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have hscale_raw: "top1_continuous_map_on ?A (subspace_topology UNIV top1_open_sets ?A)
                       I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>s. 2 * s)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hscale_map hscale_cont])
    have hscale: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A)
                   I_set I_top (\<lambda>s. 2 * s)"
      using hscale_raw hsub_eq hItop_eq by simp
    have hcomp: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A) X TX (f \<circ> (\<lambda>s. 2 * s))"
      by (rule top1_continuous_map_on_comp[OF hscale hf])
    \<comment> \<open>h agrees with f \<circ> (2\<cdot>) on A.\<close>
    have hfunceq: "\<And>s. s \<in> ?A \<Longrightarrow> ?h s = (f \<circ> (\<lambda>s. 2 * s)) s"
      unfolding top1_path_product_def comp_def by auto
    \<comment> \<open>h agrees with f \<circ> (2\<cdot>) on A, and that's continuous.\<close>
    show ?thesis
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>s\<in>?A. ?h s \<in> X" using hh_range by auto
    next
      show "\<forall>V\<in>TX. {s \<in> ?A. ?h s \<in> V} \<in> subspace_topology I_set I_top ?A"
      proof
        fix V assume hV: "V \<in> TX"
        have "{s \<in> ?A. ?h s \<in> V} = {s \<in> ?A. (f \<circ> (\<lambda>s. 2 * s)) s \<in> V}"
          using hfunceq by auto
        also have "\<dots> \<in> subspace_topology I_set I_top ?A"
          using hcomp hV unfolding top1_continuous_map_on_def by blast
        finally show "{s \<in> ?A. ?h s \<in> V} \<in> subspace_topology I_set I_top ?A" .
      qed
    qed
  qed
  have hhB: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B) X TX ?h"
  proof -
    have hscale_map: "\<And>s. s \<in> ?B \<Longrightarrow> 2 * s - 1 \<in> I_set"
      unfolding top1_unit_interval_def by auto
    have hscale_cont: "continuous_on UNIV (\<lambda>s :: real. 2 * s - 1)"
      by (intro continuous_intros)
    have hsub_eq: "subspace_topology I_set I_top ?B = subspace_topology UNIV top1_open_sets ?B"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_trans, auto)
    have hItop_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have hscale_raw: "top1_continuous_map_on ?B (subspace_topology UNIV top1_open_sets ?B)
                       I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>s. 2 * s - 1)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hscale_map hscale_cont])
    have hscale: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B)
                   I_set I_top (\<lambda>s. 2 * s - 1)"
      using hscale_raw hsub_eq hItop_eq by simp
    have hcomp: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B) X TX (g \<circ> (\<lambda>s. 2 * s - 1))"
      by (rule top1_continuous_map_on_comp[OF hscale hg])
    have hfunceq: "\<And>s. s \<in> ?B \<Longrightarrow> ?h s = (g \<circ> (\<lambda>s. 2 * s - 1)) s"
    proof -
      fix s :: real assume hs: "s \<in> ?B"
      hence hge: "s \<ge> 1/2" by auto
      show "?h s = (g \<circ> (\<lambda>s. 2 * s - 1)) s"
      proof (cases "s > 1/2")
        case True
        hence "\<not> (s \<le> 1/2)" by simp
        thus ?thesis unfolding top1_path_product_def comp_def by simp
      next
        case False
        hence "s = 1/2" using hge by simp
        hence h2s: "2 * s = 1" and h2sm1: "2 * s - 1 = 0" by simp_all
        show ?thesis unfolding top1_path_product_def comp_def
          using h2s h2sm1 hmatch by simp
      qed
    qed
    show ?thesis
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>s\<in>?B. ?h s \<in> X" using hh_range by auto
    next
      show "\<forall>V\<in>TX. {s \<in> ?B. ?h s \<in> V} \<in> subspace_topology I_set I_top ?B"
      proof
        fix V assume hV: "V \<in> TX"
        have "{s \<in> ?B. ?h s \<in> V} = {s \<in> ?B. (g \<circ> (\<lambda>s. 2 * s - 1)) s \<in> V}"
          using hfunceq by auto
        also have "\<dots> \<in> subspace_topology I_set I_top ?B"
          using hcomp hV unfolding top1_continuous_map_on_def by blast
        finally show "{s \<in> ?B. ?h s \<in> V} \<in> subspace_topology I_set I_top ?B" .
      qed
    qed
  qed
  show ?thesis
    by (rule pasting_lemma_two_closed[OF hTI hTX hA_closed hB_closed hAB hh_range hhA hhB])
qed

lemma top1_path_product_is_path:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
  shows "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hmatch: "f 1 = g 0" using hf1 hg0 by simp
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
    by (rule top1_path_product_continuous[OF hTX hfc hgc hmatch])
  have hstart: "top1_path_product f g 0 = x0"
    unfolding top1_path_product_def using hf0 by simp
  have hend: "top1_path_product f g 1 = x2"
    unfolding top1_path_product_def using hg1 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

text \<open>If two functions agree on S, and one is continuous on S, so is the other.\<close>
lemma top1_continuous_map_on_agree:
  assumes "top1_continuous_map_on S TS Y TY f" and "\<forall>x\<in>S. f x = g x"
  shows "top1_continuous_map_on S TS Y TY g"
proof -
  have "\<forall>x\<in>S. g x \<in> Y" using assms unfolding top1_continuous_map_on_def by auto
  moreover have "\<forall>V\<in>TY. {x \<in> S. g x \<in> V} \<in> TS"
  proof (intro ballI)
    fix V assume "V \<in> TY"
    have "{x \<in> S. g x \<in> V} = {x \<in> S. f x \<in> V}" using assms(2) by auto
    thus "{x \<in> S. g x \<in> V} \<in> TS" using assms(1) \<open>V \<in> TY\<close> unfolding top1_continuous_map_on_def by simp
  qed
  ultimately show ?thesis unfolding top1_continuous_map_on_def by blast
qed

(** from \<S>51 Theorem 51.2: groupoid properties of * **)
lemma Theorem_51_2_associativity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
      and hh: "top1_is_path_on X TX x2 x3 h"
  shows "top1_path_homotopic_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))
    (top1_path_product (top1_path_product f g) h)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hhc: "top1_continuous_map_on I_set I_top X TX h" and hh0: "h 0 = x2" and hh1: "h 1 = x3"
    using hh unfolding top1_is_path_on_def by blast+
  have hfr: "\<forall>s\<in>I_set. f s \<in> X" using hfc unfolding top1_continuous_map_on_def by blast
  have hgr: "\<forall>s\<in>I_set. g s \<in> X" using hgc unfolding top1_continuous_map_on_def by blast
  have hhr: "\<forall>s\<in>I_set. h s \<in> X" using hhc unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) with piecewise linear reparametrization.
     f on [0, (1+t)/4], g on [(1+t)/4, (2+t)/4], h on [(2+t)/4, 1].
     F(s,t) = f(4s/(1+t)) if 4s \<le> 1+t;
              g(4s - 1 - t) if 1+t < 4s \<le> 2+t;
              h((4s - 2 - t)/(2 - t)) if 4s > 2+t.\<close>
  let ?F = "\<lambda>(s::real, t::real).
    if 4*s \<le> 1+t then f (4*s / (1+t))
    else if 4*s \<le> 2+t then g (4*s - 1 - t)
    else h ((4*s - 2 - t) / (2 - t))"
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
      using hp by auto
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" and ht0: "t \<ge> 0" and ht1: "t \<le> 1"
      using hs ht unfolding top1_unit_interval_def by auto
    show "?F p \<in> X"
    proof (cases "4*s \<le> 1+t")
      case True
      have h1t_pos: "1+t > 0" using ht0 by simp
      hence "4*s / (1+t) \<ge> 0" using hs0 by simp
      moreover have "4*s / (1+t) \<le> 1" using True h1t_pos
        by (simp add: divide_le_eq)
      ultimately have "4*s / (1+t) \<in> I_set" unfolding top1_unit_interval_def by simp
      thus ?thesis using hst True hfr by simp
    next
      case False note not1 = this
      show ?thesis
      proof (cases "4*s \<le> 2+t")
        case True
        have "4*s - 1 - t \<ge> 0" using not1 by simp
        moreover have "4*s - 1 - t \<le> 1" using True by simp
        ultimately have "4*s - 1 - t \<in> I_set" unfolding top1_unit_interval_def by simp
        thus ?thesis using hst not1 True hgr by simp
      next
        case False
        have "2 - t > 0" using ht1 by simp
        have "4*s - 2 - t \<ge> 0" using False by simp
        moreover have "4*s - 2 - t \<le> 2 - t" using hs1 by simp
        ultimately have "(4*s - 2 - t) / (2 - t) \<ge> 0" using \<open>2 - t > 0\<close> by simp
        moreover have "(4*s - 2 - t) / (2 - t) \<le> 1"
          using \<open>4*s - 2 - t \<le> 2 - t\<close> \<open>2 - t > 0\<close>
          by (simp add: divide_le_eq_1_pos)
        ultimately have "(4*s - 2 - t) / (2 - t) \<in> I_set" unfolding top1_unit_interval_def by simp
        thus ?thesis using hst not1 False hhr by simp
      qed
    qed
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    \<comment> \<open>Two-level pasting: first paste f,g pieces, then paste with h piece.\<close>
    let ?Cfg = "{(s,t) \<in> I_set \<times> I_set. 4*s \<le> 2+t}"
    let ?Ch = "{(s,t) \<in> I_set \<times> I_set. 4*s \<ge> 2+t}"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>Closedness of Cfg and Ch.\<close>
    have hCfg_closed: "closedin_on (I_set \<times> I_set) II_topology ?Cfg"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Cfg \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Cfg = {(s,t) \<in> I_set \<times> I_set. 4*s > 2+t}" by auto
      also have "\<dots> = (I_set \<times> I_set) \<inter> {p :: real \<times> real. 4 * fst p - snd p > 2}"
        by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {p :: real \<times> real. 4 * fst p - snd p > 2}"
          by (intro open_Collect_less continuous_intros)
        hence "{p :: real \<times> real. 4 * fst p - snd p > 2} \<in> (top1_open_sets :: (real\<times>real) set set)"
          unfolding top1_open_sets_def by blast
        hence "{p :: real \<times> real. 4 * fst p - snd p > 2}
               \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by metis
        thus ?thesis
          unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
      qed
      finally show "I_set \<times> I_set - ?Cfg \<in> II_topology" .
    qed
    have hCh_closed: "closedin_on (I_set \<times> I_set) II_topology ?Ch"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Ch \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Ch = {(s,t) \<in> I_set \<times> I_set. 4*s < 2+t}" by auto
      also have "\<dots> = (I_set \<times> I_set) \<inter> {p :: real \<times> real. 4 * fst p - snd p < 2}"
        by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {p :: real \<times> real. 4 * fst p - snd p < 2}"
          by (intro open_Collect_less continuous_intros)
        hence "{p :: real \<times> real. 4 * fst p - snd p < 2} \<in> (top1_open_sets :: (real\<times>real) set set)"
          unfolding top1_open_sets_def by blast
        hence "{p :: real \<times> real. 4 * fst p - snd p < 2}
               \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by metis
        thus ?thesis
          unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
      qed
      finally show "I_set \<times> I_set - ?Ch \<in> II_topology" .
    qed
    have hcover: "?Cfg \<union> ?Ch = I_set \<times> I_set" by auto
    \<comment> \<open>Continuity of F on Cfg (inner pasting of f and g).\<close>
    have hFcfg: "top1_continuous_map_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg)
                  X TX ?F"
    proof -
      \<comment> \<open>Two clamped reparametrizations.\<close>
      let ?\<rho>f = "\<lambda>p::real\<times>real. max 0 (min 1 (4 * fst p / max 1 (1 + snd p)))"
      let ?\<rho>g = "\<lambda>p::real\<times>real. max 0 (min 1 (4 * fst p - 1 - snd p))"
      have h\<rho>f_cont: "continuous_on (I_set \<times> I_set) ?\<rho>f"
        by (intro continuous_intros continuous_on_divide) auto
      have h\<rho>f_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>f p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hf_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> ?\<rho>f)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>f_map h\<rho>f_cont] hfc])
      have h\<rho>g_cont: "continuous_on (I_set \<times> I_set) ?\<rho>g" by (intro continuous_intros)
      have h\<rho>g_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>g p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hg_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (g \<circ> ?\<rho>g)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>g_map h\<rho>g_cont] hgc])
      \<comment> \<open>Restrict + transfer.\<close>
      let ?Cf = "{(s,t) \<in> I_set \<times> I_set. 4*s \<le> 1+t}"
      let ?Cg = "{(s,t) \<in> I_set \<times> I_set. 4*s \<ge> 1+t \<and> 4*s \<le> 2+t}"
      have hCf_sub: "?Cf \<subseteq> I_set \<times> I_set" by auto
      have hCg_sub: "?Cg \<subseteq> I_set \<times> I_set" by auto
      have hf_agree: "\<forall>p\<in>?Cf. (f \<circ> ?\<rho>f) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Cf"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s: "4*s \<le> 1+t" using hp by auto
        have ht0: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
        have hs0: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
        have "max (1::real) (1 + t) = 1 + t" using ht0 by simp
        moreover have "4*s / (1+t) \<ge> 0" using hs0 ht0 by simp
        moreover have "4*s / (1+t) \<le> 1" using h4s ht0 by (simp add: divide_le_eq)
        ultimately have "?\<rho>f p = 4*s / (1+t)" using hst by auto
        hence lhs: "(f \<circ> ?\<rho>f) p = f (4*s / (1+t))" unfolding comp_def by simp
        have rhs: "?F p = f (4*s / (1+t))" using hst h4s by simp
        show "(f \<circ> ?\<rho>f) p = ?F p" using lhs rhs by metis
      qed
      have hg_agree: "\<forall>p\<in>?Cg. (g \<circ> ?\<rho>g) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Cg"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s_ge: "4*s \<ge> 1+t" and h4s_le: "4*s \<le> 2+t" using hp by auto
        have "4*s - 1 - t \<ge> 0" using h4s_ge by simp
        moreover have "4*s - 1 - t \<le> 1" using h4s_le by simp
        ultimately have "?\<rho>g p = 4*s - 1 - t" using hst by auto
        hence "(g \<circ> ?\<rho>g) p = g (4*s - 1 - t)" by (simp add: comp_def)
        moreover have "?F p = g (4*s - 1 - t)"
        proof (cases "4*s = 1+t")
          case True
          \<comment> \<open>Boundary: both branches give x1.\<close>
          hence "?F p = f (4*s / (1+t))" using hst by simp
          also have "... = f 1"
          proof -
            have "1 + t \<noteq> 0" using ht unfolding top1_unit_interval_def by simp
            thus ?thesis using True by (simp add: divide_simps)
          qed
          also have "... = x1" using hf1 .
          finally have l: "?F p = x1" .
          have "g (4*s - 1 - t) = g 0" using True by simp
          also have "... = x1" using hg0 .
          finally show ?thesis using l by simp
        next
          case False
          hence "4*s > 1+t" using h4s_ge by simp
          hence "\<not>(4*s \<le> 1+t)" by simp
          moreover have "4*s \<le> 2+t" using h4s_le .
          ultimately show ?thesis using hst by simp
        qed
        ultimately show "(g \<circ> ?\<rho>g) p = ?F p" by simp
      qed
      have hF_Cf: "top1_continuous_map_on ?Cf (subspace_topology (I_set \<times> I_set) II_topology ?Cf) X TX ?F"
        by (rule top1_continuous_map_on_agree[OF
             top1_continuous_map_on_restrict_domain_simple[OF hf_comp hCf_sub] hf_agree])
      have hF_Cg: "top1_continuous_map_on ?Cg (subspace_topology (I_set \<times> I_set) II_topology ?Cg) X TX ?F"
        by (rule top1_continuous_map_on_agree[OF
             top1_continuous_map_on_restrict_domain_simple[OF hg_comp hCg_sub] hg_agree])
      \<comment> \<open>Paste Cf and Cg to get Cfg.\<close>
      have "?Cf \<union> ?Cg = ?Cfg" by auto
      \<comment> \<open>Need closedness of Cf, Cg in Cfg subspace, plus the pasting lemma on Cfg.\<close>
      \<comment> \<open>Inner pasting: Cf \<union> Cg = Cfg, closedness in Cfg subspace.\<close>
      have hTcfg: "is_topology_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg)"
        by (rule subspace_topology_is_topology_on[OF hTII]) auto
      have hCf_closed_cfg: "closedin_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?Cf \<subseteq> ?Cfg" by auto
        have "?Cfg - ?Cf = ?Cfg \<inter> {(s,t) \<in> I_set \<times> I_set. 4*s > 1+t}" by auto
        also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg"
        proof -
          have "open {p :: real \<times> real. 4 * fst p - snd p > 1}"
            by (intro open_Collect_less continuous_intros)
          hence "{p :: real \<times> real. 4 * fst p - snd p > 1} \<in> (top1_open_sets :: (real\<times>real) set set)"
            unfolding top1_open_sets_def by blast
          hence "{p :: real \<times> real. 4 * fst p - snd p > 1}
                 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            using product_topology_on_open_sets_real2 by metis
          hence "(I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p > 1} \<in> II_topology"
            unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
          moreover have "{(s,t) \<in> I_set \<times> I_set. 4*s > 1+t} = (I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p > 1}"
            by auto
          ultimately have "{(s,t) \<in> I_set \<times> I_set. 4*s > 1+t} \<in> II_topology" by simp
          thus ?thesis unfolding subspace_topology_def by blast
        qed
        finally show "?Cfg - ?Cf \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg" .
      qed
      have hCg_closed_cfg: "closedin_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?Cg \<subseteq> ?Cfg" by auto
        have "?Cfg - ?Cg = {(s,t) \<in> I_set \<times> I_set. 4*s < 1+t}" by auto
        also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg"
        proof -
          have "open {p :: real \<times> real. 4 * fst p - snd p < 1}"
            by (intro open_Collect_less continuous_intros)
          hence "{p :: real \<times> real. 4 * fst p - snd p < 1} \<in> (top1_open_sets :: (real\<times>real) set set)"
            unfolding top1_open_sets_def by blast
          hence "{p :: real \<times> real. 4 * fst p - snd p < 1}
                 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            using product_topology_on_open_sets_real2 by metis
          hence "(I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p < 1} \<in> II_topology"
            unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
          moreover have "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} = (I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p < 1}"
            by auto
          ultimately have hopen_II: "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} \<in> II_topology" by simp
          have "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} = ?Cfg \<inter> {(s,t) \<in> I_set \<times> I_set. 4*s < 1+t}"
            by auto
          thus ?thesis unfolding subspace_topology_def using hopen_II by blast
        qed
        finally show "?Cfg - ?Cg \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg" .
      qed
      have hCfCg_cover: "?Cf \<union> ?Cg = ?Cfg" by auto
      have hF_range_cfg: "\<forall>p\<in>?Cfg. ?F p \<in> X" using hF_range by auto
      \<comment> \<open>Need continuity of ?F on subspace of Cfg from Cf and Cg subspaces.\<close>
      have hCf_sub_Cfg: "?Cf \<subseteq> ?Cfg" by auto
      have hCg_sub_Cfg: "?Cg \<subseteq> ?Cfg" by auto
      have htrans_Cf: "subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf
                      = subspace_topology (I_set \<times> I_set) II_topology ?Cf"
        by (rule subspace_topology_trans[OF hCf_sub_Cfg])
      have htrans_Cg: "subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg
                      = subspace_topology (I_set \<times> I_set) II_topology ?Cg"
        by (rule subspace_topology_trans[OF hCg_sub_Cfg])
      have hF_Cf_cfg: "top1_continuous_map_on ?Cf (subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf)
                        X TX ?F"
        using hF_Cf unfolding htrans_Cf .
      have hF_Cg_cfg: "top1_continuous_map_on ?Cg (subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg)
                        X TX ?F"
        using hF_Cg unfolding htrans_Cg .
      show ?thesis
        by (rule pasting_lemma_two_closed[OF hTcfg hTX hCf_closed_cfg hCg_closed_cfg hCfCg_cover hF_range_cfg hF_Cf_cfg hF_Cg_cfg])
    qed
    \<comment> \<open>Continuity of F on Ch: h((4s-2-t)/(2-t)).\<close>
    have hFch: "top1_continuous_map_on ?Ch (subspace_topology (I_set \<times> I_set) II_topology ?Ch)
                 X TX ?F"
    proof -
      let ?\<rho> = "\<lambda>p::real\<times>real. max 0 (min 1 ((4 * fst p - 2 - snd p) / (2 - snd p)))"
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>"
        by (intro continuous_intros continuous_on_divide) (auto simp: top1_unit_interval_def)
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho> p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhc])
      \<comment> \<open>Restrict to Ch.\<close>
      have hCh_sub: "?Ch \<subseteq> I_set \<times> I_set" by auto
      have hcomp_restrict: "top1_continuous_map_on ?Ch (subspace_topology (I_set \<times> I_set) II_topology ?Ch)
                             X TX (h \<circ> ?\<rho>)"
        using top1_continuous_map_on_restrict_domain_simple[OF hcomp hCh_sub] .
      \<comment> \<open>h \<circ> \<rho> agrees with ?F on Ch.\<close>
      have hagree: "\<forall>p\<in>?Ch. (h \<circ> ?\<rho>) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Ch"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s: "4*s \<ge> 2+t" using hp by auto
        have hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
        have ht0: "t \<ge> 0" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
        have h2t: "2 - t > 0" using ht1 by simp
        have hnn: "(4*s - 2 - t) \<ge> 0" using h4s by simp
        have hle: "(4*s - 2 - t) \<le> 2 - t" using hs1 by linarith
        hence hrho_val: "?\<rho> p = (4*s - 2 - t) / (2 - t)" using hst hnn hle h2t
          by (simp add: divide_le_eq)
        show "(h \<circ> ?\<rho>) p = ?F p"
        proof (cases "4*s = 2+t")
          case True
          hence "?\<rho> p = 0" using hst by simp
          hence lhs: "(h \<circ> ?\<rho>) p = h 0" by (simp add: comp_def)
          have "4*s > 1+t" using h4s ht0 by linarith
          hence "\<not>(4*s \<le> 1+t)" by simp
          hence "?F p = g (4*s - 1 - t)" using hst True by simp
          also have "... = g 1" using True by simp
          also have "... = x2" using hg1 .
          finally have rhs: "?F p = x2" .
          show ?thesis using lhs rhs hh0 by simp
        next
          case False
          hence h4s_gt: "4*s > 2+t" using h4s by simp
          hence "\<not>(4*s \<le> 1+t)" and "\<not>(4*s \<le> 2+t)" by auto
          hence "?F p = h ((4*s - 2 - t) / (2 - t))" using hst by simp
          thus ?thesis using hrho_val hst by (simp add: comp_def)
        qed
      qed
      show ?thesis by (rule top1_continuous_map_on_agree[OF hcomp_restrict hagree])
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hCfg_closed hCh_closed hcover hF_range hFcfg hFch])
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product (top1_path_product f g) h s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 0) = top1_path_product (top1_path_product f g) h s"
    proof (cases "s \<le> 1/2")
      case True \<comment> \<open>(f*g)*h maps to (f*g)(2s)\<close>
      show ?thesis
      proof (cases "s \<le> 1/4")
        case True2: True \<comment> \<open>(f*g)(2s) = f(4s) since 2s \<le> 1/2\<close>
        have "4*s \<le> 1+0" using True2 by simp
        hence lhs: "?F (s, 0) = f (4*s / 1)" by simp
        have "top1_path_product (top1_path_product f g) h s
            = top1_path_product f g (2*s)" using True unfolding top1_path_product_def by simp
        also have "... = f (2*(2*s))" using True2 unfolding top1_path_product_def by simp
        also have "... = f (4*s)" by simp
        finally show ?thesis using lhs by simp
      next
        case False2: False \<comment> \<open>(f*g)(2s) = g(4s-1) since 2s > 1/2\<close>
        hence "s > 1/4" by simp
        hence "4*s > 1" by simp
        moreover have "4*s \<le> 2" using True by simp
        ultimately have lhs: "?F (s, 0) = g (4*s - 1 - 0)" by simp
        have "top1_path_product (top1_path_product f g) h s
            = top1_path_product f g (2*s)" using True unfolding top1_path_product_def by simp
        also have "... = g (2*(2*s) - 1)" using False2 unfolding top1_path_product_def by auto
        also have "... = g (4*s - 1)" by simp
        finally show ?thesis using lhs by simp
      qed
    next
      case False \<comment> \<open>(f*g)*h maps to h(2s-1)\<close>
      hence "s > 1/2" by simp
      hence "4*s > 2" by simp
      hence h4s_gt: "\<not> (4*s \<le> 1 + (0::real))" and h4s_gt2: "\<not> (4*s \<le> 2 + (0::real))" by auto
      have harith: "(4*s - 2) / (2::real) = 2*s - 1" by auto
      have "?F (s, 0) = h ((4*s - 2) / 2)"
        using h4s_gt h4s_gt2 by simp
      hence lhs: "?F (s, 0) = h (2*s - 1)" using harith by presburger
      have "top1_path_product (top1_path_product f g) h s = h (2*s - 1)"
        using False unfolding top1_path_product_def by auto
      thus ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = top1_path_product f (top1_path_product g h) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 1) = top1_path_product f (top1_path_product g h) s"
    proof (cases "s \<le> 1/2")
      case True
      have "4*s \<le> 1 + (1::real)" using True by simp
      hence lhs: "?F (s, 1) = f (4*s / (1+1))" by simp
      have "top1_path_product f (top1_path_product g h) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      moreover have "4*s / 2 = 2*s" by simp
      ultimately show ?thesis using lhs by simp
    next
      case False
      hence "s > 1/2" by simp
      show ?thesis
      proof (cases "s \<le> 3/4")
        case True2: True
        have "4*s > 2" using \<open>s > 1/2\<close> by simp
        moreover have "4*s \<le> 2 + (1::real)" using True2 by simp
        ultimately have lhs: "?F (s, 1) = g (4*s - 1 - 1)" by simp
        have "top1_path_product f (top1_path_product g h) s
            = top1_path_product g h (2*s - 1)"
          using False unfolding top1_path_product_def by auto
        also have "... = g (2*(2*s - 1))" using True2 \<open>s > 1/2\<close>
          unfolding top1_path_product_def by auto
        also have "... = g (4*s - 2)" by simp
        finally show ?thesis using lhs by simp
      next
        case False2: False
        hence "s > 3/4" by simp
        have "4*s > 3" using \<open>s > 3/4\<close> by simp
        hence lhs: "?F (s, 1) = h ((4*s - 2 - 1) / (2 - 1))" by simp
        have "top1_path_product f (top1_path_product g h) s
            = top1_path_product g h (2*s - 1)"
          using False unfolding top1_path_product_def by auto
        also have "... = h (2*(2*s - 1) - 1)" using False2
          unfolding top1_path_product_def by auto
        also have "... = h (4*s - 3)" by simp
        finally have rhs: "top1_path_product f (top1_path_product g h) s = h (4*s - 3)" .
        have "(4*s - 3) / 1 = 4*s - 3" by simp
        thus ?thesis using lhs rhs by simp
      qed
    qed
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "4*(0::real) \<le> 1+t" using ht unfolding top1_unit_interval_def by simp
    hence "?F (0, t) = f (0 / (1+t))" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x3"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    have "4*(1::real) = 4" by simp
    moreover have "2 + t \<le> 3" using ht1 by simp
    hence "4 > 2 + t" by simp
    ultimately have lhs: "?F (1, t) = h ((4 - 2 - t) / (2 - t))" by simp
    have "2 - t > 0" using ht1 by simp
    hence "(2 - t) / (2 - t) = 1" by simp
    thus "?F (1, t) = x3" using lhs hh1 by simp
  qed
  have hgh: "top1_is_path_on X TX x1 x3 (top1_path_product g h)"
    by (rule top1_path_product_is_path[OF hTX hg hh])
  have hfg: "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX hf hg])
  have hpath_lhs: "top1_is_path_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))"
    by (rule top1_path_product_is_path[OF hTX hf hgh])
  have hpath_rhs: "top1_is_path_on X TX x0 x3
    (top1_path_product (top1_path_product f g) h)"
    by (rule top1_path_product_is_path[OF hTX hfg hh])
  \<comment> \<open>Our F goes from (f*g)*h to f*(g*h), but the goal is the reverse.
      Use symmetry of path homotopy.\<close>
  have hrev: "top1_path_homotopic_on X TX x0 x3
    (top1_path_product (top1_path_product f g) h)
    (top1_path_product f (top1_path_product g h))"
    unfolding top1_path_homotopic_on_def
    using hpath_rhs hpath_lhs hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
  show ?thesis by (rule Lemma_51_1_path_homotopic_sym[OF hrev])
qed

lemma Theorem_51_2_left_identity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) f) f"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(max(0, (2s - 1 + t)/(1 + t))).
     At t=0: s \<le> 1/2 gives max(0, (2s-1)/1) = max(0, 2s-1) = 0, so F=f(0)=x0.
             s \<ge> 1/2 gives f(2s-1) = (e * f)(s). So F(\<cdot>,0) = e * f.
     At t=1: max(0, (2s)/2) = max(0, s) = s for s\<ge>0. So F(\<cdot>,1) = f.
     At s=0: max(0, (-1+t)/(1+t)). For t\<in>[0,1], -1+t \<le> 0, so max=0, F=f(0)=x0.
     At s=1: max(0, (1+t)/(1+t)) = max(0, 1) = 1, so F=f(1)=x1.\<close>
  let ?g = "\<lambda>(s::real, t::real). max 0 (min 1 ((2*s - 1 + t) / (1 + t)))"
  let ?F = "\<lambda>p. f (?g p)"
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have h1t_pos: "\<And>s t. (s, t) \<in> I_set \<times> I_set \<Longrightarrow> 1 + t > 0"
        unfolding top1_unit_interval_def by auto
      have hnum: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p - 1 + snd p)"
        by (intro continuous_intros)
      have hden: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 + snd p)"
        by (intro continuous_intros)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. (2 * fst p - 1 + snd p) / (1 + snd p))"
        by (rule continuous_on_divide[OF hnum hden])
           (auto simp: top1_unit_interval_def)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>(s, t). (2*s - 1 + t) / (1 + t))"
        by (simp add: case_prod_unfold)
      hence hmin: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min 1 ((2 * fst p - 1 + snd p) / (1 + snd p)))"
        by (intro continuous_on_min continuous_on_const) (simp add: case_prod_unfold)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (min 1 ((2 * fst p - 1 + snd p) / (1 + snd p))))"
        by (intro continuous_on_max continuous_on_const hmin)
      thus ?thesis by (simp add: case_prod_unfold)
    qed
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
    proof -
      have hmap: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?g p \<in> I_set" using hg_range by auto
      show ?thesis by (rule top1_continuous_map_on_II_to_I[OF hmap hg_cont])
    qed
    have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> ?g)"
      unfolding II_topology_def by (rule top1_continuous_map_on_comp[OF hg_top1 hfcont])
    moreover have "\<forall>p\<in>I_set \<times> I_set. (f \<circ> ?g) p = ?F p" by (auto simp: comp_def)
    ultimately show ?thesis
      unfolding top1_continuous_map_on_def II_topology_def
      using hF_range by auto
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product (top1_constant_path x0) f s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?F (s, 0) = top1_path_product (top1_constant_path x0) f s"
    proof (cases "s \<le> 1/2")
      case True
      hence "2*s - 1 + 0 = 2*s - 1" by simp
      hence "(2*s - 1) / (1 + 0) = 2*s - 1" by simp
      moreover have "2*s - 1 \<le> 0" using True by simp
      ultimately have "?g (s, 0) = 0"
        using hs unfolding top1_unit_interval_def by auto
      hence "?F (s, 0) = f 0" by simp
      also have "... = x0" using hf0 by simp
      finally have lhs: "?F (s, 0) = x0" .
      have "top1_path_product (top1_constant_path x0) f s = top1_constant_path x0 (2 * s)"
        using True unfolding top1_path_product_def by simp
      also have "... = x0" unfolding top1_constant_path_def by simp
      finally have rhs: "top1_path_product (top1_constant_path x0) f s = x0" .
      show ?thesis using lhs rhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      hence "2*s - 1 > 0" by simp
      hence "(2*s - 1) / 1 = 2*s - 1" by simp
      moreover have "2*s - 1 \<ge> 0" using hge by simp
      moreover have "2*s - 1 \<le> 1" using hs unfolding top1_unit_interval_def by auto
      ultimately have "?g (s, 0) = 2*s - 1" using hs unfolding top1_unit_interval_def by auto
      hence h_Fs0: "?F (s, 0) = f (2*s - 1)" by simp
      have "top1_path_product (top1_constant_path x0) f s = f (2*s - 1)"
        using hge unfolding top1_path_product_def top1_constant_path_def by auto
      thus ?thesis using h_Fs0 by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "(2*s - 1 + 1) / (1 + 1) = s" by auto
    moreover have "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
    moreover have "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
    ultimately have "?g (s, 1) = s" by auto
    thus "?F (s, 1) = f s" by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*0 - 1 + t) / (1 + t) = (t - 1) / (1 + t)" by simp
    moreover have "t - 1 \<le> 0" using ht unfolding top1_unit_interval_def by simp
    moreover have "1 + t > 0" using ht unfolding top1_unit_interval_def by simp
    ultimately have "(t - 1) / (1 + t) \<le> 0" by (simp add: divide_nonpos_nonneg)
    hence "?g (0, t) = 0" by auto
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x1"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*1 - 1 + t) / (1 + t) = (1 + t) / (1 + t)" by simp
    moreover have "1 + t > 0" using ht unfolding top1_unit_interval_def by simp
    ultimately have "(1 + t) / (1 + t) = 1" by simp
    hence "?g (1, t) = 1" by auto
    hence "?F (1, t) = f 1" by simp
    thus "?F (1, t) = x1" using hf1 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx0X: "x0 \<in> X" using hfrange h0I hf0 by force
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  have hpath_ef: "top1_is_path_on X TX x0 x1 (top1_path_product (top1_constant_path x0) f)"
    by (rule top1_path_product_is_path[OF hTX hconst hf])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_ef hf hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_right_identity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_constant_path x1)) f"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(min(1, 2s/(2-t))).
     At t=0: s < 1/2 gives f(2s/2) = f(s); s = 1/2 gives f(1); s > 1/2 gives f(min(1, 2s/2)).
     Wait — use F(s,t) = f(min(1, (2s)/(1+t))).
     At t=0: min(1, 2s) — for s \<le> 1/2, f(2s); for s \<ge> 1/2, f(1) = x1.
             So F(\<cdot>, 0) = f * e_{x1}.
     At t=1: min(1, s) = s (for s \<in> [0,1]). So F(\<cdot>, 1) = f.
     At s=0: min(1, 0) = 0. F(0,t) = f(0) = x0.
     At s=1: min(1, 2/(1+t)). Since 1+t \<ge> 1, 2/(1+t) \<le> 2. Also 1+t \<le> 2, so 2/(1+t) \<ge> 1.
             So min(1, 2/(1+t)) = 1. F(1,t) = f(1) = x1.\<close>
  let ?g = "\<lambda>(s::real, t::real). min 1 (max 0 ((2*s) / (1 + t)))"
  let ?F = "\<lambda>p. f (?g p)"
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have hnum: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p)"
        by (intro continuous_intros)
      have hden: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 + snd p)"
        by (intro continuous_intros)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. (2 * fst p) / (1 + snd p))"
        by (rule continuous_on_divide[OF hnum hden])
           (auto simp: top1_unit_interval_def)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (2 * fst p / (1 + snd p)))"
        by (intro continuous_on_max continuous_on_const)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min 1 (max 0 (2 * fst p / (1 + snd p))))"
        by (intro continuous_on_min continuous_on_const)
      thus ?thesis by (simp add: case_prod_unfold)
    qed
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
      by (rule top1_continuous_map_on_II_to_I) (use hg_range in auto, rule hg_cont)
    have "f \<circ> ?g = ?F" by (rule ext) (simp add: comp_def case_prod_unfold)
    hence hcomp: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX ?F"
      using top1_continuous_map_on_comp[OF hg_top1 hfcont] by simp
    show ?thesis unfolding II_topology_def using hcomp .
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product f (top1_constant_path x1) s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?F (s, 0) = top1_path_product f (top1_constant_path x1) s"
    proof (cases "s \<le> 1/2")
      case True
      have hs_nn: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
      have "2*s / (1 + 0) = 2*s" by simp
      moreover have "2*s \<ge> 0" using hs_nn by simp
      moreover have "2*s \<le> 1" using True by simp
      ultimately have "?g (s, 0) = 2*s" by auto
      hence lhs: "?F (s, 0) = f (2*s)" by simp
      have "top1_path_product f (top1_constant_path x1) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      thus ?thesis using lhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      have "2*s > 1" using hge by simp
      hence "2*s / 1 > 1" by simp
      hence "?g (s, 0) = 1" by auto
      hence lhs: "?F (s, 0) = f 1" by simp
      have "top1_path_product f (top1_constant_path x1) s = top1_constant_path x1 (2*s - 1)"
        using hge unfolding top1_path_product_def by auto
      also have "... = x1" unfolding top1_constant_path_def by simp
      also have "... = f 1" using hf1 by simp
      finally show ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs_nn: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
    have hs_le1: "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
    have "(2*s) / (1 + 1) = s" by auto
    moreover have "s \<le> 1" using hs_le1 .
    moreover have "s \<ge> 0" using hs_nn .
    ultimately have "?g (s, 1) = s" by auto
    thus "?F (s, 1) = f s" by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*0) / (1 + t) = 0" by simp
    hence "?g (0, t) = 0" by simp
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x1"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht_nn: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
    have "1 + t > 0" using ht_nn by simp
    moreover have "2 / (1 + t) \<ge> 1" using ht unfolding top1_unit_interval_def
      by (simp add: le_divide_eq)
    ultimately have "?g (1, t) = 1" by auto
    hence "?F (1, t) = f 1" by simp
    thus "?F (1, t) = x1" using hf1 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx1X: "x1 \<in> X" using hfrange h1I hf1 by force
  have hconst: "top1_is_path_on X TX x1 x1 (top1_constant_path x1)"
    by (rule top1_constant_path_is_path[OF hTX hx1X])
  have hpath_fe: "top1_is_path_on X TX x0 x1 (top1_path_product f (top1_constant_path x1))"
    by (rule top1_path_product_is_path[OF hTX hf hconst])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_fe hf hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_invgerse_left:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x0
    (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(max(0, min(2s, min(2-2s, 1-t)))).
     At t=0: max(0, min(2s, min(2-2s, 1))) = max(0, min(2s, 2-2s)).
             For s \<le> 1/2: min(2s, 2-2s) = 2s, F = f(2s) = (f*f^{-1})(s) piece 1.
             For s \<ge> 1/2: min(2s, 2-2s) = 2-2s, F = f(2-2s) = (f*f^{-1})(s) piece 2.
     At t=1: max(0, min(2s, min(2-2s, 0))) = max(0, 0) = 0, F = f(0) = x0.
     At s=0: max(0, min(0, min(2, 1-t))) = 0, F = f(0) = x0.
     At s=1: max(0, min(2, min(0, 1-t))) = 0, F = f(0) = x0.\<close>
  let ?g = "\<lambda>(s::real, t::real). max 0 (min (2*s) (min (2 - 2*s) (1 - t)))"
  let ?F = "\<lambda>p. f (?g p)"
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have h2s: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p)" by (intro continuous_intros)
      have h22s: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 - 2 * fst p)" by (intro continuous_intros)
      have h1t: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 - snd p)" by (intro continuous_intros)
      have hmin1: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min (2 - 2 * fst p) (1 - snd p))"
        by (intro continuous_on_min h22s h1t)
      have hmin2: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min (2 * fst p) (min (2 - 2 * fst p) (1 - snd p)))"
        by (intro continuous_on_min h2s hmin1)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (min (2 * fst p) (min (2 - 2 * fst p) (1 - snd p))))"
        by (intro continuous_on_max continuous_on_const hmin2)
      thus ?thesis by (simp add: case_prod_unfold)
    qed
    have hg_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?g p \<in> I_set" using hg_range by auto
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
      by (rule top1_continuous_map_on_II_to_I[OF hg_map hg_cont])
    have hcomp_raw: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (f \<circ> ?g)"
      by (rule top1_continuous_map_on_comp[OF hg_top1 hfcont])
    show ?thesis unfolding II_topology_def
      by (rule top1_continuous_map_on_agree[OF hcomp_raw])
         (auto simp: comp_def case_prod_unfold)
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product f (top1_path_reverse f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs_nn: "s \<ge> 0" and hs_le1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 0) = top1_path_product f (top1_path_reverse f) s"
    proof (cases "s \<le> 1/2")
      case True
      have "min (2*s) (min (2 - 2*s) (1 - 0)) = 2*s" using True hs_nn by auto
      hence "?g (s, 0) = 2*s" using hs_nn by auto
      hence lhs: "?F (s, 0) = f (2*s)" by simp
      have "top1_path_product f (top1_path_reverse f) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      thus ?thesis using lhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      have "min (2*s) (min (2 - 2*s) 1) = 2 - 2*s" using hge hs_le1 by auto
      moreover have "2 - 2*s \<ge> 0" using hs_le1 by simp
      ultimately have "?g (s, 0) = 2 - 2*s" by auto
      hence lhs: "?F (s, 0) = f (2 - 2*s)" by simp
      have "top1_path_product f (top1_path_reverse f) s = top1_path_reverse f (2*s - 1)"
        using hge unfolding top1_path_product_def by auto
      also have "... = f (1 - (2*s - 1))" unfolding top1_path_reverse_def by simp
      also have "... = f (2 - 2*s)" by simp
      finally show ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = top1_constant_path x0 s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "min (2*s) (min (2 - 2*s) (1 - 1)) = 0"
      using hs unfolding top1_unit_interval_def by auto
    hence "?g (s, 1) = 0" by auto
    hence "?F (s, 1) = f 0" by simp
    thus "?F (s, 1) = top1_constant_path x0 s" using hf0 unfolding top1_constant_path_def by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "?g (0, t) = 0" by simp
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "min (2*1) (min (2 - 2*1) (1 - t)) = 0"
      using ht unfolding top1_unit_interval_def by auto
    hence "?g (1, t) = 0" by auto
    hence "?F (1, t) = f 0" by simp
    thus "?F (1, t) = x0" using hf0 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx0X: "x0 \<in> X" using hfrange h0I hf0 by force
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have hpath_frev: "top1_is_path_on X TX x0 x0 (top1_path_product f (top1_path_reverse f))"
    by (rule top1_path_product_is_path[OF hTX hf hrev])
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_frev hconst hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_invgerse_right:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
proof -
  \<comment> \<open>By symmetry: apply invgerse_left to the reversed path f^{-1}: x1 \<rightarrow> x0.\<close>
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) (top1_path_reverse (top1_path_reverse f)))
    (top1_constant_path x1)"
    by (rule Theorem_51_2_invgerse_left[OF hTX hrev])
  moreover have "top1_path_reverse (top1_path_reverse f) = f"
    by (rule top1_path_reverse_twice)
  ultimately show ?thesis by simp
qed

section \<open>\<S>52 The Fundamental Group\<close>

text \<open>A loop at x0: a path starting and ending at x0.\<close>
definition top1_is_loop_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_loop_on X TX x0 f \<longleftrightarrow> top1_is_path_on X TX x0 x0 f"

lemma top1_is_loop_on_continuous:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> top1_continuous_map_on I_set I_top X TX f"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_is_loop_on_start:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> f 0 = x0"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_is_loop_on_end:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> f 1 = x0"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_constant_path_is_loop:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_is_loop_on X TX x (top1_constant_path x)"
  unfolding top1_is_loop_on_def using top1_constant_path_is_path[OF assms] .

text \<open>Product of loops at x0 is a loop at x0.\<close>
lemma top1_path_product_is_loop:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_loop_on X TX x0 f" and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_is_loop_on X TX x0 (top1_path_product f g)"
proof -
  have "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  moreover have "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
  ultimately have "top1_is_path_on X TX x0 x0 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX])
  thus ?thesis unfolding top1_is_loop_on_def .
qed

text \<open>Reverse of a loop is a loop at the same basepoint.\<close>
lemma top1_path_reverse_is_loop:
  assumes hf: "top1_is_loop_on X TX x0 f"
  shows "top1_is_loop_on X TX x0 (top1_path_reverse f)"
proof -
  have "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  hence "top1_is_path_on X TX x0 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path)
  thus ?thesis unfolding top1_is_loop_on_def .
qed

text \<open>The path-homotopy equivalence class of a loop is the same as
  path-homotopy equivalence restricted to loops at x0.\<close>
definition top1_loop_equiv_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_loop_equiv_on X TX x0 f g \<longleftrightarrow>
     top1_is_loop_on X TX x0 f \<and> top1_is_loop_on X TX x0 g
     \<and> top1_path_homotopic_on X TX x0 x0 f g"

lemma top1_loop_equiv_on_refl:
  assumes "top1_is_loop_on X TX x0 f"
  shows "top1_loop_equiv_on X TX x0 f f"
  unfolding top1_loop_equiv_on_def
  using assms Lemma_51_1_path_homotopic_refl[of X TX x0 x0 f]
  unfolding top1_is_loop_on_def by blast

lemma top1_loop_equiv_on_sym:
  assumes "top1_loop_equiv_on X TX x0 f g"
  shows "top1_loop_equiv_on X TX x0 g f"
  using assms Lemma_51_1_path_homotopic_sym[of X TX x0 x0 f g]
  unfolding top1_loop_equiv_on_def by blast

lemma top1_loop_equiv_on_trans:
  assumes hTX: "is_topology_on X TX"
      and "top1_loop_equiv_on X TX x0 f g"
      and "top1_loop_equiv_on X TX x0 g h"
  shows "top1_loop_equiv_on X TX x0 f h"
  using assms Lemma_51_1_path_homotopic_trans[OF hTX, of x0 x0 f g h]
  unfolding top1_loop_equiv_on_def by blast

text \<open>The set of loops at x0 modulo path homotopy — the carrier of pi_1(X, x0).
  Represented as equivalence classes of loops.\<close>
definition top1_fundamental_group_carrier :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) set set" where
  "top1_fundamental_group_carrier X TX x0 =
     { {g. top1_loop_equiv_on X TX x0 f g} | f. top1_is_loop_on X TX x0 f }"

text \<open>Group operation on \<pi>_1(X, x_0): [f] * [g] = [f * g] (path concatenation).
  Well-defined on equivalence classes via Theorem 51.2 operations.\<close>
definition top1_fundamental_group_mul ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow>
   (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_mul X TX x0 c1 c2 =
     {h. \<exists>f\<in>c1. \<exists>g\<in>c2. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"

text \<open>Identity element of \<pi>_1(X, x_0): the equivalence class of the constant loop.\<close>
definition top1_fundamental_group_id ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_id X TX x0 =
     {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"

text \<open>Inverse in \<pi>_1(X, x_0): [f] \<rightarrow> [reverse f].\<close>
definition top1_fundamental_group_invg ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_invg X TX x0 c =
     {h. \<exists>f\<in>c. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"

text \<open>The induced homomorphism on \<pi>_1: for continuous h: (X, x_0) \<rightarrow> (Y, y_0),
  h_*([f]) = [h \<circ> f]. This sends an equivalence class to the class containing h \<circ> f.\<close>
definition top1_fundamental_group_induced_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> 'b
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'b) set" where
  "top1_fundamental_group_induced_on X TX x0 Y TY y0 h c =
     {g. \<exists>f\<in>c. top1_loop_equiv_on Y TY y0 (h \<circ> f) g}"

text \<open>The image subgroup h_*(\<pi>_1(X, x_0)) \<subseteq> \<pi>_1(Y, y_0).\<close>
definition top1_fundamental_group_image_hom ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> 'b
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b) set set" where
  "top1_fundamental_group_image_hom X TX x0 Y TY y0 h =
     (top1_fundamental_group_induced_on X TX x0 Y TY y0 h) `
       (top1_fundamental_group_carrier X TX x0)"

text \<open>Simply connected: path-connected with trivial fundamental group.
  We keep the base definition polymorphic; a strict version is given below.\<close>
definition top1_simply_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_simply_connected_on X TX \<longleftrightarrow>
     top1_path_connected_on X TX \<and>
     (\<forall>x0\<in>X. \<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
        top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0))"

text \<open>Strict version: simply connected in a strict topology.\<close>
definition top1_simply_connected_strict :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_simply_connected_strict X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and> top1_simply_connected_on X TX"

lemma top1_simply_connected_strict_imp:
  "top1_simply_connected_strict X TX \<Longrightarrow> top1_simply_connected_on X TX"
  unfolding top1_simply_connected_strict_def by blast

lemma top1_simply_connected_strict_is_topology_strict:
  "top1_simply_connected_strict X TX \<Longrightarrow> is_topology_on_strict X TX"
  unfolding top1_simply_connected_strict_def by blast

lemma top1_simply_connected_on_path_connected:
  "top1_simply_connected_on X TX \<Longrightarrow> top1_path_connected_on X TX"
  unfolding top1_simply_connected_on_def by blast


text \<open>The fundamental group operation: [f]*[g] = [f*g] on equivalence classes.
  Well-defined by Theorem 51.2.\<close>

text \<open>Homomorphism induced by a continuous map h: (X, x0) \<rightarrow> (Y, y0).\<close>
definition top1_induced_homomorphism_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'b)" where
  "top1_induced_homomorphism_on X TX Y TY h f = h \<circ> f"

text \<open>Congruence: path homotopy is compatible with path product (left and right).\<close>
lemma path_homotopic_product_left:
  assumes hTX: "is_topology_on X TX"
      and hfg: "top1_path_homotopic_on X TX x0 x1 f g"
      and hh: "top1_is_path_on X TX x1 x2 h"
  shows "top1_path_homotopic_on X TX x0 x2 (top1_path_product f h) (top1_path_product g h)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x0" and hF1: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hh0: "h 0 = x1" and hh1: "h 1 = x2"
    using hh unfolding top1_is_path_on_def by blast+
  have hhcont: "top1_continuous_map_on I_set I_top X TX h"
    using hh unfolding top1_is_path_on_def by blast
  \<comment> \<open>Define G(s,t) = if s \<le> 1/2 then F(2s, t) else h(2s-1).\<close>
  let ?G = "\<lambda>p::real\<times>real. if fst p \<le> 1/2 then F (2 * fst p, snd p) else h (2 * fst p - 1)"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    let ?As = "{s\<in>I_set. s \<le> 1/2} \<times> I_set"
    let ?Bs = "{s\<in>I_set. s \<ge> 1/2} \<times> I_set"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>Reparametrization (2s, t) continuous from As to I\<times>I.\<close>
    have h\<phi>: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As)
               (I_set \<times> I_set) II_topology (\<lambda>p. (2 * fst p, snd (p::real\<times>real)))"
    proof -
      have hcont: "continuous_on UNIV (\<lambda>p::real\<times>real. (2 * fst p, snd p))" by (intro continuous_intros)
      have hmap: "\<And>p. p \<in> ?As \<Longrightarrow> (2 * fst p, snd p) \<in> I_set \<times> I_set"
        unfolding top1_unit_interval_def by auto
      have hAs_sub: "?As \<subseteq> I_set \<times> I_set" by auto
      have hraw: "top1_continuous_map_on ?As
                   (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?As)
                   (I_set \<times> I_set) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                   (\<lambda>p. (2 * fst p, snd p))"
        by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
      have hdom: "subspace_topology (I_set \<times> I_set) II_topology ?As
                = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?As"
        unfolding II_topology_def using subspace_topology_trans[OF hAs_sub] II_topology_eq_subspace by simp
      have hcod: "II_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
        unfolding II_topology_def by (rule II_topology_eq_subspace)
      show ?thesis using hraw hdom hcod by simp
    qed
    have hFAs: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX
                 (\<lambda>p. F (2 * fst p, snd p))"
    proof -
      have "F \<circ> (\<lambda>p. (2 * fst p, snd p)) = (\<lambda>p. F (2 * fst p, snd p))" by (rule ext) simp
      thus ?thesis using top1_continuous_map_on_comp[OF h\<phi> hF] by simp
    qed
    \<comment> \<open>h(2s-1) continuous on Bs.\<close>
    have hHBs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX
                 (\<lambda>p. h (2 * fst p - 1))"
    proof -
      let ?\<rho>h = "\<lambda>p::real\<times>real. max 0 (min 1 (2 * fst p - 1))"
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>h" by (intro continuous_intros)
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>h p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>h)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhcont])
      have hBs_sub: "?Bs \<subseteq> I_set \<times> I_set" by auto
      have hrestr: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX (h \<circ> ?\<rho>h)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hcomp hBs_sub])
      have hagree: "\<forall>p\<in>?Bs. (h \<circ> ?\<rho>h) p = h (2 * fst p - 1)"
      proof
        fix p assume hp: "p \<in> ?Bs"
        have "fst p \<ge> 1/2" using hp by auto
        hence "2 * fst p - 1 \<ge> 0" by simp
        moreover have "fst p \<le> 1" using hp unfolding top1_unit_interval_def by auto
        hence "2 * fst p - 1 \<le> 1" by simp
        ultimately show "(h \<circ> ?\<rho>h) p = h (2 * fst p - 1)" by (simp add: comp_def)
      qed
      show ?thesis by (rule top1_continuous_map_on_agree[OF hrestr hagree])
    qed
    \<comment> \<open>Agreement of ?G with piece functions.\<close>
    have hG_As: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hFAs])
      show "\<forall>p\<in>?As. F (2 * fst p, snd p) = ?G p"
      proof
        fix p assume "p \<in> ?As"
        hence "fst p \<le> 1/2" by auto
        thus "F (2 * fst p, snd p) = ?G p" by simp
      qed
    qed
    have hG_Bs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hHBs])
      show "\<forall>p\<in>?Bs. h (2 * fst p - 1) = ?G p"
      proof
        fix p assume hp: "p \<in> ?Bs"
        hence hge: "fst p \<ge> 1/2" by auto
        show "h (2 * fst p - 1) = ?G p"
        proof (cases "fst p = 1/2")
          case True
          have h2fst: "2 * fst p = 1" using True by simp
          hence "?G p = F (1, snd p)" by simp
          also have "... = x1" using hF1 hp by auto
          finally have l: "?G p = x1" .
          have h2m1: "2 * fst p - 1 = (0::real)" using True by simp
          have "h (2 * fst p - 1) = h 0" using h2m1 by simp
          thus ?thesis using l hh0 by simp
        next
          case False
          hence "fst p > 1/2" using hge by simp
          hence "\<not>(fst p \<le> 1/2)" by simp
          thus ?thesis by simp
        qed
      qed
    qed
    \<comment> \<open>Closedness of As, Bs in I\<times>I.\<close>
    have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
    have hAs_closed: "closedin_on (I_set \<times> I_set) II_topology ?As"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?As \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?As = {s\<in>I_set. s > 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "{s\<in>I_set. s > 1/2} = I_set \<inter> {s :: real. s > 1/2}"
          unfolding top1_unit_interval_def by auto
        also have "\<dots> \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using open_greaterThan[of "1/2::real"] unfolding top1_open_sets_def greaterThan_def by blast
        finally have "{s\<in>I_set. s > 1/2} \<in> I_top" .
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?As \<in> II_topology" .
    qed
    have hBs_closed: "closedin_on (I_set \<times> I_set) II_topology ?Bs"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Bs \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Bs = {s\<in>I_set. s < 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "{s\<in>I_set. s < 1/2} = I_set \<inter> {s :: real. s < 1/2}"
          unfolding top1_unit_interval_def by auto
        also have "\<dots> \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using open_lessThan[of "1/2::real"] unfolding top1_open_sets_def lessThan_def by blast
        finally have "{s\<in>I_set. s < 1/2} \<in> I_top" .
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?Bs \<in> II_topology" .
    qed
    have hcover: "?As \<union> ?Bs = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
    proof
      fix p assume hp: "p \<in> I_set \<times> I_set"
      show "?G p \<in> X"
      proof (cases "fst p \<le> 1/2")
        case True
        have "(2 * fst p, snd p) \<in> I_set \<times> I_set"
          using hp True unfolding top1_unit_interval_def by auto
        thus ?thesis using True hF unfolding top1_continuous_map_on_def by simp
      next
        case False
        have "2 * fst p - 1 \<in> I_set"
          using hp False unfolding top1_unit_interval_def by auto
        thus ?thesis using False hhcont unfolding top1_continuous_map_on_def by simp
      qed
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hAs_closed hBs_closed hcover hG_range hG_As hG_Bs])
  qed
  have hfpath: "top1_is_path_on X TX x0 x1 f"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hgpath: "top1_is_path_on X TX x0 x1 g"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hfh: "top1_is_path_on X TX x0 x2 (top1_path_product f h)"
    by (rule top1_path_product_is_path[OF hTX hfpath hh])
  have hgh: "top1_is_path_on X TX x0 x2 (top1_path_product g h)"
    by (rule top1_path_product_is_path[OF hTX hgpath hh])
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_product f h s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 0) = top1_path_product f h s"
    proof (cases "s \<le> 1/2")
      case True
      have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      hence "F (2*s, 0) = f (2*s)" using hFs0 by blast
      thus ?thesis using True unfolding top1_path_product_def by simp
    next
      case False thus ?thesis unfolding top1_path_product_def by simp
    qed
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_product g h s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 1) = top1_path_product g h s"
    proof (cases "s \<le> 1/2")
      case True
      have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      hence "F (2*s, 1) = g (2*s)" using hFs1 by blast
      thus ?thesis using True unfolding top1_path_product_def by simp
    next
      case False thus ?thesis unfolding top1_path_product_def by simp
    qed
  qed
  have hG0: "\<forall>t\<in>I_set. ?G (0, t) = x0" using hF0 by simp
  have hG1: "\<forall>t\<in>I_set. ?G (1, t) = x2" using hh1 by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hfh hgh hGcont hGs0 hGs1 hG0 hG1 by blast
qed

lemma path_homotopic_product_right:
  assumes hTX: "is_topology_on X TX"
      and hfg: "top1_path_homotopic_on X TX x1 x2 f g"
      and hh: "top1_is_path_on X TX x0 x1 h"
  shows "top1_path_homotopic_on X TX x0 x2 (top1_path_product h f) (top1_path_product h g)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x1" and hF1: "\<forall>t\<in>I_set. F (1, t) = x2"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hhcont: "top1_continuous_map_on I_set I_top X TX h"
    using hh unfolding top1_is_path_on_def by blast
  have hh0: "h 0 = x0" and hh1: "h 1 = x1"
    using hh unfolding top1_is_path_on_def by blast+
  let ?G = "\<lambda>p::real\<times>real. if fst p \<le> 1/2 then h (2 * fst p) else F (2 * fst p - 1, snd p)"
  \<comment> \<open>Continuity by spatial pasting (same structure as path_homotopic_product_left).\<close>
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    let ?As = "{s\<in>I_set. s \<le> 1/2} \<times> I_set"
    let ?Bs = "{s\<in>I_set. s \<ge> 1/2} \<times> I_set"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have hHAs: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX (\<lambda>p. h (2 * fst p))"
    proof -
      let ?\<rho> = "\<lambda>p::real\<times>real. max 0 (min 1 (2 * fst p))"
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho> p \<in> I_set" unfolding top1_unit_interval_def by auto
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>" by (intro continuous_intros)
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhcont])
      hence hrestr: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX (h \<circ> ?\<rho>)"
        by (rule top1_continuous_map_on_restrict_domain_simple) auto
      show ?thesis by (rule top1_continuous_map_on_agree[OF hrestr]) (auto simp: comp_def top1_unit_interval_def)
    qed
    have hFBs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX (\<lambda>p. F (2 * fst p - 1, snd p))"
    proof -
      have hmap: "\<And>p. p \<in> ?Bs \<Longrightarrow> (2 * fst p - 1, snd p) \<in> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
      have hcont: "continuous_on UNIV (\<lambda>p::real\<times>real. (2 * fst p - 1, snd p))" by (intro continuous_intros)
      have hBs_sub: "?Bs \<subseteq> I_set \<times> I_set" by auto
      have hraw: "top1_continuous_map_on ?Bs (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Bs)
                   (I_set \<times> I_set) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)) (\<lambda>p. (2 * fst p - 1, snd p))"
        by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
      have hdom: "subspace_topology (I_set \<times> I_set) II_topology ?Bs = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Bs"
        unfolding II_topology_def using subspace_topology_trans[OF hBs_sub] II_topology_eq_subspace by simp
      have hcod: "II_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
        unfolding II_topology_def by (rule II_topology_eq_subspace)
      have h\<phi>: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) (I_set \<times> I_set) II_topology (\<lambda>p. (2 * fst p - 1, snd p))"
        using hraw hdom hcod by simp
      show ?thesis using top1_continuous_map_on_comp[OF h\<phi> hF] by (simp add: comp_def)
    qed
    have hG_As: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX ?G"
      by (rule top1_continuous_map_on_agree[OF hHAs]) auto
    have hG_Bs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hFBs])
      show "\<forall>p\<in>?Bs. F (2 * fst p - 1, snd p) = ?G p"
      proof
        fix p assume hp: "p \<in> ?Bs"
        show "F (2 * fst p - 1, snd p) = ?G p"
        proof (cases "fst p = 1/2")
          case True
          have h2m1: "2 * fst p - 1 = (0::real)" using True by simp
          have h2fst: "2 * fst p = (1::real)" using True by simp
          have lhs: "F (2 * fst p - 1, snd p) = x1" using h2m1 hF0 hp by auto
          have rhs: "?G p = x1" using True h2fst hh1 by simp
          show ?thesis using lhs rhs by simp
        next
          case False hence "\<not>(fst p \<le> 1/2)" using hp by auto
          thus ?thesis by simp
        qed
      qed
    qed
    have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
    have hAs_closed: "closedin_on (I_set \<times> I_set) II_topology ?As"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?As \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?As = {s\<in>I_set. s > 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {s :: real. s > 1/2}" by (rule open_Collect_less[OF continuous_on_const continuous_on_id])
        hence "{s :: real. s > 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
        hence "I_set \<inter> {s. s > 1/2} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by blast
        moreover have "{s\<in>I_set. s > 1/2} = I_set \<inter> {s. s > 1/2}" by auto
        ultimately have "{s\<in>I_set. s > 1/2} \<in> I_top" by simp
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?As \<in> II_topology" .
    qed
    have hBs_closed: "closedin_on (I_set \<times> I_set) II_topology ?Bs"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Bs \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Bs = {s\<in>I_set. s < 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {s :: real. s < 1/2}" by (rule open_Collect_less[OF continuous_on_id continuous_on_const])
        hence "{s :: real. s < 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
        hence "I_set \<inter> {s. s < 1/2} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by blast
        moreover have "{s\<in>I_set. s < 1/2} = I_set \<inter> {s. s < 1/2}" by auto
        ultimately have "{s\<in>I_set. s < 1/2} \<in> I_top" by simp
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?Bs \<in> II_topology" .
    qed
    have hcover: "?As \<union> ?Bs = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
    proof
      fix p assume hp: "p \<in> I_set \<times> I_set"
      show "?G p \<in> X"
      proof (cases "fst p \<le> 1/2")
        case True
        have "2 * fst p \<in> I_set" using hp True unfolding top1_unit_interval_def by auto
        thus ?thesis using True hhcont unfolding top1_continuous_map_on_def by simp
      next
        case False
        have "(2 * fst p - 1, snd p) \<in> I_set \<times> I_set" using hp False unfolding top1_unit_interval_def by auto
        thus ?thesis using False hF unfolding top1_continuous_map_on_def by simp
      qed
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hAs_closed hBs_closed hcover hG_range hG_As hG_Bs])
  qed
  have hfpath: "top1_is_path_on X TX x1 x2 f"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hgpath: "top1_is_path_on X TX x1 x2 g"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hhf: "top1_is_path_on X TX x0 x2 (top1_path_product h f)"
    by (rule top1_path_product_is_path[OF hTX hh hfpath])
  have hhg: "top1_is_path_on X TX x0 x2 (top1_path_product h g)"
    by (rule top1_path_product_is_path[OF hTX hh hgpath])
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_product h f s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 0) = top1_path_product h f s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding top1_path_product_def by simp
    next
      case False
      have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hFs0 unfolding top1_path_product_def by simp
    qed
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_product h g s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 1) = top1_path_product h g s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding top1_path_product_def by simp
    next
      case False
      have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hFs1 unfolding top1_path_product_def by simp
    qed
  qed
  have hG0: "\<forall>t\<in>I_set. ?G (0, t) = x0" using hh0 by simp
  have hG1: "\<forall>t\<in>I_set. ?G (1, t) = x2" using hF1 by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hhf hhg hGcont hGs0 hGs1 hG0 hG1 by blast
qed

text \<open>Helper: for path-connected spaces, nulhomotopy at one basepoint implies
  simple connectivity (nulhomotopy at all basepoints via basepoint change).\<close>
lemma top1_simply_connected_from_one_point:
  assumes hTX: "is_topology_on X TX"
      and hpc: "top1_path_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hnul: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
          top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  shows "top1_simply_connected_on X TX"
  unfolding top1_simply_connected_on_def
proof (intro conjI ballI allI impI)
  show "top1_path_connected_on X TX" by (rule hpc)
next
  fix x1 f
  assume hx1: "x1 \<in> X" and hf1: "top1_is_loop_on X TX x1 f"
  \<comment> \<open>Choose path \<alpha> from x0 to x1 (path-connected). Conjugate: \<alpha>\<inverse> * f * \<alpha> is loop at x0.
     By hypothesis, \<alpha>\<inverse> * f * \<alpha> is nulhomotopic. Hence f is nulhomotopic at x1.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on X TX x0 x1 \<alpha>"
    using hpc hx0 hx1 unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Conjugate loop \<alpha>\<inverse> * f * \<alpha> at x0 is nulhomotopic.\<close>
  \<comment> \<open>Conjugate: \<alpha> * f * \<alpha>\<inverse> is a loop at x0.\<close>
  let ?conj = "top1_path_product (top1_path_product \<alpha> f) (top1_path_reverse \<alpha>)"
  have h\<alpha>_rev: "top1_is_path_on X TX x1 x0 (top1_path_reverse \<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>])
  have hf_path: "top1_is_path_on X TX x1 x1 f"
    using hf1 unfolding top1_is_loop_on_def .
  have h\<alpha>f: "top1_is_path_on X TX x0 x1 (top1_path_product \<alpha> f)"
    by (rule top1_path_product_is_path[OF hTX h\<alpha> hf_path])
  have hconj_path: "top1_is_path_on X TX x0 x0 ?conj"
    by (rule top1_path_product_is_path[OF hTX h\<alpha>f h\<alpha>_rev])
  have hconj_loop: "top1_is_loop_on X TX x0 ?conj"
    unfolding top1_is_loop_on_def using hconj_path by (by100 simp)
  have hconj_nul: "top1_path_homotopic_on X TX x0 x0 ?conj (top1_constant_path x0)"
    using hnul hconj_loop by (by100 blast)
  \<comment> \<open>From conjugate nulhomotopic, extract f nulhomotopic at x1.
     Proof uses path algebra: ?conj*\<alpha> \<simeq> const*\<alpha> \<simeq> \<alpha> and ?conj*\<alpha> \<simeq> (\<alpha>*f)*const \<simeq> \<alpha>*f,
     so \<alpha>*f \<simeq> \<alpha>, then \<alpha>\<inverse>*(\<alpha>*f) \<simeq> \<alpha>\<inverse>*\<alpha> \<simeq> const and \<alpha>\<inverse>*(\<alpha>*f) \<simeq> f, hence f \<simeq> const.
     Requires: path_homotopic_product_left/right, associativity, identity, inverse.\<close>
  show "top1_path_homotopic_on X TX x1 x1 f (top1_constant_path x1)"
  proof -
    let ?\<alpha>f = "top1_path_product \<alpha> f"
    \<comment> \<open>?conj * \<alpha> \<simeq> const * \<alpha> \<simeq> \<alpha>\<close>
    have s1: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>)
        (top1_path_product (top1_constant_path x0) \<alpha>)"
      by (rule path_homotopic_product_left[OF hTX hconj_nul h\<alpha>])
    have s2: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product (top1_constant_path x0) \<alpha>) \<alpha>"
      by (rule Theorem_51_2_left_identity[OF hTX h\<alpha>])
    have s12: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>) \<alpha>"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2])
    \<comment> \<open>?conj * \<alpha> \<simeq> \<alpha>*f by associativity + inverse + right identity\<close>
    have s3: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>)
        (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>))"
      by (rule Lemma_51_1_path_homotopic_sym[OF
            Theorem_51_2_associativity[OF hTX h\<alpha>f h\<alpha>_rev h\<alpha>]])
    have s4: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) (top1_constant_path x1)"
      by (rule Theorem_51_2_invgerse_right[OF hTX h\<alpha>])
    have s5: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>))
        (top1_path_product ?\<alpha>f (top1_constant_path x1))"
      by (rule path_homotopic_product_right[OF hTX s4 h\<alpha>f])
    have s6: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product ?\<alpha>f (top1_constant_path x1)) ?\<alpha>f"
      by (rule Theorem_51_2_right_identity[OF hTX h\<alpha>f])
    have s35: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>) ?\<alpha>f"
    proof (rule Lemma_51_1_path_homotopic_trans[OF hTX s3])
      show "top1_path_homotopic_on X TX x0 x1
          (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>)) ?\<alpha>f"
        by (rule Lemma_51_1_path_homotopic_trans[OF hTX s5 s6])
    qed
    \<comment> \<open>\<alpha>*f \<simeq> \<alpha>\<close>
    have s35_sym: "top1_path_homotopic_on X TX x0 x1 ?\<alpha>f (top1_path_product ?conj \<alpha>)"
      by (rule Lemma_51_1_path_homotopic_sym[OF s35])
    have h\<alpha>f_\<alpha>: "top1_path_homotopic_on X TX x0 x1 ?\<alpha>f \<alpha>"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s35_sym s12])
    \<comment> \<open>\<alpha>\<inverse>*(\<alpha>*f) \<simeq> \<alpha>\<inverse>*\<alpha> \<simeq> const_x1\<close>
    have s7: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)
        (top1_path_product (top1_path_reverse \<alpha>) \<alpha>)"
      by (rule path_homotopic_product_right[OF hTX h\<alpha>f_\<alpha> h\<alpha>_rev])
    have s78: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f) (top1_constant_path x1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s7 s4])
    \<comment> \<open>\<alpha>\<inverse>*(\<alpha>*f) \<simeq> (\<alpha>\<inverse>*\<alpha>)*f \<simeq> const*f \<simeq> f\<close>
    have s8a: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)
        (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f)"
      by (rule Theorem_51_2_associativity[OF hTX h\<alpha>_rev h\<alpha> hf_path])
    have s8b: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f)
        (top1_path_product (top1_constant_path x1) f)"
      by (rule path_homotopic_product_left[OF hTX s4 hf_path])
    have s8c: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_constant_path x1) f) f"
      by (rule Theorem_51_2_left_identity[OF hTX hf_path])
    have s8: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f) f"
    proof (rule Lemma_51_1_path_homotopic_trans[OF hTX s8a])
      show "top1_path_homotopic_on X TX x1 x1
          (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f) f"
        by (rule Lemma_51_1_path_homotopic_trans[OF hTX s8b s8c])
    qed
    have s8_sym: "top1_path_homotopic_on X TX x1 x1 f
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)"
      by (rule Lemma_51_1_path_homotopic_sym[OF s8])
    show ?thesis
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s8_sym s78])
  qed
qed

text \<open>Change of basepoint map: alpha-hat([f]) = [rev-alpha * f * alpha] where alpha is a path x0 -> x1.\<close>
definition top1_basepoint_change_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_basepoint_change_on X TX x0 x1 alpha f =
     top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha)"

(** from \<S>52 Theorem 52.1 (homomorphism part): the basepoint-change map
    \<alpha>-hat preserves the path-product operation up to path homotopy.
    Combined with bijectivity this gives a group isomorphism of \<pi>_1(X, x_0)
    with \<pi>_1(X, x_1). **)
theorem Theorem_52_1:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha (top1_path_product f g))
    (top1_path_product
      (top1_basepoint_change_on X TX x0 x1 alpha f)
      (top1_basepoint_change_on X TX x0 x1 alpha g))"
proof -
  let ?aR = "top1_path_reverse alpha"
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hgp: "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
  have haR: "top1_is_path_on X TX x1 x0 ?aR" by (rule top1_path_reverse_is_path[OF halpha])
  have hfg: "top1_is_path_on X TX x0 x0 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX hfp hgp])
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f alpha)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hga: "top1_is_path_on X TX x0 x1 (top1_path_product g alpha)"
    by (rule top1_path_product_is_path[OF hTX hgp halpha])
  have hfga: "top1_is_path_on X TX x0 x1 (top1_path_product (top1_path_product f g) alpha)"
    by (rule top1_path_product_is_path[OF hTX hfg halpha])
  have haR_fa: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product f alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hfa])
  have haR_ga: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product g alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hga])
  \<comment> \<open>Step 1: (α⁻¹*(f*α)) * (α⁻¹*(g*α)) ≃ α⁻¹ * ((f*α) * (α⁻¹*(g*α))) by assoc.\<close>
  have step1: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha))
                       (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f alpha)
                                               (top1_path_product ?aR (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
         Theorem_51_2_associativity[OF hTX haR hfa haR_ga]])
  \<comment> \<open>Steps 2-6 require right congruence (h*f ≃ h*g when f ≃ g) to manipulate
     inside the α⁻¹ * (...) context. Right congruence spatial pasting is blocked
     by build time ceiling. Each step uses assoc/inv/id applied inside.\<close>
  \<comment> \<open>Step 2: α⁻¹ * ((f*α) * (α⁻¹*(g*α))) ≃ α⁻¹ * (f * (α * (α⁻¹*(g*α)))) by right cong + assoc.\<close>
  have haR_ga_path: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product g alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hga])
  have step2_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_path_product f alpha) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX hfp halpha haR_ga_path]])
  have step2: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product (top1_path_product f alpha) (top1_path_product ?aR (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))"
    by (rule path_homotopic_product_right[OF hTX step2_inner haR])
  \<comment> \<open>Step 3: α * (α⁻¹*(g*α)) ≃ (α*α⁻¹) * (g*α) by assoc.\<close>
  have step3_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))"
    by (rule Theorem_51_2_associativity[OF hTX halpha haR hga])
  have step3_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha))))
    (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step3_inner hfp])
  have step3: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))"
    by (rule path_homotopic_product_right[OF hTX step3_mid haR])
  \<comment> \<open>Step 4: (α*α⁻¹) ≃ e by inverse.\<close>
  have step4_inv: "top1_path_homotopic_on X TX x0 x0
    (top1_path_product alpha ?aR) (top1_constant_path x0)"
    by (rule Theorem_51_2_invgerse_left[OF hTX halpha])
  have step4_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))
    (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))"
    by (rule path_homotopic_product_left[OF hTX step4_inv hga])
  have step4_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step4_inner hfp])
  have step4: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))"
    by (rule path_homotopic_product_right[OF hTX step4_mid haR])
  \<comment> \<open>Step 5: e * (g*α) ≃ (g*α) by left identity.\<close>
  have step5_id: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)) (top1_path_product g alpha)"
    by (rule Theorem_51_2_left_identity[OF hTX hga])
  have step5_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product g alpha))"
    by (rule path_homotopic_product_right[OF hTX step5_id hfp])
  have step5: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step5_mid haR])
  \<comment> \<open>Step 6: f * (g*α) ≃ (f*g) * α by assoc.\<close>
  have step6_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product g alpha))
    (top1_path_product (top1_path_product f g) alpha)"
    by (rule Theorem_51_2_associativity[OF hTX hfp hgp halpha])
  have step6_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product g alpha))
    (top1_path_product (top1_path_product f g) alpha)"
    using step6_inner .
  have step6: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))"
    by (rule path_homotopic_product_right[OF hTX step6_mid haR])
  \<comment> \<open>Chain: RHS ≃ step1 ≃ step2 ≃ step3 ≃ step4 ≃ step5 ≃ step6 = LHS.\<close>
  \<comment> \<open>Chain all 6 steps via transitivity.\<close>
  have chain12: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX step1 step2])
  have chain123: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12 step3])
  have chain1234: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123 step4])
  have chain12345: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain1234 step5])
  have chain123456: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12345 step6])
  \<comment> \<open>The chain goes from RHS to LHS. Symmetry gives LHS ≃ RHS.\<close>
  have result: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF chain123456])
  show ?thesis unfolding top1_basepoint_change_on_def using result .
qed

subsection \<open>Lightweight group-theoretic machinery (needed for \<S>52 onwards)\<close>

text \<open>A group is a 4-tuple (G, mul, e, invg) satisfying associativity,
  left/right identity, and left/right invgerse.
  Definitions placed here (before \<S>52) so Theorem\_52\_1\_iso can unfold them.\<close>
definition top1_is_group_on :: "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> bool" where
  "top1_is_group_on G mul e invg \<longleftrightarrow>
     e \<in> G \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G) \<and>
     (\<forall>x\<in>G. invg x \<in> G) \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)) \<and>
     (\<forall>x\<in>G. mul e x = x \<and> mul x e = x) \<and>
     (\<forall>x\<in>G. mul (invg x) x = e \<and> mul x (invg x) = e)"

text \<open>An abelian group additionally satisfies commutativity.\<close>
definition top1_is_abelian_group_on :: "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> bool" where
  "top1_is_abelian_group_on G mul e invg \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. mul x y = mul y x)"

text \<open>Group homomorphism: f preserves multiplication (and hence identity and invgerse).\<close>
definition top1_group_hom_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_group_hom_on G mulG H mulH f \<longleftrightarrow>
     (\<forall>x\<in>G. f x \<in> H) \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. f (mulG x y) = mulH (f x) (f y))"

text \<open>Group isomorphism: bijective homomorphism.\<close>
definition top1_group_iso_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_group_iso_on G mulG H mulH f \<longleftrightarrow>
     top1_group_hom_on G mulG H mulH f \<and>
     bij_betw f G H"

definition top1_groups_isomorphic_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_groups_isomorphic_on G mulG H mulH \<longleftrightarrow>
     (\<exists>f. top1_group_iso_on G mulG H mulH f)"

text \<open>Helper: basepoint change preserves path homotopy (congruence).\<close>
lemma top1_basepoint_change_congruence:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hf': "top1_is_loop_on X TX x0 f'"
      and hff': "top1_path_homotopic_on X TX x0 x0 f f'"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha f')"
  unfolding top1_basepoint_change_on_def
proof -
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse alpha)"
    by (rule top1_path_reverse_is_path[OF halpha])
  \<comment> \<open>Step 1: f * \<alpha> \<simeq> f' * \<alpha> (left congruence)\<close>
  have step1: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product f alpha) (top1_path_product f' alpha)"
    by (rule path_homotopic_product_left[OF hTX hff' halpha])
  \<comment> \<open>Step 2: \<alpha>^{-1} * (f * \<alpha>) \<simeq> \<alpha>^{-1} * (f' * \<alpha>) (right congruence)\<close>
  show "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha))
    (top1_path_product (top1_path_reverse alpha) (top1_path_product f' alpha))"
    by (rule path_homotopic_product_right[OF hTX step1 hrev])
qed

text \<open>Helper: round-trip of basepoint change is homotopic to identity.
  \<alpha>-hat sends loops at x0 to loops at x1 via [f] \<mapsto> [\<alpha>^{-1} * f * \<alpha>].
  The round-trip via \<beta> = \<alpha>^{-1} composes to the identity on equivalence classes.\<close>
lemma top1_basepoint_change_roundtrip:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on X TX x0 x0 f
    (top1_basepoint_change_on X TX x1 x0 (top1_path_reverse alpha)
      (top1_basepoint_change_on X TX x0 x1 alpha f))"
proof -
  let ?a = alpha and ?ra = "top1_path_reverse alpha" and ?e = "top1_constant_path x0"
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hra: "top1_is_path_on X TX x1 x0 ?ra"
    by (rule top1_path_reverse_is_path[OF halpha])
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f ?a)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hara: "top1_is_path_on X TX x0 x0 (top1_path_product ?a ?ra)"
    by (rule top1_path_product_is_path[OF hTX halpha hra])
  have hrafa: "top1_is_path_on X TX x1 x1 (top1_path_product ?ra (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX hra hfa])
  have hrafara: "top1_is_path_on X TX x1 x0
      (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra)"
    by (rule top1_path_product_is_path[OF hTX hrafa hra])
  have hx0X: "x0 \<in> X"
  proof -
    have "alpha 0 \<in> X" using halpha unfolding top1_is_path_on_def top1_continuous_map_on_def
      top1_unit_interval_def by auto
    moreover have "alpha 0 = x0" using halpha unfolding top1_is_path_on_def by blast
    ultimately show ?thesis by simp
  qed
  have he: "top1_is_path_on X TX x0 x0 ?e"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  have hefa: "top1_is_path_on X TX x0 x1 (top1_path_product ?e (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX he hfa])
  have harafa: "top1_is_path_on X TX x0 x1
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX hara hfa])
  have harafap: "top1_is_path_on X TX x0 x1
      (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a)))"
    by (rule top1_path_product_is_path[OF hTX halpha hrafa])
  \<comment> \<open>Chain: f \<simeq> ... \<simeq> a * ((ra * (f * a)) * ra) using 7 groupoid steps.\<close>
  \<comment> \<open>Step 1: f \<simeq> f * e\<close>
  have s1: "top1_path_homotopic_on X TX x0 x0 f (top1_path_product f ?e)"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_right_identity[OF hTX hfp]])
  \<comment> \<open>Step 2: f * e \<simeq> f * (a * ra)\<close>
  have hinv_sym: "top1_path_homotopic_on X TX x0 x0 ?e (top1_path_product ?a ?ra)"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_left[OF hTX halpha]])
  have s2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product f ?e) (top1_path_product f (top1_path_product ?a ?ra))"
    by (rule path_homotopic_product_right[OF hTX hinv_sym hfp])
  \<comment> \<open>Step 3: f * (a * ra) \<simeq> (f * a) * ra\<close>
  have s3: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product f (top1_path_product ?a ?ra))
      (top1_path_product (top1_path_product f ?a) ?ra)"
    by (rule Theorem_51_2_associativity[OF hTX hfp halpha hra])
  \<comment> \<open>Step 4: (f * a) * ra \<simeq> (e * (f * a)) * ra\<close>
  have hlid_sym: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product f ?a) (top1_path_product ?e (top1_path_product f ?a))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_left_identity[OF hTX hfa]])
  have s4: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product f ?a) ?ra)
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hlid_sym hra])
  \<comment> \<open>Step 5: (e * (f * a)) * ra \<simeq> ((a * ra) * (f * a)) * ra\<close>
  have hcong5: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?e (top1_path_product f ?a))
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))"
    by (rule path_homotopic_product_left[OF hTX hinv_sym hfa])
  have s5: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hcong5 hra])
  \<comment> \<open>Step 6: ((a * ra) * (f * a)) * ra \<simeq> (a * (ra * (f * a))) * ra\<close>
  have hassoc_sym: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))
      (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX halpha hra hfa]])
  have s6: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hassoc_sym hra])
  \<comment> \<open>Step 7: (a * (ra * (f * a))) * ra \<simeq> a * ((ra * (f * a)) * ra)\<close>
  have s7: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)
      (top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX halpha hrafa hra]])
  \<comment> \<open>Chain all 7 steps.\<close>
  have chain12: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product f (top1_path_product ?a ?ra))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2])
  have chain123: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product f ?a) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12 s3])
  have chain1234: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123 s4])
  have chain12345: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain1234 s5])
  have chain123456: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12345 s6])
  have chain1234567: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123456 s7])
  \<comment> \<open>The target is exactly the expanded basepoint change.\<close>
  have htarget_eq: "top1_basepoint_change_on X TX x1 x0 ?ra
      (top1_basepoint_change_on X TX x0 x1 ?a f)
    = top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra)"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by rule
  show ?thesis using chain1234567 unfolding htarget_eq .
qed

text \<open>Helper: basepoint change sends loops to loops.\<close>
lemma top1_basepoint_change_is_loop:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha f)"
proof -
  have hra: "top1_is_path_on X TX x1 x0 (top1_path_reverse alpha)"
    by (rule top1_path_reverse_is_path[OF halpha])
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f alpha)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hresult: "top1_is_path_on X TX x1 x1
      (top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha))"
    by (rule top1_path_product_is_path[OF hTX hra hfa])
  show ?thesis unfolding top1_is_loop_on_def top1_basepoint_change_on_def
    using hresult .
qed

text \<open>Helper: basepoint change preserves loop equivalence.\<close>
lemma top1_basepoint_change_loop_equiv:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
      and hfg: "top1_loop_equiv_on X TX x0 f g"
  shows "top1_loop_equiv_on X TX x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha g)"
proof -
  have hhat_f: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha f)"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hf])
  have hhat_g: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha g)"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hg])
  have hhom: "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha g)"
  proof -
    have hff': "top1_path_homotopic_on X TX x0 x0 f g"
      using hfg unfolding top1_loop_equiv_on_def by blast
    show ?thesis by (rule top1_basepoint_change_congruence[OF hTX halpha hf hg hff'])
  qed
  show ?thesis unfolding top1_loop_equiv_on_def using hhat_f hhat_g hhom by blast
qed

text \<open>Helper: mul(class f, class g) = class(f*g) for the fundamental group.\<close>
lemma top1_fundamental_group_mul_class:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h}
      {h. top1_loop_equiv_on X TX x0 g h}
    = {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
proof (intro set_eqI iffI)
  fix h assume "h \<in> top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 g h}"
  then obtain f' g' where hf': "top1_loop_equiv_on X TX x0 f f'"
      and hg': "top1_loop_equiv_on X TX x0 g g'"
      and hfg': "top1_loop_equiv_on X TX x0 (top1_path_product f' g') h"
    unfolding top1_fundamental_group_mul_def by blast
  have hf'_path: "top1_is_path_on X TX x0 x0 f'"
    using hf' unfolding top1_loop_equiv_on_def top1_is_loop_on_def by blast
  have hff': "top1_path_homotopic_on X TX x0 x0 f f'"
    using hf' unfolding top1_loop_equiv_on_def by blast
  have hg_path: "top1_is_path_on X TX x0 x0 g"
    using hg unfolding top1_is_loop_on_def .
  have hfg_step: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f g) (top1_path_product f' g)"
    by (rule path_homotopic_product_left[OF hTX hff' hg_path])
  have hgg': "top1_path_homotopic_on X TX x0 x0 g g'"
    using hg' unfolding top1_loop_equiv_on_def by blast
  have hgg_step: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f' g) (top1_path_product f' g')"
    by (rule path_homotopic_product_right[OF hTX hgg' hf'_path])
  have hprod_hom: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f g) (top1_path_product f' g')"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX hfg_step hgg_step])
  have hfg_loop: "top1_is_loop_on X TX x0 (top1_path_product f g)"
    unfolding top1_is_loop_on_def
    by (rule top1_path_product_is_path[OF hTX])
       (use hf hg in \<open>auto simp: top1_is_loop_on_def\<close>)
  have hfg_equiv: "top1_loop_equiv_on X TX x0 (top1_path_product f g) (top1_path_product f' g')"
    unfolding top1_loop_equiv_on_def
    using hfg_loop hfg' hprod_hom unfolding top1_loop_equiv_on_def by blast
  show "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
    using top1_loop_equiv_on_trans[OF hTX hfg_equiv hfg'] by simp
next
  fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
  thus "h \<in> top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 g h}"
    unfolding top1_fundamental_group_mul_def
    using top1_loop_equiv_on_refl[OF hf] top1_loop_equiv_on_refl[OF hg] by blast
qed

(** Full Theorem 52.1 (group isomorphism): if X is path-connected, then
    \<pi>_1(X, x_0) \<cong> \<pi>_1(X, x_1) for any two basepoints x_0, x_1 \<in> X. **)
theorem Theorem_52_1_iso:
  assumes hTX: "is_topology_on X TX"
      and hpc: "top1_path_connected_on X TX"
      and hx0: "x0 \<in> X" and hx1: "x1 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier X TX x1)
           (top1_fundamental_group_mul X TX x1)"
proof -
  obtain alpha where halpha: "top1_is_path_on X TX x0 x1 alpha"
    using hpc hx0 hx1 unfolding top1_path_connected_on_def by blast
  let ?hat = "\<lambda>f. top1_basepoint_change_on X TX x0 x1 alpha f"
  let ?ra = "top1_path_reverse alpha"
  let ?hat_inv = "\<lambda>g. top1_basepoint_change_on X TX x1 x0 ?ra g"
  \<comment> \<open>Define \<phi> on equivalence classes.\<close>
  let ?\<phi> = "\<lambda>c. {g. \<exists>f\<in>c. top1_loop_equiv_on X TX x1 (?hat f) g}"
  \<comment> \<open>\<phi> maps carrier(x0) to carrier(x1), is a homomorphism, and is bijective.\<close>
  \<comment> \<open>Key fact: \<phi>(class f) = class(\<alpha>-hat f) for any f in class f.\<close>
  have hphi_class: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    ?\<phi> {g. top1_loop_equiv_on X TX x0 f g} =
    {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
  proof (intro set_eqI iffI)
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
    then obtain f' where hf'_eq: "top1_loop_equiv_on X TX x0 f f'"
        and hg_eq: "top1_loop_equiv_on X TX x1 (?hat f') g" by auto
    have hf': "top1_is_loop_on X TX x0 f'" using hf'_eq unfolding top1_loop_equiv_on_def by blast
    have hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f) (?hat f')"
      by (rule top1_basepoint_change_loop_equiv[OF hTX halpha hf hf' hf'_eq])
    show "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      using top1_loop_equiv_on_trans[OF hTX hhat_equiv hg_eq] by simp
  next
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
    hence hg: "top1_loop_equiv_on X TX x1 (?hat f) g" by simp
    \<comment> \<open>f itself is in its own class.\<close>
    have "f \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      using top1_loop_equiv_on_refl[OF hf] by simp
    moreover have "top1_loop_equiv_on X TX x1 (?hat f) g" by (rule hg)
    ultimately show "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}" by blast
  qed
  \<comment> \<open>\<phi> maps carrier(x0) into carrier(x1).\<close>
  have hphi_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      unfolding top1_fundamental_group_carrier_def by blast
    have "?\<phi> c = {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      unfolding hc by (rule hphi_class[OF hf])
    moreover have "top1_is_loop_on X TX x1 (?hat f)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf])
    ultimately show "?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
      unfolding top1_fundamental_group_carrier_def by blast
  qed
  \<comment> \<open>Injectivity: if \<phi>(c1) = \<phi>(c2) then c1 = c2.\<close>
  have hphi_inj: "inj_on ?\<phi> (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq: "?\<phi> c1 = ?\<phi> c2"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have h1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hf1])
    have h2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hf2])
    \<comment> \<open>From \<phi>(c1) = \<phi>(c2): class(\<alpha>-hat f1) = class(\<alpha>-hat f2).\<close>
    have hhat_f1_loop: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat f1) g}
        = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using h1 h2 heq by simp
    have "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      using top1_loop_equiv_on_refl[OF hhat_f1_loop] by simp
    hence "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using hclass_eq by simp
    hence hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f2) (?hat f1)" by simp
    \<comment> \<open>By roundtrip: f1 \<simeq> \<beta>-hat(\<alpha>-hat f1) and f2 \<simeq> \<beta>-hat(\<alpha>-hat f2).\<close>
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    have hrt1: "top1_path_homotopic_on X TX x0 x0 f1
        (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_roundtrip[OF hTX halpha hf1])
    have hrt2: "top1_path_homotopic_on X TX x0 x0 f2
        (?hat_inv (?hat f2))"
      by (rule top1_basepoint_change_roundtrip[OF hTX halpha hf2])
    \<comment> \<open>\<beta>-hat preserves the equiv: \<alpha>-hat f2 \<simeq> \<alpha>-hat f1 \<Rightarrow> \<beta>-hat(\<alpha>-hat f2) \<simeq> \<beta>-hat(\<alpha>-hat f1).\<close>
    have hhat_f2_loop: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hbeta_equiv: "top1_loop_equiv_on X TX x0
        (?hat_inv (?hat f2)) (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra hhat_f2_loop hhat_f1_loop hhat_equiv])
    \<comment> \<open>Chain: f1 \<simeq> \<beta>(\<alpha>(f1)) \<simeq> \<beta>(\<alpha>(f2)) \<simeq> f2 (backward).\<close>
    have f1_equiv: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f1))"
      unfolding top1_loop_equiv_on_def using hf1 hrt1
      top1_basepoint_change_is_loop[OF hTX hra hhat_f1_loop] by blast
    have f1_to_f2: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f2))"
      using top1_loop_equiv_on_trans[OF hTX f1_equiv
        top1_loop_equiv_on_sym[OF hbeta_equiv]] .
    have f2_equiv_sym: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) f2"
    proof -
      have "top1_loop_equiv_on X TX x0 f2 (?hat_inv (?hat f2))"
        unfolding top1_loop_equiv_on_def using hf2 hrt2
        top1_basepoint_change_is_loop[OF hTX hra hhat_f2_loop] by blast
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    have f1f2_equiv: "top1_loop_equiv_on X TX x0 f1 f2"
      using top1_loop_equiv_on_trans[OF hTX f1_to_f2 f2_equiv_sym] .
    \<comment> \<open>Hence c1 = c2.\<close>
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 f1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 f2 g"
      proof
        fix g assume h: "top1_loop_equiv_on X TX x0 f1 g"
        show "top1_loop_equiv_on X TX x0 f2 g"
          using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF f1f2_equiv] h] .
      next
        fix g assume h: "top1_loop_equiv_on X TX x0 f2 g"
        show "top1_loop_equiv_on X TX x0 f1 g"
          using top1_loop_equiv_on_trans[OF hTX f1f2_equiv h] .
      qed
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  \<comment> \<open>Surjectivity: for any class at x1, there's a preimage class at x0.\<close>
  have hphi_surj: "?\<phi> ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier X TX x1"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier X TX x0" and hd: "d = ?\<phi> c"
      by blast
    show "d \<in> top1_fundamental_group_carrier X TX x1"
      using hphi_range hc hd by blast
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier X TX x1"
    obtain h where hh: "top1_is_loop_on X TX x1 h"
        and hd_eq: "d = {g. top1_loop_equiv_on X TX x1 h g}"
      using hd unfolding top1_fundamental_group_carrier_def by blast
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    let ?g = "?hat_inv h"
    have hg_loop: "top1_is_loop_on X TX x0 ?g"
      by (rule top1_basepoint_change_is_loop[OF hTX hra hh])
    have hg_class: "{f. top1_loop_equiv_on X TX x0 ?g f} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hg_loop by blast
    \<comment> \<open>\<phi>(class \<beta>-hat h) = class(\<alpha>-hat(\<beta>-hat h)).\<close>
    have hphi_g: "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f}
        = {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      by (rule hphi_class[OF hg_loop])
    \<comment> \<open>Reverse roundtrip: h \<simeq> \<alpha>-hat(\<beta>-hat h).\<close>
    have hrev_rt: "top1_path_homotopic_on X TX x1 x1 h (?hat (?hat_inv h))"
    proof -
      have hrev_alpha_rev: "top1_path_reverse ?ra = alpha"
        by (simp add: top1_path_reverse_twice)
      have "top1_path_homotopic_on X TX x1 x1 h
          (top1_basepoint_change_on X TX x0 x1 (top1_path_reverse ?ra)
            (top1_basepoint_change_on X TX x1 x0 ?ra h))"
        by (rule top1_basepoint_change_roundtrip[OF hTX hra hh])
      thus ?thesis unfolding hrev_alpha_rev .
    qed
    \<comment> \<open>So class(\<alpha>-hat(\<beta>-hat h)) = class(h) = d.\<close>
    have hequiv: "top1_loop_equiv_on X TX x1 h (?hat ?g)"
      unfolding top1_loop_equiv_on_def
      using hh top1_basepoint_change_is_loop[OF hTX halpha hg_loop] hrev_rt by blast
    have "\<And>g. top1_loop_equiv_on X TX x1 (?hat ?g) g \<longleftrightarrow>
              top1_loop_equiv_on X TX x1 h g"
    proof
      fix g' assume h1: "top1_loop_equiv_on X TX x1 (?hat ?g) g'"
      show "top1_loop_equiv_on X TX x1 h g'"
        by (rule top1_loop_equiv_on_trans[OF hTX hequiv h1])
    next
      fix g' assume h1: "top1_loop_equiv_on X TX x1 h g'"
      have "top1_loop_equiv_on X TX x1 (?hat ?g) h"
        by (rule top1_loop_equiv_on_sym[OF hequiv])
      thus "top1_loop_equiv_on X TX x1 (?hat ?g) g'"
        by (rule top1_loop_equiv_on_trans[OF hTX _ h1])
    qed
    hence hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat ?g) g}
        = {g. top1_loop_equiv_on X TX x1 h g}" by auto
    have "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f} = d"
      unfolding hphi_g hclass_eq hd_eq ..
    thus "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
      using hg_class by blast
  qed
  \<comment> \<open>Helper: mul(class f, class g) = class(f*g) for loops f, g at the same basepoint.\<close>
  have hmul_class: "\<And>Y TY y0 f g.
    \<lbrakk>is_topology_on Y TY; top1_is_loop_on Y TY y0 f; top1_is_loop_on Y TY y0 g\<rbrakk> \<Longrightarrow>
    top1_fundamental_group_mul Y TY y0
      {h. top1_loop_equiv_on Y TY y0 f h}
      {h. top1_loop_equiv_on Y TY y0 g h}
    = {h. top1_loop_equiv_on Y TY y0 (top1_path_product f g) h}"
    by (rule top1_fundamental_group_mul_class)
  \<comment> \<open>Homomorphism: \<phi> preserves multiplication.\<close>
  have hphi_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    \<comment> \<open>mul(c1, c2) = class(f1 * f2).\<close>
    have hf1f2: "top1_is_loop_on X TX x0 (top1_path_product f1 f2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hf1 hf2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product f1 f2) h}"
      unfolding hc1_eq hc2_eq by (rule hmul_class[OF hTX hf1 hf2])
    \<comment> \<open>\<phi>(mul) = class(\<alpha>-hat(f1*f2)).\<close>
    have hphi_mul: "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2)
        = {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
      unfolding hmul_eq by (rule hphi_class[OF hf1f2])
    \<comment> \<open>mul(\<phi> c1, \<phi> c2) = class(\<alpha>-hat(f1) * \<alpha>-hat(f2)).\<close>
    have hhat_f1: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have hhat_f2: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hphi_c1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hf1])
    have hphi_c2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hf2])
    have hmul_phi: "top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)
        = {h. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) h}"
      unfolding hphi_c1 hphi_c2 by (rule hmul_class[OF hTX hhat_f1 hhat_f2])
    \<comment> \<open>By Theorem 52.1: \<alpha>-hat(f1*f2) \<simeq> \<alpha>-hat(f1) * \<alpha>-hat(f2).\<close>
    have hThm: "top1_path_homotopic_on X TX x1 x1
        (?hat (top1_path_product f1 f2))
        (top1_path_product (?hat f1) (?hat f2))"
      by (rule Theorem_52_1[OF hTX halpha hf1 hf2])
    \<comment> \<open>Hence the classes are equal.\<close>
    have hhat_f1f2: "top1_is_loop_on X TX x1 (?hat (top1_path_product f1 f2))"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1f2])
    have hprod_loop: "top1_is_loop_on X TX x1 (top1_path_product (?hat f1) (?hat f2))"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hhat_f1 hhat_f2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hequiv: "top1_loop_equiv_on X TX x1
        (?hat (top1_path_product f1 f2)) (top1_path_product (?hat f1) (?hat f2))"
      unfolding top1_loop_equiv_on_def using hhat_f1f2 hprod_loop hThm by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}
        = {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
    proof (intro set_eqI iffI)
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
      hence "top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g" by simp
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv]] by simp
    next
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
      hence "top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g" by simp
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv] by simp
    qed
    show "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
      unfolding hphi_mul hmul_phi hclass_eq ..
  qed
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier X TX x1)
      (top1_fundamental_group_mul X TX x1) ?\<phi>"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hphi_range hphi_hom hphi_inj hphi_surj by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

text \<open>Path-specific version: given a specific path, the basepoint change is an iso.
  Follows from Theorem\_52\_1\_iso since a path between two points implies
  they are in a common path-component.\<close>
corollary basepoint_change_iso_via_path:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier X TX x1)
           (top1_fundamental_group_mul X TX x1)"
proof -
  \<comment> \<open>Same proof as Theorem\_52\_1\_iso but starting from a given path.\<close>
  let ?hat = "\<lambda>f. top1_basepoint_change_on X TX x0 x1 alpha f"
  let ?ra = "top1_path_reverse alpha"
  let ?hat_inv = "\<lambda>g. top1_basepoint_change_on X TX x1 x0 ?ra g"
  let ?\<phi> = "\<lambda>c. {g. \<exists>f\<in>c. top1_loop_equiv_on X TX x1 (?hat f) g}"
  have hphi_class: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    ?\<phi> {g. top1_loop_equiv_on X TX x0 f g} =
    {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
  proof (intro set_eqI iffI)
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
    then obtain f' where hf'_eq: "top1_loop_equiv_on X TX x0 f f'"
        and hg_eq: "top1_loop_equiv_on X TX x1 (?hat f') g" by auto
    have hf': "top1_is_loop_on X TX x0 f'" using hf'_eq unfolding top1_loop_equiv_on_def by blast
    show "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      using top1_loop_equiv_on_trans[OF hTX
        top1_basepoint_change_loop_equiv[OF hTX halpha hf hf' hf'_eq] hg_eq] by simp
  next
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
    thus "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
      using top1_loop_equiv_on_refl[OF hf] by blast
  qed
  have hphi_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      unfolding top1_fundamental_group_carrier_def by blast
    show "?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
      unfolding hc hphi_class[OF hf] top1_fundamental_group_carrier_def
      using top1_basepoint_change_is_loop[OF hTX halpha hf] by blast
  qed
  have hphi_inj: "inj_on ?\<phi> (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq: "?\<phi> c1 = ?\<phi> c2"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat f1) g}
        = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using heq unfolding hc1_eq hc2_eq hphi_class[OF hf1] hphi_class[OF hf2] .
    have hhat_f1_loop: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      using top1_loop_equiv_on_refl[OF hhat_f1_loop] by simp
    hence "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using hclass_eq by simp
    hence hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f2) (?hat f1)" by simp
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    have hhat_f2_loop: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hbeta_equiv: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra hhat_f2_loop hhat_f1_loop hhat_equiv])
    have f1_equiv: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f1))"
      unfolding top1_loop_equiv_on_def using hf1
        top1_basepoint_change_roundtrip[OF hTX halpha hf1]
        top1_basepoint_change_is_loop[OF hTX hra hhat_f1_loop] by blast
    have f1_to_f2: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f2))"
      using top1_loop_equiv_on_trans[OF hTX f1_equiv
        top1_loop_equiv_on_sym[OF hbeta_equiv]] .
    have f2_equiv_sym: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) f2"
      by (rule top1_loop_equiv_on_sym)
         (unfold top1_loop_equiv_on_def, use hf2
           top1_basepoint_change_roundtrip[OF hTX halpha hf2]
           top1_basepoint_change_is_loop[OF hTX hra hhat_f2_loop] in blast)
    have f1f2_equiv: "top1_loop_equiv_on X TX x0 f1 f2"
      using top1_loop_equiv_on_trans[OF hTX f1_to_f2 f2_equiv_sym] .
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 f1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 f2 g"
      proof
        fix g assume "top1_loop_equiv_on X TX x0 f1 g"
        thus "top1_loop_equiv_on X TX x0 f2 g"
          using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF f1f2_equiv]] by blast
      next
        fix g assume "top1_loop_equiv_on X TX x0 f2 g"
        thus "top1_loop_equiv_on X TX x0 f1 g"
          using top1_loop_equiv_on_trans[OF hTX f1f2_equiv] by blast
      qed
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  have hphi_surj: "?\<phi> ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier X TX x1"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
    thus "d \<in> top1_fundamental_group_carrier X TX x1"
      using hphi_range by blast
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier X TX x1"
    obtain h where hh: "top1_is_loop_on X TX x1 h"
        and hd_eq: "d = {g. top1_loop_equiv_on X TX x1 h g}"
      using hd unfolding top1_fundamental_group_carrier_def by blast
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    let ?g = "?hat_inv h"
    have hg_loop: "top1_is_loop_on X TX x0 ?g"
      by (rule top1_basepoint_change_is_loop[OF hTX hra hh])
    have hphi_g: "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f}
        = {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      by (rule hphi_class[OF hg_loop])
    have hrev_rt: "top1_path_homotopic_on X TX x1 x1 h (?hat (?hat_inv h))"
      using top1_basepoint_change_roundtrip[OF hTX hra hh]
      unfolding top1_path_reverse_twice .
    have hequiv: "top1_loop_equiv_on X TX x1 h (?hat ?g)"
      unfolding top1_loop_equiv_on_def
      using hh top1_basepoint_change_is_loop[OF hTX halpha hg_loop] hrev_rt by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat ?g) g}
        = {g. top1_loop_equiv_on X TX x1 h g}"
    proof (intro set_eqI iffI)
      fix g' assume "g' \<in> {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      thus "g' \<in> {g. top1_loop_equiv_on X TX x1 h g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv] by simp
    next
      fix g' assume "g' \<in> {g. top1_loop_equiv_on X TX x1 h g}"
      hence "top1_loop_equiv_on X TX x1 h g'" by simp
      thus "g' \<in> {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv]] by simp
    qed
    have "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f} = d"
      unfolding hphi_g hclass_eq hd_eq ..
    moreover have "{f. top1_loop_equiv_on X TX x0 ?g f} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hg_loop by blast
    ultimately show "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0" by blast
  qed
  have hmul_class: "\<And>Y TY y0 f g.
    \<lbrakk>is_topology_on Y TY; top1_is_loop_on Y TY y0 f; top1_is_loop_on Y TY y0 g\<rbrakk> \<Longrightarrow>
    top1_fundamental_group_mul Y TY y0
      {h. top1_loop_equiv_on Y TY y0 f h} {h. top1_loop_equiv_on Y TY y0 g h}
    = {h. top1_loop_equiv_on Y TY y0 (top1_path_product f g) h}"
    by (rule top1_fundamental_group_mul_class)
  have hphi_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 l1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 l2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hl12: "top1_is_loop_on X TX x0 (top1_path_product l1 l2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hl1 hl2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product l1 l2) h}"
      unfolding hc1_eq hc2_eq by (rule hmul_class[OF hTX hl1 hl2])
    have hLHS: "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2)
        = {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
      unfolding hmul_eq by (rule hphi_class[OF hl12])
    have hhat_l1: "top1_is_loop_on X TX x1 (?hat l1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hl1])
    have hhat_l2: "top1_is_loop_on X TX x1 (?hat l2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hl2])
    have hphi_c1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat l1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hl1])
    have hphi_c2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat l2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hl2])
    have hRHS: "top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)
        = {h. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) h}"
      unfolding hphi_c1 hphi_c2 by (rule hmul_class[OF hTX hhat_l1 hhat_l2])
    have hThm: "top1_path_homotopic_on X TX x1 x1
        (?hat (top1_path_product l1 l2))
        (top1_path_product (?hat l1) (?hat l2))"
      by (rule Theorem_52_1[OF hTX halpha hl1 hl2])
    have hprod_loop: "top1_is_loop_on X TX x1 (top1_path_product (?hat l1) (?hat l2))"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hhat_l1 hhat_l2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hequiv': "top1_loop_equiv_on X TX x1
        (?hat (top1_path_product l1 l2)) (top1_path_product (?hat l1) (?hat l2))"
      unfolding top1_loop_equiv_on_def
      using top1_basepoint_change_is_loop[OF hTX halpha hl12] hprod_loop hThm by blast
    have hclass_eq': "{g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}
        = {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
    proof (intro set_eqI iffI)
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv']] by simp
    next
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv'] by simp
    qed
    show "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
      unfolding hLHS hRHS hclass_eq' ..
  qed
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier X TX x1)
      (top1_fundamental_group_mul X TX x1) ?\<phi>"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hphi_range hphi_hom hphi_inj hphi_surj by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

text \<open>Functoriality of fundamental group: (k o h)_* = k_* o h_*.\<close>
(** from \<S>52 Theorem 52.4 **)
theorem Theorem_52_4_composition:
  assumes "top1_continuous_map_on X TX Y TY h"
      and "top1_continuous_map_on Y TY Z TZ k"
      and "top1_is_loop_on X TX x0 f"
  shows "top1_induced_homomorphism_on X TX Z TZ (k \<circ> h) f =
         top1_induced_homomorphism_on Y TY Z TZ k
           (top1_induced_homomorphism_on X TX Y TY h f)"
  unfolding top1_induced_homomorphism_on_def by (simp add: comp_assoc)

theorem Theorem_52_4_identity:
  assumes "top1_is_loop_on X TX x0 f"
  shows "top1_induced_homomorphism_on X TX X TX id f = f"
  unfolding top1_induced_homomorphism_on_def by simp

section \<open>\<S>53 Covering Spaces\<close>

text \<open>Evenly covered: an open U \<subseteq> B is evenly covered by p: E \<rightarrow> B if
  p\<invgerse>(U) is a disjoint union of open V\<alpha> \<subseteq> E, each mapped homeomorphically by p.
  Uses openin_on: each V is open in E and a subset of E.\<close>
definition top1_evenly_covered_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "top1_evenly_covered_on E TE B TB p U \<longleftrightarrow>
     openin_on B TB U \<and>
     (\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
          (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
          {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
          (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p))"

text \<open>Covering map: every point of B has a neighborhood evenly covered by p.\<close>
definition top1_covering_map_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_covering_map_on E TE B TB p \<longleftrightarrow>
     top1_continuous_map_on E TE B TB p \<and>
     p ` E = B \<and>
     (\<forall>b\<in>B. \<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE B TB p U)"

lemma top1_covering_map_on_continuous:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> top1_continuous_map_on E TE B TB p"
  unfolding top1_covering_map_on_def by blast

lemma top1_covering_map_on_surj:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> p ` E = B"
  unfolding top1_covering_map_on_def by blast

lemma top1_covering_map_on_evenly_covered:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> b \<in> B \<Longrightarrow>
    \<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE B TB p U"
  unfolding top1_covering_map_on_def by blast

text \<open>Helper: evenly-covered U is open (by definition).\<close>
lemma top1_evenly_covered_on_openin_on:
  assumes "top1_evenly_covered_on E TE B TB p U"
  shows "openin_on B TB U"
proof -
  from assms have "openin_on B TB U \<and>
     (\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
          (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
          {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
          (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p))"
    unfolding top1_evenly_covered_on_def .
  thus ?thesis by (rule conjunct1)
qed

text \<open>In a strict cover, every open cover point has an open neighborhood.\<close>
lemma top1_covering_map_on_strict_evenly_covered_openin:
  assumes "top1_covering_map_on E TE B TB p"
  and "b \<in> B"
  shows "\<exists>U. b \<in> U \<and> openin_on B TB U"
proof -
  obtain U where hbU: "b \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
    using top1_covering_map_on_evenly_covered[OF assms] by blast
  have "openin_on B TB U" by (rule top1_evenly_covered_on_openin_on[OF hec])
  thus ?thesis using hbU by blast
qed

text \<open>Lifting of a continuous map: f\<tilde>: X \<rightarrow> E with p \<circ> f\<tilde> = f.\<close>
definition top1_is_lifting_on :: "'x set \<Rightarrow> 'x set set \<Rightarrow> 'e set \<Rightarrow> 'e set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<longleftrightarrow>
     top1_continuous_map_on X TX E TE ftilde \<and>
     (\<forall>x\<in>X. p (ftilde x) = f x)"

lemma top1_is_lifting_on_continuous:
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<Longrightarrow>
    top1_continuous_map_on X TX E TE ftilde"
  unfolding top1_is_lifting_on_def by blast

lemma top1_is_lifting_on_covers:
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<Longrightarrow>
    \<forall>x\<in>X. p (ftilde x) = f x"
  unfolding top1_is_lifting_on_def by blast

text \<open>The unit circle S^1 as a subspace of R^2.\<close>
definition top1_S1 :: "(real \<times> real) set" where
  "top1_S1 = {p. fst p ^ 2 + snd p ^ 2 = 1}"

definition top1_S1_topology :: "(real \<times> real) set set" where
  "top1_S1_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_S1"

text \<open>The canonical covering map p: R \<rightarrow> S^1 given by p(x) = (cos 2\<pi>x, sin 2\<pi>x).\<close>
definition top1_R_to_S1 :: "real \<Rightarrow> real \<times> real" where
  "top1_R_to_S1 x = (cos (2 * pi * x), sin (2 * pi * x))"

(** from \<S>53 Theorem 53.1: the canonical map R \<rightarrow> S^1 is a covering map.

    Munkres' proof: for U \<subseteq> S^1 the open arc with positive first coord,
    p^{-1}(U) is \<Union>_{n\<in>Z} (n - 1/4, n + 1/4). Each such interval maps
    homeomorphically to U (cos is a bijection between (-1/4,1/4) and (-\<pi>/2, \<pi>/2)
    mod 2\<pi>). The four similar arcs (positive/negative first/second coordinate) cover S^1. **)

text \<open>Helper: four open arcs covering S^1.\<close>
definition top1_S1_arc_E :: "(real \<times> real) set" where
  "top1_S1_arc_E = {(x,y). x^2 + y^2 = 1 \<and> x > 0}"
definition top1_S1_arc_W :: "(real \<times> real) set" where
  "top1_S1_arc_W = {(x,y). x^2 + y^2 = 1 \<and> x < 0}"
definition top1_S1_arc_N :: "(real \<times> real) set" where
  "top1_S1_arc_N = {(x,y). x^2 + y^2 = 1 \<and> y > 0}"
definition top1_S1_arc_S :: "(real \<times> real) set" where
  "top1_S1_arc_S = {(x,y). x^2 + y^2 = 1 \<and> y < 0}"

lemma top1_S1_arcs_cover: "top1_S1 \<subseteq> top1_S1_arc_E \<union> top1_S1_arc_W \<union> top1_S1_arc_N \<union> top1_S1_arc_S"
proof (intro subsetI)
  fix p :: "real \<times> real"
  assume hp: "p \<in> top1_S1"
  obtain x y where hpxy: "p = (x, y)" by (cases p) blast
  have heq: "x^2 + y^2 = 1" using hp hpxy unfolding top1_S1_def by simp
  have hne: "x \<noteq> 0 \<or> y \<noteq> 0" using heq by auto
  show "p \<in> top1_S1_arc_E \<union> top1_S1_arc_W \<union> top1_S1_arc_N \<union> top1_S1_arc_S"
    unfolding top1_S1_arc_E_def top1_S1_arc_W_def top1_S1_arc_N_def top1_S1_arc_S_def
    using hne heq hpxy by auto
qed

text \<open>Periodicity of the covering map: p(x + n) = p(x) for integer n.
  (Proved from cos_add/sin_add + cos_int_2pin/sin_int_2pin.)\<close>
lemma top1_R_to_S1_int_shift_early:
  "top1_R_to_S1 (x + of_int n) = top1_R_to_S1 x"
proof -
  have hc: "cos ((2 * pi) * of_int n) = 1" by (rule cos_int_2pin)
  have hs: "sin ((2 * pi) * of_int n) = 0" by (rule sin_int_2pin)
  have hexp: "2 * pi * (x + of_int n) = 2 * pi * x + (2 * pi) * of_int n"
    by (simp add: algebra_simps)
  show ?thesis unfolding top1_R_to_S1_def
    by (simp add: hexp cos_add sin_add hc hs)
qed

lemma top1_S1_arc_E_preimage:
  "{x. top1_R_to_S1 x \<in> top1_S1_arc_E} = (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
proof (intro set_eqI iffI)
  fix x :: real
  assume hx: "x \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}"
  hence hcos: "cos (2 * pi * x) > 0"
    unfolding top1_R_to_S1_def top1_S1_arc_E_def by auto
  \<comment> \<open>cos(2\<pi>x) > 0 implies x \<in> (n - 1/4, n + 1/4) for n = round(x).
     Uses cos\_monotone\_0\_pi: cos strictly decreasing on [0, \<pi>].\<close>
  show "x \<in> (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
  proof -
    let ?n = "\<lfloor>x + 1/2\<rfloor>"
    have hfloor: "of_int ?n \<le> x + 1/2" by (rule of_int_floor_le)
    have hfloor_ub: "x + 1/2 < of_int ?n + 1" using floor_correct[of "x + 1/2"] by linarith
    hence hdiff_lb: "of_int ?n - 1/2 \<le> x" and hdiff_ub: "x < of_int ?n + 1/2"
      by linarith+
    \<comment> \<open>Shift by periodicity: cos(2\<pi>(x-n)) = cos(2\<pi>x) > 0.\<close>
    have hcos_shift: "cos (2 * pi * (x - of_int ?n)) > 0"
    proof -
      let ?\<theta> = "2 * pi * (x - of_int ?n)"
      let ?k = "(2 * pi) * of_int ?n"
      have "2 * pi * x = ?\<theta> + ?k" by (simp add: algebra_simps)
      hence "cos (2 * pi * x) = cos (?\<theta> + ?k)" by simp
      also have "\<dots> = cos ?\<theta> * cos ?k - sin ?\<theta> * sin ?k" by (rule cos_add)
      also have "\<dots> = cos ?\<theta>" by (simp add: cos_int_2pin sin_int_2pin)
      finally show ?thesis using hcos by simp
    qed
    let ?\<theta> = "2 * pi * (x - of_int ?n)"
    have hpi: "0 < pi" by (rule pi_gt_zero)
    have h2pi: "0 < 2 * pi" using hpi by linarith
    have hdiff_lb_strict: "x - of_int ?n > -(1/2)"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n > -(1/2)"
      hence "x - of_int ?n \<le> -(1/2)" by simp
      hence "x - of_int ?n = -(1/2)" using hdiff_lb by linarith
      hence "?\<theta> = -pi" using hpi by (simp add: field_simps)
      hence "cos ?\<theta> = -1" by simp
      thus False using hcos_shift by linarith
    qed
    have h\<theta>_lb: "?\<theta> > -pi"
    proof -
      have "-(pi) = 2 * pi * (-(1/2))" by (simp add: field_simps)
      also have "\<dots> < 2 * pi * (x - of_int ?n)"
        using hdiff_lb_strict h2pi by (intro mult_strict_left_mono) auto
      finally show ?thesis .
    qed
    have h\<theta>_ub: "?\<theta> < pi"
    proof -
      have "2 * pi * (x - of_int ?n) < 2 * pi * (1/2)"
        using hdiff_ub h2pi by (intro mult_strict_left_mono) linarith+
      also have "\<dots> = pi" by (simp add: field_simps)
      finally show ?thesis .
    qed
    \<comment> \<open>If \<theta> \<ge> \<pi>/2: cos(\<theta>) \<le> cos(\<pi>/2) = 0 by monotonicity. Contradiction.\<close>
    have hdiff_lt: "x - of_int ?n < 1/4"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n < 1/4"
      hence hge: "x - of_int ?n \<ge> 1/4" by simp
      hence "?\<theta> \<ge> pi / 2"
      proof -
        have "pi / 2 = 2 * pi * (1/4)" by (simp add: field_simps)
        also have "\<dots> \<le> 2 * pi * (x - of_int ?n)"
          using hge h2pi by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      hence "cos ?\<theta> \<le> cos (pi / 2)"
        using h\<theta>_ub by (intro cos_monotone_0_pi_le[of "pi/2" ?\<theta>]) (auto simp: pi_ge_zero)
      hence "cos ?\<theta> \<le> 0" by simp
      thus False using hcos_shift by linarith
    qed
    \<comment> \<open>If \<theta> \<le> -\<pi>/2: cos(\<theta>) = cos(-\<theta>) \<le> 0. Contradiction.\<close>
    have hdiff_gt: "x - of_int ?n > -(1/4)"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n > -(1/4)"
      hence hle: "x - of_int ?n \<le> -(1/4)" by simp
      hence "?\<theta> \<le> -(pi / 2)"
      proof -
        have "2 * pi * (x - of_int ?n) \<le> 2 * pi * (-(1/4))"
          using hle h2pi by (intro mult_left_mono) auto
        also have "\<dots> = -(pi / 2)" by (simp add: field_simps)
        finally show ?thesis .
      qed
      hence "-?\<theta> \<ge> pi / 2" by linarith
      moreover have "-?\<theta> \<le> pi" using h\<theta>_lb by linarith
      ultimately have "cos (-?\<theta>) \<le> cos (pi/2)"
        by (intro cos_monotone_0_pi_le[of "pi/2" "-?\<theta>"]) (auto simp: pi_ge_zero)
      hence "cos (-?\<theta>) \<le> 0" by simp
      hence "cos ?\<theta> \<le> 0" by simp
      thus False using hcos_shift by linarith
    qed
    have "of_int ?n - 1/4 < x" using hdiff_gt by linarith
    moreover have "x < of_int ?n + 1/4" using hdiff_lt by linarith
    ultimately show ?thesis by auto
  qed
next
  fix x :: real
  assume hx: "x \<in> (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
  then obtain n :: int where hn: "of_int n - 1/4 < x" "x < of_int n + 1/4" by auto
  \<comment> \<open>x \<in> (n - 1/4, n + 1/4) implies cos(2\<pi>x) > 0.\<close>
  have hcos: "cos (2 * pi * x) > 0"
  proof -
    have hdiff_lb: "- (1/4) < x - of_int n" using hn(1) by linarith
    have hdiff_ub: "x - of_int n < 1/4" using hn(2) by linarith
    have hpi_pos: "(0::real) < 2 * pi" using pi_gt_zero by linarith
    have hd: "- (pi / 2) < 2 * pi * (x - of_int n)"
    proof -
      have "-(pi/2) = 2 * pi * (-(1/4))" by (simp add: field_simps)
      also have "\<dots> < 2 * pi * (x - of_int n)"
        using hdiff_lb hpi_pos by (intro mult_strict_left_mono) auto
      finally show ?thesis .
    qed
    have hu: "2 * pi * (x - of_int n) < pi / 2"
    proof -
      have "2 * pi * (x - of_int n) < 2 * pi * (1/4)"
        using hdiff_ub hpi_pos by (intro mult_strict_left_mono) auto
      also have "\<dots> = pi/2" by (simp add: field_simps)
      finally show ?thesis .
    qed
    have "cos (2 * pi * (x - of_int n)) > 0"
      by (rule cos_gt_zero_pi[OF hd hu])
    moreover have "cos (2 * pi * x) = cos (2 * pi * (x - of_int n))"
    proof -
      let ?\<theta> = "2 * pi * (x - of_int n)"
      let ?k = "(2 * pi) * of_int n"
      have h1: "2 * pi * x = ?\<theta> + ?k" by (simp add: algebra_simps)
      have h2: "cos (?\<theta> + ?k) = cos ?\<theta> * cos ?k - sin ?\<theta> * sin ?k"
        by (rule cos_add)
      have h3: "cos ?k = 1" by (rule cos_int_2pin)
      have h4: "sin ?k = 0" by (rule sin_int_2pin)
      show ?thesis unfolding h1 h2 h3 h4 by simp
    qed
    ultimately show ?thesis by simp
  qed
  have hcirc: "cos (2 * pi * x)^2 + sin (2 * pi * x)^2 = 1" by (simp add: sin_squared_eq)
  show "x \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}"
    unfolding top1_R_to_S1_def top1_S1_arc_E_def using hcos hcirc by auto
qed

text \<open>Continuity transfer for continuous_on S (partial functions).\<close>
lemma top1_continuous_map_on_subspace_open_sets_on:
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
      and hcont: "continuous_on S f"
  shows "top1_continuous_map_on S (subspace_topology UNIV top1_open_sets S)
                               T (subspace_topology UNIV top1_open_sets T) f"
proof -
  have "\<forall>V\<in>subspace_topology UNIV top1_open_sets T.
      {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
  proof
    fix V assume "V \<in> subspace_topology UNIV top1_open_sets T"
    then obtain U where hUo: "open U" and hVeq: "V = T \<inter> U"
      unfolding subspace_topology_def top1_open_sets_def by (by100 auto)
    have hcoi: "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S)"
      using iffD1[OF continuous_on_open_invariant] hcont by (by100 blast)
    have "\<exists>A. open A \<and> A \<inter> S = f -` U \<inter> S" using hcoi hUo by (by100 blast)
    then obtain W where hWo: "open W" and hWeq: "W \<inter> S = f -` U \<inter> S" by (by100 blast)
    have "{x \<in> S. f x \<in> V} = S \<inter> W"
      unfolding hVeq using hmap hWeq by (by100 auto)
    thus "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def top1_open_sets_def using hWo by (by100 blast)
  qed
  thus ?thesis unfolding top1_continuous_map_on_def using hmap by (by100 blast)
qed

theorem Theorem_53_1:
  "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
proof -
  \<comment> \<open>Munkres 53.1: p(x) = (cos 2\<pi>x, sin 2\<pi>x) is the standard covering R \<rightarrow> S^1.
     Step 1: p is continuous and surjective.\<close>
  have hp_cont: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
  proof -
    have hmap: "\<And>x::real. top1_R_to_S1 x \<in> top1_S1"
      unfolding top1_R_to_S1_def top1_S1_def by (simp add: sin_squared_eq)
    have hcont: "continuous_on UNIV top1_R_to_S1"
      unfolding top1_R_to_S1_def
      by (intro continuous_on_Pair continuous_on_compose2[OF continuous_on_cos]
              continuous_on_compose2[OF continuous_on_sin]
              continuous_on_mult continuous_on_const continuous_on_id) auto
    show ?thesis unfolding top1_S1_topology_def
      by (rule top1_continuous_map_on_R_to_R2_subspace[OF hmap hcont])
  qed
  have hp_surj: "top1_R_to_S1 ` UNIV = top1_S1"
  proof (rule set_eqI, rule iffI)
    fix p assume "p \<in> top1_R_to_S1 ` UNIV"
    then obtain x where hp: "p = top1_R_to_S1 x" by (by100 blast)
    show "p \<in> top1_S1" unfolding hp top1_R_to_S1_def top1_S1_def
      by (simp add: sin_squared_eq)
  next
    fix p assume hp: "p \<in> top1_S1"
    hence heq: "fst p ^ 2 + snd p ^ 2 = 1" unfolding top1_S1_def by (by100 simp)
    obtain \<theta> where hcos: "fst p = cos \<theta>" and hsin: "snd p = sin \<theta>"
      using sincos_total_2pi[of "fst p" "snd p"] heq by (by100 metis)
    let ?x = "\<theta> / (2 * pi)"
    have "top1_R_to_S1 ?x = (cos \<theta>, sin \<theta>)"
      unfolding top1_R_to_S1_def by (by100 simp)
    hence "top1_R_to_S1 ?x = p" using hcos hsin by (simp add: prod_eq_iff)
    thus "p \<in> top1_R_to_S1 ` UNIV" by (by100 blast)
  qed
  \<comment> \<open>Step 2: Every b \<in> S^1 has an evenly covered open neighborhood.
     Use the 4 open arcs E, N, W, S covering S^1. Each arc U_i has
     p\<inverse>(U_i) = \<Union>_n (n + open interval) — a disjoint union of sheets homeomorphic to U_i.\<close>
  \<comment> \<open>Each of the 4 arcs E,N,W,S is evenly covered. We prove arc_E; others are symmetric.\<close>
  have harc_E_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_E"
  proof -
    \<comment> \<open>arc_E is open in S^1: arc_E = S^1 \<inter> {(x,y). x > 0}.\<close>
    have harc_E_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_E"
    proof -
      have heq: "top1_S1_arc_E = top1_S1 \<inter> {p::real\<times>real. fst p > 0}"
        unfolding top1_S1_arc_E_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. fst p > 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. fst p > 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. fst p > 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    \<comment> \<open>Slices: V_n = (n - 1/4, n + 1/4) for each n \<in> Z.\<close>
    define \<V> where "\<V> = (\<lambda>n::int. {of_int n - 1/4 <..< of_int n + (1/4::real)}) ` UNIV"
    \<comment> \<open>Each slice is open.\<close>
    have hV_open: "\<forall>V\<in>\<V>. openin_on UNIV (top1_open_sets::real set set) V"
      unfolding \<V>_def openin_on_def top1_open_sets_def by (by100 auto)
    \<comment> \<open>Slices pairwise disjoint.\<close>
    have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> \<V>" "V' \<in> \<V>" "V \<noteq> V'"
      then obtain n m :: int where hV: "V = {of_int n - 1/4 <..< of_int n + 1/4}"
          and hV': "V' = {of_int m - 1/4 <..< of_int m + 1/4}" and hnm: "n \<noteq> m"
        unfolding \<V>_def by blast
      have "of_int n - of_int m \<ge> (1::real) \<or> of_int m - of_int n \<ge> (1::real)"
        using hnm by linarith
      hence hgap: "of_int m + 1/4 \<le> of_int n - (1/4::real) \<or> of_int n + 1/4 \<le> of_int m - (1/4::real)"
      proof
        assume h: "of_int n - of_int m \<ge> (1::real)"
        hence "of_int m + 1/4 \<le> of_int n - (1/4::real)" by (by100 linarith)
        thus ?thesis by (by100 blast)
      next
        assume h: "of_int m - of_int n \<ge> (1::real)"
        hence "of_int n + 1/4 \<le> of_int m - (1/4::real)" by (by100 linarith)
        thus ?thesis by (by100 blast)
      qed
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence "of_int n - 1/4 < x" "x < of_int n + 1/4"
              "of_int m - 1/4 < x" "x < of_int m + 1/4"
          unfolding hV hV' by (by100 auto)+
        thus False using hgap by (by100 linarith)
      qed
    qed
    \<comment> \<open>Union = preimage.\<close>
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_E} = \<Union>\<V>"
      unfolding \<V>_def using top1_S1_arc_E_preimage by (by100 auto)
    \<comment> \<open>p homeomorphism on each slice.\<close>
    have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
        top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
    proof
      fix V assume hVmem: "V \<in> \<V>"
      then obtain n :: int where hVeq: "V = {of_int n - 1/4 <..< of_int n + (1/4::real)}"
        unfolding \<V>_def by (by100 blast)
      have hpV: "\<forall>x\<in>V. top1_R_to_S1 x \<in> top1_S1_arc_E"
        using hV_union hVmem by (by100 blast)
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have harc_sub: "top1_S1_arc_E \<subseteq> top1_S1"
        unfolding top1_S1_arc_E_def top1_S1_def by (by100 auto)
      have hpV_surj: "top1_R_to_S1 ` V = top1_S1_arc_E"
      proof (intro equalityI subsetI)
        fix y assume "y \<in> top1_R_to_S1 ` V"
        thus "y \<in> top1_S1_arc_E" using hpV by (by100 blast)
      next
        fix y assume hy: "y \<in> top1_S1_arc_E"
        \<comment> \<open>y is in the preimage of arc_E, so y = p(t) for some t \<in> (m-1/4, m+1/4).\<close>
        have "y \<in> top1_S1" using hy harc_sub by (by100 blast)
        hence "y \<in> top1_R_to_S1 ` UNIV" using hp_surj by (by100 blast)
        then obtain t where hpt: "top1_R_to_S1 t = y" by (by100 blast)
        hence "t \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}" using hy by (by100 simp)
        hence "t \<in> (\<Union>m::int. {of_int m - 1/4 <..< of_int m + 1/4})"
          using top1_S1_arc_E_preimage by (by100 blast)
        then obtain m :: int where "t \<in> {of_int m - 1/4 <..< of_int m + 1/4}" by (by100 blast)
        \<comment> \<open>Shift by periodicity: t' = t + (n - m) is in V_n and p(t') = p(t) = y.\<close>
        let ?t' = "t + of_int (n - m)"
        have htm_lb: "of_int m - 1/4 < t" and htm_ub: "t < of_int m + 1/4"
          using \<open>t \<in> {of_int m - 1/4 <..< of_int m + 1/4}\<close> by (by100 simp)+
        hence "of_int n - 1/4 < t + of_int (n - m)" "t + of_int (n - m) < of_int n + 1/4"
          by (by100 linarith)+
        hence ht'V: "?t' \<in> V" unfolding hVeq by (by100 auto)
        have "top1_R_to_S1 ?t' = top1_R_to_S1 t"
        proof -
          show ?thesis unfolding top1_R_to_S1_def
            using cos_int_2pin[of "n - m"] sin_int_2pin[of "n - m"]
            by (simp add: distrib_left cos_add sin_add)
        qed
        hence "top1_R_to_S1 ?t' = y" using hpt by (by100 simp)
        thus "y \<in> top1_R_to_S1 ` V" using ht'V by (by100 blast)
      qed
      have hpV_inj: "inj_on top1_R_to_S1 V"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> V" and hy: "y \<in> V"
            and heq: "top1_R_to_S1 x = top1_R_to_S1 y"
        \<comment> \<open>x, y \<in> (n-1/4, n+1/4), so 2\<pi>x, 2\<pi>y \<in> (2\<pi>n-\<pi>/2, 2\<pi>n+\<pi>/2).
           sin injective on this interval \<Rightarrow> 2\<pi>x = 2\<pi>y \<Rightarrow> x = y.\<close>
        have "sin (2 * pi * x) = sin (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)
        moreover have "cos (2 * pi * x) = cos (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)
        moreover have "cos (2 * pi * x) > 0"
        proof -
          have "x \<in> {of_int n - 1/4 <..< of_int n + 1/4}" using hx hVeq by (by100 blast)
          hence "top1_R_to_S1 x \<in> top1_S1_arc_E" using hpV hx by (by100 blast)
          thus ?thesis unfolding top1_R_to_S1_def top1_S1_arc_E_def by (by100 simp)
        qed
        \<comment> \<open>sin \<theta>1 = sin \<theta>2 \<and> cos \<theta>1 = cos \<theta>2 \<Rightarrow> \<exists>k. \<theta>1 = \<theta>2 + 2k\<pi>.\<close>
        ultimately obtain k :: int where "2*pi*x = 2*pi*y + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        hence "2*pi*x - 2*pi*y = 2*pi * of_int k" by (by100 linarith)
        hence "2*pi * (x - y) = 2*pi * of_int k" by (simp add: algebra_simps)
        hence "x - y = of_int k" using pi_gt_zero by (by100 simp)
        \<comment> \<open>x, y \<in> (n-1/4, n+1/4), so |x-y| < 1/2 < 1. Hence k = 0.\<close>
        moreover have "of_int n - 1/4 < x" "x < of_int n + 1/4"
            "of_int n - 1/4 < y" "y < of_int n + 1/4"
          using hx hy unfolding hVeq by (by100 auto)+
        hence "\<bar>x - y\<bar> < 1/2" by (by100 linarith)
        hence "k = 0" using \<open>x - y = of_int k\<close> by (by100 linarith)
        ultimately show "x = y" by (by100 linarith)
      qed
      have hinv_cont: "top1_continuous_map_on top1_S1_arc_E
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)
          V (subspace_topology UNIV top1_open_sets V) (inv_into V top1_R_to_S1)"
      proof -
        define inv_fn :: "real \<times> real \<Rightarrow> real"
          where "inv_fn \<equiv> \<lambda>p. arctan (snd p / fst p) / (2 * pi) + of_int n"
        have hinv_co: "continuous_on top1_S1_arc_E inv_fn"
          unfolding inv_fn_def top1_S1_arc_E_def
          by (intro continuous_on_add continuous_on_const
              continuous_on_divide[OF _ continuous_on_const]
              continuous_on_compose2[OF continuous_on_arctan _ subset_UNIV]
              continuous_on_divide continuous_on_snd continuous_on_fst) (by100 auto)+
        have hinv_range: "\<And>p. p \<in> top1_S1_arc_E \<Longrightarrow> inv_fn p \<in> V"
        proof -
          fix p assume hp: "p \<in> top1_S1_arc_E"
          hence hx_pos: "fst p > 0" unfolding top1_S1_arc_E_def by (by100 auto)
          have "arctan (snd p / fst p) \<in> {-pi/2 <..< pi/2}"
            using arctan_bounded[of "snd p / fst p"] by (by100 simp)
          hence "arctan (snd p / fst p) / (2*pi) \<in> {-1/4 <..< 1/4}"
            using pi_gt_zero by (simp add: field_simps)
          thus "inv_fn p \<in> V" unfolding inv_fn_def hVeq by (by100 auto)
        qed
        have hinv_agree: "\<forall>p\<in>top1_S1_arc_E. inv_into V top1_R_to_S1 p = inv_fn p"
        proof
          fix p assume hp: "p \<in> top1_S1_arc_E"
          have hx_pos: "fst p > 0" using hp unfolding top1_S1_arc_E_def by (by100 auto)
          have hcirc: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_arc_E_def by (by100 auto)
          have hinV: "inv_fn p \<in> V" using hinv_range[OF hp] .
          \<comment> \<open>Show p(inv_fn p) = p: cos(arctan(y/x)) = x and sin(arctan(y/x)) = y for x>0, x^2+y^2=1.\<close>
          have hsqrt: "sqrt (1 + (snd p / fst p)\<^sup>2) = 1 / fst p"
          proof -
            have "1 + (snd p / fst p)^2 = ((fst p)^2 + (snd p)^2) / (fst p)^2"
              using hx_pos by (simp add: field_simps power2_eq_square)
            also have "\<dots> = 1 / (fst p)^2" using hcirc by (by100 simp)
            finally have "sqrt (1 + (snd p / fst p)^2) = sqrt (1 / (fst p)^2)" by (by100 simp)
            also have "\<dots> = 1 / fst p" using hx_pos by (simp add: real_sqrt_divide)
            finally show ?thesis .
          qed
          have hcos: "cos (arctan (snd p / fst p)) = fst p"
            using cos_arctan[of "snd p / fst p"] hsqrt hx_pos by (by100 simp)
          have hsin: "sin (arctan (snd p / fst p)) = snd p"
            using sin_arctan[of "snd p / fst p"] hsqrt hx_pos by (by100 simp)
          have "top1_R_to_S1 (inv_fn p) = p"
            unfolding top1_R_to_S1_def inv_fn_def
            using hcos hsin by (simp add: distrib_left cos_add sin_add cos_int_2pin sin_int_2pin
                                          prod_eq_iff)
          thus "inv_into V top1_R_to_S1 p = inv_fn p"
            using inv_into_f_eq[OF hpV_inj hinV] by (by100 simp)
        qed
        have harc_eq: "subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_E"
          unfolding top1_S1_topology_def
          using subspace_topology_trans[OF harc_sub]
          by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
        have "top1_continuous_map_on top1_S1_arc_E
            (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_E)
            V (subspace_topology UNIV (top1_open_sets :: real set set) V) inv_fn"
          by (rule top1_continuous_map_on_subspace_open_sets_on[OF hinv_range hinv_co])
        hence hinv_fn_cont: "top1_continuous_map_on top1_S1_arc_E
            (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)
            V (subspace_topology UNIV top1_open_sets V) inv_fn"
          unfolding harc_eq .
        have "\<forall>p\<in>top1_S1_arc_E. inv_fn p = inv_into V top1_R_to_S1 p"
          using hinv_agree by (by100 auto)
        thus ?thesis by (rule top1_continuous_map_on_agree'[OF hinv_fn_cont])
      qed
      have hbij: "bij_betw top1_R_to_S1 V top1_S1_arc_E"
        unfolding bij_betw_def using hpV_inj hpV_surj by (by100 blast)
      have hTV: "is_topology_on V (subspace_topology UNIV top1_open_sets V)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV hV_sub])
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTarc: "is_topology_on top1_S1_arc_E
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use harc_sub in \<open>by100 blast\<close>)
      have hp_V_img: "top1_R_to_S1 ` V \<subseteq> top1_S1_arc_E"
        using hpV by (by100 blast)
      have hp_V_arc: "top1_continuous_map_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
        by (rule top1_continuous_map_on_codomain_shrink[OF
              top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV_sub]
              hp_V_img harc_sub])
      show "top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
        unfolding top1_homeomorphism_on_def
        using hTV hTarc hbij hp_V_arc hinv_cont by (by100 blast)
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_E_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  \<comment> \<open>Arcs N, W, S: symmetric to arc_E with adapted coordinates.\<close>
  have harc_N_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_N"
  proof -
    \<comment> \<open>Arc N = {(x,y) \<in> S^1 | y > 0}. Preimage under p: those x with sin(2\<pi>x) > 0,
       i.e., x \<in> (n, n+1/2) for each integer n. Each slice maps homeomorphically to arc_N.
       Inverse: given (a,b) with b > 0, x = arcsin(b)/(2\<pi>) + n (or arctan-based).\<close>
    have harc_N_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_N"
    proof -
      have heq: "top1_S1_arc_N = top1_S1 \<inter> {p::real\<times>real. snd p > 0}"
        unfolding top1_S1_arc_N_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. snd p > 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. snd p > 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. snd p > 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n < x \<and> x < of_int n + 1/2}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        by (by100 blast)
      have "V = {of_int n <..< of_int n + 1/2}" using hV by (by100 auto)
      moreover have "open {of_int n <..< of_int n + (1/2::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      then obtain n where hV: "V = {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m < x \<and> x < of_int m + 1/2}"
        using \<open>V' \<in> ?\<V>\<close> by (by100 blast)
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence hx1: "of_int n < x" and hx2: "x < of_int n + (1/2::real)"
            and hx3: "of_int m < x" and hx4: "x < of_int m + (1/2::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N} = \<Union>?\<V>"
    proof (intro set_eqI iffI)
      fix x :: real
      assume hx: "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N}"
      hence hsin: "sin (2 * pi * x) > 0"
        unfolding top1_R_to_S1_def top1_S1_arc_N_def by (by100 auto)
      \<comment> \<open>sin(2\<pi>x) > 0 iff 2\<pi>x \<in> (2k\<pi>, (2k+1)\<pi>) iff x \<in> (k, k + 1/2) for some integer k.\<close>
      \<comment> \<open>Let n = floor(x). Then x - n \<in> [0,1) and sin(2\<pi>(x-n)) = sin(2\<pi>x) > 0.
         On [0,1), sin(2\<pi>t) > 0 iff t \<in> (0, 1/2). So x \<in> (n, n+1/2).\<close>
      define n where "n = \<lfloor>x\<rfloor>"
      have hn_le: "of_int n \<le> x" and hx_lt: "x < of_int n + 1"
        unfolding n_def by linarith+
      have hfrac: "x - of_int n \<ge> 0" "x - of_int n < 1" using hn_le hx_lt by linarith+
      \<comment> \<open>sin(2\<pi>(x-n)) = sin(2\<pi>x) by periodicity.\<close>
      have hshift: "sin (2 * pi * (x - of_int n)) = sin (2 * pi * x)"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      \<comment> \<open>sin(2\<pi>(x-n)) > 0 with x-n \<in> [0,1). On [0,1): sin(2\<pi>t) > 0 iff t \<in> (0, 1/2).
         sin(2\<pi>t) = 0 at t=0 and t=1/2; sin(2\<pi>t) > 0 on (0, 1/2); sin(2\<pi>t) < 0 on (1/2, 1).\<close>
      have hfrac_pos: "sin (2 * pi * (x - of_int n)) > 0" using hsin hshift by (by100 linarith)
      have hfrac_gt: "x - of_int n > 0"
      proof (rule ccontr)
        assume "\<not> x - of_int n > 0"
        hence "x - of_int n = 0" using hfrac by (by100 linarith)
        hence "sin (2 * pi * (x - of_int n)) = 0" by simp
        thus False using hfrac_pos by (by100 linarith)
      qed
      have hfrac_lt: "x - of_int n < 1/2"
      proof (rule ccontr)
        assume "\<not> x - of_int n < 1/2"
        hence hge: "x - of_int n \<ge> 1/2" by (by100 linarith)
        show False
        proof (cases "x - of_int n = 1/2")
          case True
          have "x - of_int n = 1/2" using True .
          hence h12: "x - of_int n = 1/2" .
          have "2 * pi * (x - of_int n) = 2 * pi * (1/2::real)" using h12 by simp
          hence "sin (2 * pi * (x - of_int n)) = sin (pi * (2 * (1/2)))" by (simp add: algebra_simps)
          also have "pi * (2 * (1/2::real)) = pi" by simp
          also have "sin pi = 0" by simp
          finally have "sin (2 * pi * (x - of_int n)) = 0" .
          thus False using hfrac_pos by (by100 linarith)
        next
          case False
          hence hgt: "x - of_int n > 1/2" using hge by (by100 linarith)
          \<comment> \<open>On (1/2, 1), sin(2\<pi>t) < 0.\<close>
          have hpi_lt: "pi < 2 * pi * (x - of_int n)"
          proof -
            have "pi = pi * (2 * (1/2::real))" by simp
            also have "\<dots> = 2 * pi * (1/2::real)" by (simp add: algebra_simps)
            also have "\<dots> < 2 * pi * (x - of_int n)"
              using hgt pi_gt_zero by (by100 simp)
            finally show ?thesis .
          qed
          have h2pi_gt: "2 * pi * (x - of_int n) < 2 * pi"
          proof -
            have "2 * pi * (x - of_int n) < 2 * pi * 1"
              using hfrac pi_gt_zero by (by100 simp)
            thus ?thesis by simp
          qed
          have "sin (2 * pi * (x - of_int n)) < 0"
            by (rule sin_lt_zero[OF hpi_lt h2pi_gt])
          thus False using hfrac_pos by (by100 linarith)
        qed
      qed
      have "x \<in> {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        using hfrac_gt hfrac_lt by (by100 simp)
      thus "x \<in> \<Union>?\<V>" by (by100 blast)
    next
      fix x :: real
      assume "x \<in> \<Union>?\<V>"
      then obtain n :: int where "of_int n < x" "x < of_int n + (1/2::real)" by (by100 auto)
      have hpi: "pi > 0" by (rule pi_gt_zero)
      hence "0 < 2 * pi * x - 2 * pi * of_int n"
        using \<open>of_int n < x\<close> by (by100 simp)
      moreover have "2 * pi * x - 2 * pi * of_int n < pi"
      proof -
        have "2 * pi * x < 2 * pi * (of_int n + 1/2)"
          using \<open>x < of_int n + (1/2::real)\<close> hpi by (by100 simp)
        also have "\<dots> = 2 * pi * of_int n + pi" by (simp add: algebra_simps)
        finally show ?thesis by (by100 linarith)
      qed
      ultimately have hsin: "sin (2 * pi * x - 2 * of_int n * pi) > 0"
        by (intro sin_gt_zero) (simp add: algebra_simps)+
      \<comment> \<open>sin(2\<pi>x) = sin(2\<pi>(x-n)) > 0 from hsin and periodicity.\<close>
      have hshift: "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
        using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
      have "sin (2 * pi * x) = sin (2 * pi * (x - of_int n))"
      proof -
        have "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" using hshift by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      also have "\<dots> = sin (2 * pi * x - 2 * of_int n * pi)"
        by (simp add: algebra_simps)
      finally have "sin (2 * pi * x) > 0" using hsin by (by100 linarith)
      moreover have "cos (2 * pi * x) ^ 2 + sin (2 * pi * x) ^ 2 = 1" by (rule sin_cos_squared_add2)
      ultimately show "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N}"
        unfolding top1_R_to_S1_def top1_S1_arc_N_def by (by100 auto)
    qed
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_N (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N) top1_R_to_S1"
      sorry
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_N_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have harc_W_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_W"
  proof -
    \<comment> \<open>Arc W = {(x,y) \<in> S^1 | x < 0}. Preimage: cos(2\<pi>x) < 0, i.e., x \<in> (n+1/4, n+3/4).
       Each slice maps homeomorphically to arc_W.\<close>
    have harc_W_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_W"
    proof -
      have heq: "top1_S1_arc_W = top1_S1 \<inter> {p::real\<times>real. fst p < 0}"
        unfolding top1_S1_arc_W_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. fst p < 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. fst p < 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. fst p < 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}"
        by (by100 blast)
      have "V = {of_int n + 1/4 <..< of_int n + 3/4}" using hV by (by100 auto)
      moreover have "open {of_int n + 1/4 <..< of_int n + (3/4::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      obtain n where hV: "V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m + 1/4 < x \<and> x < of_int m + 3/4}"
        using \<open>V' \<in> ?\<V>\<close> by auto
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence "of_int n + (1/4::real) < x" "x < of_int n + (3/4::real)"
            "of_int m + (1/4::real) < x" "x < of_int m + (3/4::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_W} = \<Union>?\<V>"
      sorry \<comment> \<open>cos(2\<pi>x) < 0 iff x \<in> (n+1/4, n+3/4): same analysis as arc_N with cos.\<close>
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_W (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W) top1_R_to_S1"
      sorry
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_W_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have harc_S_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_S"
  proof -
    \<comment> \<open>Arc S = {(x,y) \<in> S^1 | y < 0}. Preimage: sin(2\<pi>x) < 0, i.e., x \<in> (n+1/2, n+1).
       Each slice maps homeomorphically to arc_S.\<close>
    have harc_S_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_S"
    proof -
      have heq: "top1_S1_arc_S = top1_S1 \<inter> {p::real\<times>real. snd p < 0}"
        unfolding top1_S1_arc_S_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. snd p < 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. snd p < 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. snd p < 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        by (by100 blast)
      have "V = {of_int n + 1/2 <..< of_int n + 1}" using hV by (by100 auto)
      moreover have "open {of_int n + 1/2 <..< of_int n + (1::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      obtain n where hV: "V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m + 1/2 < x \<and> x < of_int m + 1}"
        using \<open>V' \<in> ?\<V>\<close> by auto
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence "of_int n + (1/2::real) < x" "x < of_int n + (1::real)"
            "of_int m + (1/2::real) < x" "x < of_int m + (1::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S} = \<Union>?\<V>"
    proof (intro set_eqI iffI)
      fix x :: real
      assume hx: "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S}"
      hence hsin: "sin (2 * pi * x) < 0"
        unfolding top1_R_to_S1_def top1_S1_arc_S_def by (by100 auto)
      define n where "n = \<lfloor>x\<rfloor>"
      have hn_le: "of_int n \<le> x" and hx_lt: "x < of_int n + 1"
        unfolding n_def by linarith+
      have hfrac: "x - of_int n \<ge> 0" "x - of_int n < 1" using hn_le hx_lt by linarith+
      have hshift: "sin (2 * pi * (x - of_int n)) = sin (2 * pi * x)"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have hfrac_neg: "sin (2 * pi * (x - of_int n)) < 0" using hsin hshift by (by100 linarith)
      \<comment> \<open>sin(2\<pi>t) < 0 for t \<in> (1/2, 1): sin = 0 at 0 and 1/2, > 0 on (0, 1/2), < 0 on (1/2, 1).\<close>
      have hfrac_gt: "x - of_int n > 1/2"
      proof (rule ccontr)
        assume "\<not> x - of_int n > 1/2"
        hence hle: "x - of_int n \<le> 1/2" by (by100 linarith)
        show False
        proof (cases "x - of_int n = 0")
          case True thus False using hfrac_neg by simp
        next
          case False
          hence hgt0: "x - of_int n > 0" using hfrac by (by100 linarith)
          show False
          proof (cases "x - of_int n = 1/2")
            case True
            have "x - of_int n = 1/2" using True .
            have "x - of_int n = 1/2" using True .
            hence "sin (2 * pi * (x - of_int n)) = sin (pi * (2 * (1/2)))"
              by (simp add: algebra_simps)
            also have "pi * (2 * (1/2::real)) = pi" by simp
            also have "sin pi = 0" by simp
            finally have "sin (2 * pi * (x - of_int n)) = 0" .
            hence "sin (2 * pi * (x - of_int n)) = 0" by simp
            thus False using hfrac_neg by (by100 linarith)
          next
            case False
            hence hlt12: "x - of_int n < 1/2" using hle by (by100 linarith)
            have hpi: "pi > 0" by (rule pi_gt_zero)
            have "0 < 2 * pi * (x - of_int n)" using hgt0 hpi by (by100 simp)
            moreover have "2 * pi * (x - of_int n) < pi"
            proof -
              have "2 * pi * (x - of_int n) < 2 * pi * (1/2::real)" using hlt12 hpi by (by100 simp)
              also have "\<dots> = pi * (2 * (1/2::real))" by (simp add: algebra_simps)
              also have "\<dots> = pi" by simp
              finally show ?thesis .
            qed
            ultimately have "sin (2 * pi * (x - of_int n)) > 0" by (rule sin_gt_zero)
            thus False using hfrac_neg by (by100 linarith)
          qed
        qed
      qed
      have "x \<in> {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        using hfrac_gt hfrac by (by100 simp)
      thus "x \<in> \<Union>?\<V>" by (by100 blast)
    next
      fix x :: real assume "x \<in> \<Union>?\<V>"
      then obtain n :: int where hn1: "of_int n + (1/2::real) < x" and hn2: "x < of_int n + 1"
        by (by100 auto)
      have hpi: "pi > 0" by (rule pi_gt_zero)
      have hpi_lt: "pi < 2 * pi * (x - of_int n)"
      proof -
        have "pi = pi * (2 * (1/2::real))" by simp
        also have "\<dots> = 2 * pi * (1/2::real)" by (simp add: algebra_simps)
        also have "\<dots> < 2 * pi * (x - of_int n)" using hn1 hpi by (by100 simp)
        finally show ?thesis .
      qed
      have h2pi_gt: "2 * pi * (x - of_int n) < 2 * pi"
      proof -
        have "2 * pi * (x - of_int n) < 2 * pi * 1" using hn2 hpi by (by100 simp)
        thus ?thesis by simp
      qed
      have hsin_neg: "sin (2 * pi * (x - of_int n)) < 0"
        by (rule sin_lt_zero[OF hpi_lt h2pi_gt])
      have hshift: "sin (2 * pi * x) = sin (2 * pi * (x - of_int n))"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have "sin (2 * pi * x) < 0" using hsin_neg hshift by (by100 linarith)
      moreover have "cos (2 * pi * x) ^ 2 + sin (2 * pi * x) ^ 2 = 1"
        by (rule sin_cos_squared_add2)
      ultimately show "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S}"
        unfolding top1_R_to_S1_def top1_S1_arc_S_def by (by100 auto)
    qed
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_S (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S) top1_R_to_S1"
      sorry
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_S_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have hp_evenly: "\<forall>b\<in>top1_S1. \<exists>U. openin_on top1_S1 top1_S1_topology U \<and> b \<in> U
      \<and> top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
  proof
    fix b assume hb: "b \<in> top1_S1"
    have "b \<in> top1_S1_arc_E \<or> b \<in> top1_S1_arc_W \<or> b \<in> top1_S1_arc_N \<or> b \<in> top1_S1_arc_S"
      using top1_S1_arcs_cover hb by (by100 blast)
    thus "\<exists>U. openin_on top1_S1 top1_S1_topology U \<and> b \<in> U
        \<and> top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
    proof (elim disjE)
      assume hb': "b \<in> top1_S1_arc_E"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_E"
        using harc_E_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_E_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_W"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_W"
        using harc_W_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_W_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_N"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_N"
        using harc_N_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_N_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_S"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_S"
        using harc_S_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_S_ec by (by100 blast)
    qed
  qed
  show ?thesis unfolding top1_covering_map_on_def
  proof (intro conjI)
    show "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      by (rule hp_cont)
    show "top1_R_to_S1 ` UNIV = top1_S1" by (rule hp_surj)
    show "\<forall>b\<in>top1_S1. \<exists>U. b \<in> U \<and>
        top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
    proof
      fix b assume "b \<in> top1_S1"
      then obtain U where "openin_on top1_S1 top1_S1_topology U" "b \<in> U"
          "top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
        using hp_evenly by (by100 blast)
      thus "\<exists>U. b \<in> U \<and>
          top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
        by (by100 blast)
    qed
  qed
qed

(** from \<S>53 Theorem 53.2: restriction of a covering map to a subspace is a covering map.
    Uses strict topology: subspace of strict is strict. **)
theorem Theorem_53_2:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "B0 \<subseteq> B"
      and "E0 = {e\<in>E. p e \<in> B0}"
  shows "top1_covering_map_on E0 (subspace_topology E TE E0)
    B0 (subspace_topology B TB B0) p"
proof -
  \<comment> \<open>Munkres 53.2: restrict covering to subspace.\<close>
  have hE0sub: "E0 \<subseteq> E" using assms(5) by (by100 blast)
  have hp_cont: "top1_continuous_map_on E0 (subspace_topology E TE E0)
      B0 (subspace_topology B TB B0) p"
  proof -
    have hp_E_B: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_E0_B: "top1_continuous_map_on E0 (subspace_topology E TE E0) B TB p"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF hp_E_B hE0sub])
    have himg: "p ` E0 \<subseteq> B0" using assms(5) by (by100 blast)
    show ?thesis
      by (rule top1_continuous_map_on_codomain_shrink[OF hp_E0_B himg assms(4)])
  qed
  have hp_surj: "p ` E0 = B0"
  proof (rule set_eqI, rule iffI)
    fix b assume "b \<in> p ` E0"
    thus "b \<in> B0" using assms(5) by (by100 blast)
  next
    fix b assume hb: "b \<in> B0"
    have "p ` E = B" using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    hence "\<exists>e\<in>E. p e = b" using hb assms(4) by (by100 blast)
    then obtain e where he: "e \<in> E" "p e = b" by (by100 blast)
    have "e \<in> E0" using he hb assms(5) by (by100 blast)
    thus "b \<in> p ` E0" using he by (by100 blast)
  qed
  have hp_evenly: "\<forall>b0\<in>B0. \<exists>U0. b0 \<in> U0 \<and>
      top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p U0"
  proof
    fix b0 assume hb0: "b0 \<in> B0"
    \<comment> \<open>b0 \<in> B, so there exists evenly covered U \<ni> b0 in B.\<close>
    have hb0B: "b0 \<in> B" using hb0 assms(4) by (by100 blast)
    obtain U where hU: "b0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
      using top1_covering_map_on_evenly_covered[OF assms(1) hb0B] by (by100 blast)
    \<comment> \<open>U0 = U \<inter> B0 is open in B0. The slices V\<alpha> \<inter> E0 partition p\<inverse>(U0) \<inter> E0.\<close>
    let ?U0 = "U \<inter> B0"
    have "b0 \<in> ?U0" using hU hb0 by (by100 blast)
    moreover have "top1_evenly_covered_on E0 (subspace_topology E TE E0)
        B0 (subspace_topology B TB B0) p ?U0"
    proof -
      \<comment> \<open>From hUec: U is evenly covered by slices \<V> in E.\<close>
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                           (subspace_topology B TB U) p"
        using hUec unfolding top1_evenly_covered_on_def by auto
      \<comment> \<open>Restrict slices: \<V>0 = {V \<inter> E0 | V \<in> \<V>}.\<close>
      let ?\<V>0 = "{V \<inter> E0 | V. V \<in> \<V>}"
      \<comment> \<open>Need: U \<inter> B0 is open in B0; slices are open, disjoint, partition, homeomorphic.\<close>
      show ?thesis unfolding top1_evenly_covered_on_def
      proof (intro conjI exI[of _ ?\<V>0])
        \<comment> \<open>U \<inter> B0 is open in B0.\<close>
        show "openin_on B0 (subspace_topology B TB B0) (?U0)"
        proof -
          have hUopen: "U \<in> TB"
            using hUec unfolding top1_evenly_covered_on_def openin_on_def by (by100 blast)
          have "?U0 = B0 \<inter> U" by (by100 blast)
          also have "\<dots> \<in> subspace_topology B TB B0"
            unfolding subspace_topology_def using hUopen by (by100 blast)
          finally have "?U0 \<in> subspace_topology B TB B0" .
          moreover have "?U0 \<subseteq> B0" by (by100 blast)
          ultimately show ?thesis unfolding openin_on_def by (by100 blast)
        qed
        \<comment> \<open>Restricted slices are open in E0.\<close>
        show "\<forall>V\<in>?\<V>0. openin_on E0 (subspace_topology E TE E0) V"
        proof (intro ballI)
          fix V0 assume "V0 \<in> ?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hV0eq: "V0 = V \<inter> E0" by (by100 blast)
          have hVTE: "V \<in> TE" using hV hV_open unfolding openin_on_def by (by100 blast)
          have "V0 \<in> subspace_topology E TE E0"
            unfolding subspace_topology_def hV0eq using hVTE by (by100 auto)
          moreover have "V0 \<subseteq> E0" unfolding hV0eq by (by100 blast)
          ultimately show "openin_on E0 (subspace_topology E TE E0) V0"
            unfolding openin_on_def by (by100 blast)
        qed
        \<comment> \<open>Restricted slices are pairwise disjoint.\<close>
        show "\<forall>V\<in>?\<V>0. \<forall>V'\<in>?\<V>0. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          using hV_disj by (by100 auto)
        \<comment> \<open>Restricted slices partition p⁻¹(U \<inter> B0) \<inter> E0.\<close>
        show "{x \<in> E0. p x \<in> ?U0} = \<Union>?\<V>0"
        proof (intro set_eqI iffI)
          fix x assume "x \<in> {x \<in> E0. p x \<in> ?U0}"
          hence hxE0: "x \<in> E0" and hpxU: "p x \<in> U" and hpxB0: "p x \<in> B0" by (by100 simp)+
          have hxE: "x \<in> E" using hxE0 hE0sub by (by100 blast)
          hence "x \<in> \<Union>\<V>" using hpxU hV_union by (by100 blast)
          then obtain V where hV: "V \<in> \<V>" and hxV: "x \<in> V" by (by100 blast)
          have "x \<in> V \<inter> E0" using hxV hxE0 by (by100 blast)
          thus "x \<in> \<Union>?\<V>0" using hV by (by100 blast)
        next
          fix x assume "x \<in> \<Union>?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hxVE0: "x \<in> V \<inter> E0" by (by100 blast)
          have hxE: "x \<in> E" using hxVE0 hE0sub by (by100 blast)
          have "x \<in> \<Union>\<V>" using hV hxVE0 by (by100 blast)
          hence "x \<in> {x\<in>E. p x \<in> U}" using hV_union by (by100 simp)
          hence "p x \<in> U" by (by100 simp)
          moreover have "p x \<in> B0" using hxVE0 assms(5) by (by100 simp)
          moreover have "x \<in> E0" using hxVE0 by (by100 blast)
          ultimately show "x \<in> {x \<in> E0. p x \<in> ?U0}" by (by100 simp)
        qed
        \<comment> \<open>p restricted to each slice is a homeomorphism.\<close>
        show "\<forall>V\<in>?\<V>0. top1_homeomorphism_on V (subspace_topology E0 (subspace_topology E TE E0) V)
            ?U0 (subspace_topology B0 (subspace_topology B TB B0) ?U0) p"
        proof (intro ballI)
          fix V0 assume hV0: "V0 \<in> ?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hV0eq: "V0 = V \<inter> E0" by (by100 blast)
          have hVhomeo: "top1_homeomorphism_on V (subspace_topology E TE V) U
                (subspace_topology B TB U) p"
            using hV hV_homeo by (by100 blast)
          \<comment> \<open>Subspace topology: subspace of subspace = subspace of ambient.\<close>
          have hV0_sub_V: "V0 \<subseteq> V" using hV0eq by (by100 blast)
          have hV0_sub_E0: "V0 \<subseteq> E0" using hV0eq by (by100 blast)
          have hV_sub_E: "V \<subseteq> E"
            using hV hV_open unfolding openin_on_def by (by100 blast)
          \<comment> \<open>The homeomorphism restricted to V\<inter>E0 → U\<inter>B0.\<close>
          \<comment> \<open>Subspace of subspace = subspace of ambient.\<close>
          have hTV0: "subspace_topology E0 (subspace_topology E TE E0) V0
              = subspace_topology E TE V0"
            using subspace_topology_trans[OF hV0_sub_E0] by simp
          have hU0_sub_B0: "?U0 \<subseteq> B0" by (by100 blast)
          have hTU0: "subspace_topology B0 (subspace_topology B TB B0) ?U0
              = subspace_topology B TB ?U0"
            using subspace_topology_trans[OF hU0_sub_B0] by simp
          have hV0_sub_E: "V0 \<subseteq> E" using hV0_sub_V hV_sub_E by (by100 blast)
          \<comment> \<open>V0 = V \<inter> E0 = V \<inter> p⁻¹(B0), and p|V is bijective V → U.
             So p maps V0 to U ∩ B0 bijectively.\<close>
          have hV0_pU0: "\<forall>x\<in>V0. p x \<in> ?U0"
          proof (intro ballI)
            fix x assume "x \<in> V0"
            hence "x \<in> V" and "x \<in> E0" using hV0eq by (by100 blast)+
            have "p x \<in> U" using \<open>x \<in> V\<close> hVhomeo unfolding top1_homeomorphism_on_def bij_betw_def
              by (by100 blast)
            moreover have "p x \<in> B0" using \<open>x \<in> E0\<close> assms(5) by (by100 simp)
            ultimately show "p x \<in> ?U0" by (by100 blast)
          qed
          \<comment> \<open>V0 = V \<inter> E0 and U0 = U \<inter> B0. Subspace topologies simplify.\<close>
          have hTV0': "subspace_topology E TE V0 = subspace_topology V (subspace_topology E TE V) V0"
            using subspace_topology_trans[OF hV0_sub_V] by simp
          have hU0_sub_U: "?U0 \<subseteq> U" by (by100 blast)
          have hTU0': "subspace_topology B TB ?U0 = subspace_topology U (subspace_topology B TB U) ?U0"
            using subspace_topology_trans[OF hU0_sub_U] by simp
          show "top1_homeomorphism_on V0 (subspace_topology E0 (subspace_topology E TE E0) V0)
              ?U0 (subspace_topology B0 (subspace_topology B TB B0) ?U0) p"
            unfolding hTV0 hTU0 hTV0' hTU0'
          proof -
            let ?TV = "subspace_topology E TE V" and ?TU = "subspace_topology B TB U"
            have hTV_top: "is_topology_on V ?TV"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hTU_top: "is_topology_on U ?TU"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hbij: "bij_betw p V U"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_cont: "top1_continuous_map_on V ?TV U ?TU p"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinv_cont: "top1_continuous_map_on U ?TU V ?TV (inv_into V p)"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>p maps V0 onto U0.\<close>
            have hpV0: "p ` V0 = ?U0"
            proof (intro equalityI subsetI)
              fix y assume "y \<in> p ` V0"
              then obtain x where hx: "x \<in> V0" and hpx: "y = p x" by (by100 blast)
              show "y \<in> ?U0" using hV0_pU0 hx hpx by (by100 blast)
            next
              fix y assume hy: "y \<in> ?U0"
              have "y \<in> U" using hy by (by100 blast)
              then obtain x where hx: "x \<in> V" and hpx: "p x = y"
                using hbij unfolding bij_betw_def by (by100 auto)
              have "x \<in> E" using hx hV_sub_E by (by100 blast)
              have "p x \<in> B0" using hy hpx by (by100 blast)
              hence "x \<in> E0" using \<open>x \<in> E\<close> assms(5) by (by100 simp)
              hence "x \<in> V0" using hx hV0eq by (by100 blast)
              thus "y \<in> p ` V0" using hpx by (by100 blast)
            qed
            have hbij0: "bij_betw p V0 ?U0"
              using bij_betw_subset[OF hbij hV0_sub_V hpV0] .
            \<comment> \<open>Continuity of restriction.\<close>
            have hp_cont_V0: "top1_continuous_map_on V0 (subspace_topology V ?TV V0) ?U0
                (subspace_topology U ?TU ?U0) p"
              by (rule top1_continuous_map_on_codomain_shrink[OF
                    top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV0_sub_V]])
                 (use hV0_pU0 in \<open>by100 auto\<close>)
            \<comment> \<open>Inverse maps U0 to V0.\<close>
            have hinv_V0: "\<forall>y\<in>?U0. inv_into V p y \<in> V0"
            proof
              fix y assume hy: "y \<in> ?U0"
              have "y \<in> U" using hy by (by100 blast)
              have hxV: "inv_into V p y \<in> V"
                using \<open>y \<in> U\<close> hbij unfolding bij_betw_def by (by100 auto)
              have hpx: "p (inv_into V p y) = y"
                using \<open>y \<in> U\<close> hbij unfolding bij_betw_def by (by100 auto)
              have "inv_into V p y \<in> E" using hxV hV_sub_E by (by100 blast)
              moreover have "p (inv_into V p y) \<in> B0" using hpx hy by (by100 auto)
              ultimately have "inv_into V p y \<in> E0" using assms(5) by (by100 simp)
              thus "inv_into V p y \<in> V0" using hxV hV0eq by (by100 blast)
            qed
            \<comment> \<open>inv_into V0 p = inv_into V p on U0.\<close>
            have hinv_eq: "\<forall>y\<in>?U0. inv_into V0 p y = inv_into V p y"
            proof
              fix y assume hy: "y \<in> ?U0"
              have "inv_into V p y \<in> V0" using hinv_V0 hy by (by100 blast)
              moreover have "p (inv_into V p y) = y"
                using hy hbij unfolding bij_betw_def by (by100 auto)
              moreover have "p (inv_into V0 p y) = y"
                using hy hbij0 unfolding bij_betw_def
                by (metis f_inv_into_f IntI imageI)
              moreover have "inv_into V0 p y \<in> V0"
                using hy hbij0 unfolding bij_betw_def
                by (metis IntI inv_into_into imageI)
              ultimately show "inv_into V0 p y = inv_into V p y"
              proof -
                assume hxV0: "inv_into V p y \<in> V0"
                   and hpVy: "p (inv_into V p y) = y"
                   and hpV0y: "p (inv_into V0 p y) = y"
                   and hx0V0: "inv_into V0 p y \<in> V0"
                have "p (inv_into V0 p y) = p (inv_into V p y)" using hpVy hpV0y by simp
                moreover have "inv_into V0 p y \<in> V" using hx0V0 hV0_sub_V by (by100 blast)
                moreover have "inv_into V p y \<in> V" using hxV0 hV0_sub_V by (by100 blast)
                ultimately show ?thesis
                  using hbij unfolding bij_betw_def inj_on_def by (by100 blast)
              qed
            qed
            \<comment> \<open>Continuity of inverse restriction.\<close>
            have hinv_cont_U0: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V0
                (subspace_topology V ?TV V0) (inv_into V0 p)"
            proof -
              have h1: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V ?TV (inv_into V p)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hU0_sub_U])
              have h2: "(inv_into V p) ` ?U0 \<subseteq> V0"
                using hinv_V0 by (by100 auto)
              have h3: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V0
                  (subspace_topology V ?TV V0) (inv_into V p)"
                by (rule top1_continuous_map_on_codomain_shrink[OF h1 h2 hV0_sub_V])
              have h4: "\<forall>y\<in>?U0. inv_into V p y = inv_into V0 p y"
                using hinv_eq by (by100 auto)
              show ?thesis by (rule top1_continuous_map_on_agree'[OF h3 h4])
            qed
            show "top1_homeomorphism_on V0 (subspace_topology V ?TV V0)
                ?U0 (subspace_topology U ?TU ?U0) p"
              unfolding top1_homeomorphism_on_def
              using subspace_topology_is_topology_on[OF hTV_top hV0_sub_V]
                    subspace_topology_is_topology_on[OF hTU_top hU0_sub_U]
                    hbij0 hp_cont_V0 hinv_cont_U0 by (by100 blast)
          qed
        qed
      qed
    qed
    ultimately have "b0 \<in> ?U0 \<and>
        top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p ?U0"
      by (by100 simp)
    thus "\<exists>U0. b0 \<in> U0 \<and>
        top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p U0"
      by (rule exI)
  qed
  show ?thesis unfolding top1_covering_map_on_def
    using hp_cont hp_surj hp_evenly by (by100 blast)
qed

(** from \<S>53 Theorem 53.3: product of covering maps is a covering map.
    Uses strict topology: product of strict is strict. **)
theorem Theorem_53_3:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on E' TE' B' TB' p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'" and "is_topology_on_strict B' TB'"
  shows "top1_covering_map_on (E \<times> E') (product_topology_on TE TE')
    (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
proof -
  \<comment> \<open>Munkres 53.3: product of covering maps.\<close>
  have hpxp_cont: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE')
      (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
  proof -
    have hTE: "is_topology_on E TE" by (rule is_topology_on_strict_imp[OF assms(3)])
    have hTB: "is_topology_on B TB" by (rule is_topology_on_strict_imp[OF assms(4)])
    have hTE': "is_topology_on E' TE'" by (rule is_topology_on_strict_imp[OF assms(5)])
    have hTB': "is_topology_on B' TB'" by (rule is_topology_on_strict_imp[OF assms(6)])
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp'_cont: "top1_continuous_map_on E' TE' B' TB' p'"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hTEE: "is_topology_on (E \<times> E') (product_topology_on TE TE')"
      by (rule product_topology_on_is_topology_on[OF hTE hTE'])
    \<comment> \<open>p \<circ> fst : E\<times>E' \<rightarrow> B is continuous.\<close>
    have hpi1: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E TE pi1"
      by (rule top1_continuous_pi1[OF hTE hTE'])
    have hpi1_eq: "(pi1 :: ('a \<times> 'b) \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
    have hfst: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E TE fst"
      using hpi1 unfolding pi1_def by (by100 simp)
    have hpfst: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B TB (p \<circ> fst)"
      by (rule top1_continuous_map_on_comp[OF hfst hp_cont])
    \<comment> \<open>p' \<circ> snd : E\<times>E' \<rightarrow> B' is continuous.\<close>
    have hpi2: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E' TE' pi2"
      by (rule top1_continuous_pi2[OF hTE hTE'])
    have hpi2_eq: "(pi2 :: ('a \<times> 'b) \<Rightarrow> 'b) = snd" unfolding pi2_def by (rule ext) simp
    have hsnd: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E' TE' snd"
      using hpi2 unfolding pi2_def by (by100 simp)
    have hp'snd: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B' TB' (p' \<circ> snd)"
      by (rule top1_continuous_map_on_comp[OF hsnd hp'_cont])
    \<comment> \<open>By Theorem 18.4: (\<lambda>(x,y). (p x, p' y)) = (\<lambda>z. (p(fst z), p'(snd z))) is continuous.\<close>
    have heq: "(\<lambda>(x, y). (p x, p' y)) = (\<lambda>z. ((p \<circ> fst) z, (p' \<circ> snd) z))"
      by (rule ext) (simp add: comp_def split_def)
    \<comment> \<open>By Theorem 18.4: pi1\<circ>f = p\<circ>fst and pi2\<circ>f = p'\<circ>snd are both continuous,
       so f = (\<lambda>(x,y). (p x, p' y)) is continuous into the product.\<close>
    have hpi1_comp: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B TB
        (pi1 \<circ> (\<lambda>(x, y). (p x, p' y)))"
    proof -
      have "pi1 \<circ> (\<lambda>(x, y). (p x, p' y)) = p \<circ> fst"
        unfolding pi1_def comp_def by (rule ext) (simp add: split_def)
      thus ?thesis using hpfst by simp
    qed
    have hpi2_comp: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B' TB'
        (pi2 \<circ> (\<lambda>(x, y). (p x, p' y)))"
    proof -
      have "pi2 \<circ> (\<lambda>(x, y). (p x, p' y)) = p' \<circ> snd"
        unfolding pi2_def comp_def by (rule ext) (simp add: split_def)
      thus ?thesis using hp'snd by simp
    qed
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTEE hTB hTB']] hpi1_comp hpi2_comp by (by100 simp)
  qed
  have hpxp_surj: "(\<lambda>(x, y). (p x, p' y)) ` (E \<times> E') = B \<times> B'"
  proof -
    have hp_surj: "p ` E = B" using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp'_surj: "p' ` E' = B'" using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis using hp_surj hp'_surj by force
  qed
  have hpxp_evenly: "\<forall>bb\<in>B \<times> B'. \<exists>W. bb \<in> W \<and>
      top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
        (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) W"
  proof
    fix bb assume hbb: "bb \<in> B \<times> B'"
    obtain b b' where hb: "b \<in> B" and hb': "b' \<in> B'" and hbb_eq: "bb = (b, b')"
      using hbb by blast
    \<comment> \<open>Take U, U' evenly covered by p, p' respectively.\<close>
    obtain U where hbU: "b \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
      using top1_covering_map_on_evenly_covered[OF assms(1) hb] by (by100 blast)
    obtain U' where hbU': "b' \<in> U'" and hU'ec: "top1_evenly_covered_on E' TE' B' TB' p' U'"
      using top1_covering_map_on_evenly_covered[OF assms(2) hb'] by (by100 blast)
    \<comment> \<open>U \<times> U' is evenly covered: slices are V\<alpha> \<times> V'\<beta>.\<close>
    have "bb \<in> U \<times> U' \<and>
        top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
          (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) (U \<times> U')" sorry
    thus "\<exists>W. bb \<in> W \<and>
        top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
          (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) W"
      by (rule exI)
  qed
  show ?thesis unfolding top1_covering_map_on_def
    using hpxp_cont hpxp_surj hpxp_evenly by blast
qed

section \<open>\<S>54 The Fundamental Group of the Circle\<close>

(** from \<S>54 Lemma 54.1: path-lifting lemma **)
lemma Lemma_54_1_path_lifting:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
  shows "\<exists>ftilde. top1_is_path_on E TE e0 (ftilde 1) ftilde
    \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)"
  \<comment> \<open>Textbook proof (Munkres Lemma 54.1):
     Step 1: Cover B by evenly covered open sets U. By the Lebesgue number lemma,
     find a subdivision 0 = s₀ < ... < sₙ = 1 s.t. each f([sᵢ,sᵢ₊₁]) \<subseteq> some Uᵢ.
     Step 2: Define ftilde step by step. Set ftilde(0) = e₀. For each [sᵢ,sᵢ₊₁],
     ftilde(sᵢ) lies in some slice V₀. Define ftilde(s) = (p|V₀)\<inverse>(f(s)).
     Step 3: Pasting lemma \<Rightarrow> continuous. p \<circ> ftilde = f by construction.\<close>
proof -
  \<comment> \<open>Step 1: Lebesgue subdivision.
     Proof sketch: every b \<in> B has an evenly covered neighborhood U_b. The preimages
     f^{-1}(U_b) cover [0,1]. Since [0,1] is compact, extract a finite subcover.
     Use the Lebesgue number \<delta> > 0 of this cover: any set of diameter < \<delta> lies in
     one element. Take n = ceil(1/\<delta>) and uniform subdivision sub(i) = i/n.\<close>
  obtain n :: nat and sub :: "nat \<Rightarrow> real" where
      hn: "n \<ge> 1" and hsub0: "sub 0 = 0" and hsubn: "sub n = 1"
      and hsub_inc: "\<forall>i<n. sub i < sub (Suc i)"
      and hcovered: "\<forall>i<n. \<exists>U. openin_on B TB U
          \<and> top1_evenly_covered_on E TE B TB p U
          \<and> f ` {s\<in>I_set. sub i \<le> s \<and> s \<le> sub (Suc i)} \<subseteq> U"
    sorry \<comment> \<open>Lebesgue number lemma on [0,1] (compact metric) with
           open cover = preimages of evenly-covered neighborhoods.\<close>
  \<comment> \<open>Step 2: Lift interval by interval by induction on the number of subintervals.
     Base: ftilde(0) = e0. Inductive step: given ftilde on [0, sub(i)],
     f([sub(i), sub(i+1)]) \<subseteq> U for some evenly covered U. ftilde(sub(i)) \<in> some slice V_0.
     Define ftilde(s) = (p|V_0)^{-1}(f(s)) for s \<in> [sub(i), sub(i+1)].
     Continuity by the pasting lemma.\<close>
  have "\<exists>ftilde. (\<forall>s\<in>I_set. ftilde s \<in> E)
      \<and> ftilde 0 = e0
      \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)
      \<and> top1_continuous_map_on I_set I_top E TE ftilde"
  proof -
    \<comment> \<open>Induction on k \<le> n gives ftilde on [0, sub(k)] at each step.
       At k = n, sub(n) = 1, giving ftilde on [0,1] = I_set.
       Each step uses the evenly covered neighborhood and the inverse of p|V_0.\<close>
    show ?thesis sorry
  qed
  \<comment> \<open>Assemble into path.\<close>
  then obtain ftilde where hft_mem: "\<forall>s\<in>I_set. ftilde s \<in> E"
      and hft0: "ftilde 0 = e0"
      and hftp: "\<forall>s\<in>I_set. p (ftilde s) = f s"
      and hft_cont: "top1_continuous_map_on I_set I_top E TE ftilde" by (by100 blast)
  have "top1_is_path_on E TE e0 (ftilde 1) ftilde"
    unfolding top1_is_path_on_def using hft_cont hft0 by (by100 simp)
  thus ?thesis using hftp by (by100 blast)
qed

text \<open>Helper: s \<mapsto> (s, c) is continuous I \<rightarrow> I \<times> I when c \<in> I.\<close>
lemma pair_s_const_continuous:
  assumes hc: "c \<in> I_set"
  shows "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, c))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  \<comment> \<open>pi_1 ∘ (s ↦ (s, c)) = id, and pi_2 ∘ (s ↦ (s, c)) = const c; both continuous.\<close>
  have hid: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hconst_c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTI hTI hc])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>s. (s, c))) = id"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>s. (s, c))) = (\<lambda>_. c)"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi1 \<circ> (\<lambda>s. (s, c)))"
    using hid unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>s. (s, c)))"
    using hconst_c unfolding hpi2_eq .
  show ?thesis
    unfolding II_topology_def
    using iffD2[OF Theorem_18_4[OF hTI hTI hTI]] hpi1_cont hpi2_cont by blast
qed

text \<open>Helper: t \<mapsto> (c, t) is continuous I \<rightarrow> I \<times> I when c \<in> I.\<close>
lemma pair_const_t_continuous:
  assumes hc: "c \<in> I_set"
  shows "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (c, t))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hid: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hconst_c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTI hTI hc])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>t. (c, t))) = (\<lambda>_. c)"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>t. (c, t))) = id"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi1 \<circ> (\<lambda>t. (c, t)))"
    using hconst_c unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>t. (c, t)))"
    using hid unfolding hpi2_eq .
  show ?thesis
    unfolding II_topology_def
    using iffD2[OF Theorem_18_4[OF hTI hTI hTI]] hpi1_cont hpi2_cont by (by100 blast)
qed

(** Uniqueness part of Lemma 54.1 (implicit in Munkres): given a path f in B with
    two lifts ftilde_1, ftilde_2 in E both starting at e_0, they are equal. **)
lemma Lemma_54_1_uniqueness:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
      and hft1: "top1_is_path_on E TE e0 e1 ftilde_1"
      and hft1p: "(\<forall>s\<in>I_set. p (ftilde_1 s) = f s)"
      and hft2: "top1_is_path_on E TE e0 e1' ftilde_2"
      and hft2p: "(\<forall>s\<in>I_set. p (ftilde_2 s) = f s)"
  shows "\<forall>s\<in>I_set. ftilde_1 s = ftilde_2 s"
proof -
  \<comment> \<open>Munkres 54.1 uniqueness: open-closed argument on the agreement set.\<close>
  let ?S = "{s \<in> I_set. ftilde_1 s = ftilde_2 s}"
  have hS_nonempty: "0 \<in> ?S"
  proof -
    have "ftilde_1 0 = e0" using hft1 unfolding top1_is_path_on_def by simp
    moreover have "ftilde_2 0 = e0" using hft2 unfolding top1_is_path_on_def by simp
    moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    ultimately show ?thesis by simp
  qed
  have hS_open: "openin_on I_set I_top ?S"
    \<comment> \<open>For s \<in> S: f(s) \<in> some evenly covered U. ftilde_1(s) = ftilde_2(s) \<in> some slice V0.
       Near s, both lifts stay in V0 (continuity). In V0, p is injective, so they agree.\<close>
    unfolding openin_on_def
  proof (intro conjI)
    show "?S \<in> I_top"
    proof -
      have hft1_cont: "top1_continuous_map_on I_set I_top E TE ftilde_1"
        using hft1 unfolding top1_is_path_on_def by (by100 blast)
      have hft2_cont: "top1_continuous_map_on I_set I_top E TE ftilde_2"
        using hft2 unfolding top1_is_path_on_def by (by100 blast)
      have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
        using hf unfolding top1_is_path_on_def by (by100 blast)
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      \<comment> \<open>For each s₀ ∈ S, find an open neighborhood of s₀ contained in S.
         Strategy: for s₀ ∈ S, get evenly covered U for f(s₀).
         The point ftilde_1(s₀) = ftilde_2(s₀) ∈ some slice V₀.
         Preimage of V₀ under both lifts contains a neighborhood of s₀.
         On this neighborhood, both lifts lie in V₀ and project to the same f(s),
         so by injectivity of p|V₀, they agree.\<close>
      \<comment> \<open>It suffices to show: for each s₀ ∈ S, there exists N ∈ I_top with s₀ ∈ N ∧ N ⊆ S.\<close>
      have "\<forall>s0\<in>?S. \<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> ?S"
      proof (intro ballI)
        fix s0 assume hs0: "s0 \<in> ?S"
        hence hs0I: "s0 \<in> I_set" and hagree: "ftilde_1 s0 = ftilde_2 s0" by (by100 blast)+
        \<comment> \<open>f(s₀) ∈ B; get evenly covered U.\<close>
        have hfs0: "f s0 \<in> B" using hf_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        obtain U where hbU: "f s0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
          using top1_covering_map_on_evenly_covered[OF hcov hfs0] by (by100 blast)
        \<comment> \<open>Get slices.\<close>
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
          using hUec unfolding top1_evenly_covered_on_def by auto
        \<comment> \<open>ftilde_1(s₀) ∈ p⁻¹(U) since p(ftilde_1(s₀)) = f(s₀) ∈ U.\<close>
        have hft1_E: "ftilde_1 s0 \<in> E"
          using hft1_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft1: "p (ftilde_1 s0) \<in> U" using hft1p hs0I hbU by (by100 simp)
        have hft1_mem: "ftilde_1 s0 \<in> {x\<in>E. p x \<in> U}"
          using hft1_E hp_ft1 by (by100 blast)
        \<comment> \<open>Find slice V₀ containing ftilde_1(s₀) = ftilde_2(s₀).\<close>
        obtain V0 where hV0: "V0 \<in> \<V>" and hft1_V0: "ftilde_1 s0 \<in> V0"
          using hft1_mem hV_union by (by100 blast)
        have hft2_V0: "ftilde_2 s0 \<in> V0" using hft1_V0 hagree by simp
        \<comment> \<open>V₀ is open in E.\<close>
        have hV0_open: "V0 \<in> TE" using hV0 hV_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>Preimages of V₀ under ftilde_1 and ftilde_2 are open in I.\<close>
        have hpre1: "{s\<in>I_set. ftilde_1 s \<in> V0} \<in> I_top"
          using hft1_cont hV0_open unfolding top1_continuous_map_on_def by (by100 blast)
        have hpre2: "{s\<in>I_set. ftilde_2 s \<in> V0} \<in> I_top"
          using hft2_cont hV0_open unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Intersection N = {s∈I. ftilde_1(s) ∈ V₀ ∧ ftilde_2(s) ∈ V₀} is open.\<close>
        let ?N = "{s\<in>I_set. ftilde_1 s \<in> V0} \<inter> {s\<in>I_set. ftilde_2 s \<in> V0}"
        have hN_open: "?N \<in> I_top"
          by (rule topology_inter2[OF hTI hpre1 hpre2])
        have hs0_N: "s0 \<in> ?N" using hs0I hft1_V0 hft2_V0 by (by100 blast)
        \<comment> \<open>On N, both lifts lie in V₀ and project to the same f(s).
           p|V₀ is a homeomorphism, hence injective. So ftilde_1(s) = ftilde_2(s).\<close>
        have hN_sub_S: "?N \<subseteq> ?S"
        proof (intro subsetI)
          fix s assume hs: "s \<in> ?N"
          hence hsI: "s \<in> I_set" and hft1s_V0: "ftilde_1 s \<in> V0" and hft2s_V0: "ftilde_2 s \<in> V0"
            by (by100 blast)+
          have hp_eq: "p (ftilde_1 s) = p (ftilde_2 s)"
          proof -
            have "p (ftilde_1 s) = f s" using hft1p hsI by (by100 blast)
            also have "\<dots> = p (ftilde_2 s)" using hft2p hsI by (by100 simp)
            finally show ?thesis .
          qed
          \<comment> \<open>p|V₀ is injective (from homeomorphism).\<close>
          have hp_inj: "inj_on p V0"
            using hV0 hV_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "ftilde_1 s = ftilde_2 s"
            using hp_inj hft1s_V0 hft2s_V0 hp_eq unfolding inj_on_def by (by100 blast)
          thus "s \<in> ?S" using hsI by (by100 blast)
        qed
        show "\<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> ?S"
          by (metis (no_types, lifting) hN_open hN_sub_S hs0_N)
      qed
      \<comment> \<open>S is a union of open sets from I_top, hence open.\<close>
      hence hSeq: "?S = \<Union>{N \<in> I_top. N \<subseteq> ?S}" by (by100 blast)
      have "{N \<in> I_top. N \<subseteq> ?S} \<subseteq> I_top" by (by100 blast)
      hence "\<Union>{N \<in> I_top. N \<subseteq> ?S} \<in> I_top"
        using conjunct1[OF conjunct2[OF conjunct2[OF hTI[unfolded is_topology_on_def]]]]
        by (by100 blast)
      thus "?S \<in> I_top" using hSeq by simp
    qed
    show "?S \<subseteq> I_set" by (by100 blast)
  qed
  have hS_closed: "closedin_on I_set I_top ?S"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?S \<subseteq> I_set" by (by100 blast)
  next
    \<comment> \<open>I_set - S = {s\<in>I_set. ftilde_1 s \<noteq> ftilde_2 s} is open.\<close>
    show "I_set - ?S \<in> I_top"
    proof -
      have hft1_cont: "top1_continuous_map_on I_set I_top E TE ftilde_1"
        using hft1 unfolding top1_is_path_on_def by (by100 blast)
      have hft2_cont: "top1_continuous_map_on I_set I_top E TE ftilde_2"
        using hft2 unfolding top1_is_path_on_def by (by100 blast)
      have hTI: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      \<comment> \<open>For each s₀ in I_set - S, get evenly covered U for f(s₀),
         find the disjoint slices containing ftilde_1(s₀) and ftilde_2(s₀),
         preimages of these slices under ftilde_1 and ftilde_2 give open neighborhood of s₀
         on which ftilde_1 and ftilde_2 disagree.\<close>
      have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
        using hf unfolding top1_is_path_on_def by (by100 blast)
      have "\<forall>s0\<in>I_set - ?S. \<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> I_set - ?S"
      proof (intro ballI)
        fix s0 assume hs0: "s0 \<in> I_set - ?S"
        hence hs0I: "s0 \<in> I_set" and hdisagree: "ftilde_1 s0 \<noteq> ftilde_2 s0" by (by100 blast)+
        have hfs0: "f s0 \<in> B" using hf_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        obtain U where hbU: "f s0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
          using top1_covering_map_on_evenly_covered[OF hcov hfs0] by (by100 blast)
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
          using hUec unfolding top1_evenly_covered_on_def by auto
        have hft1_E: "ftilde_1 s0 \<in> E"
          using hft1_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft1: "p (ftilde_1 s0) \<in> U" using hft1p hs0I hbU by (by100 simp)
        have hft1_pU: "ftilde_1 s0 \<in> {x\<in>E. p x \<in> U}" using hft1_E hp_ft1 by (by100 blast)
        have hft2_E: "ftilde_2 s0 \<in> E"
          using hft2_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft2: "p (ftilde_2 s0) \<in> U" using hft2p hs0I hbU by (by100 simp)
        have hft2_pU: "ftilde_2 s0 \<in> {x\<in>E. p x \<in> U}" using hft2_E hp_ft2 by (by100 blast)
        obtain V1 where hV1: "V1 \<in> \<V>" and hft1_V1: "ftilde_1 s0 \<in> V1"
          using hft1_pU hV_union by (by100 blast)
        obtain V2 where hV2: "V2 \<in> \<V>" and hft2_V2: "ftilde_2 s0 \<in> V2"
          using hft2_pU hV_union by (by100 blast)
        \<comment> \<open>V1 \<noteq> V2 since ftilde_1(s0) \<noteq> ftilde_2(s0) and slices disjoint.\<close>
        have hV12_ne: "V1 \<noteq> V2"
        proof
          assume "V1 = V2"
          hence "ftilde_1 s0 \<in> V1 \<and> ftilde_2 s0 \<in> V1" using hft1_V1 hft2_V2 by simp
          hence "p (ftilde_1 s0) = p (ftilde_2 s0) \<longrightarrow> ftilde_1 s0 = ftilde_2 s0"
            using hV1 hV_homeo unfolding top1_homeomorphism_on_def bij_betw_def inj_on_def
            by (by100 blast)
          moreover have "p (ftilde_1 s0) = p (ftilde_2 s0)"
            using hft1p hft2p hs0I by (by100 simp)
          ultimately show False using hdisagree by (by100 blast)
        qed
        have hV1V2_disj: "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 hV12_ne by (by100 blast)
        have hV1_open: "V1 \<in> TE" using hV1 hV_open unfolding openin_on_def by (by100 blast)
        have hV2_open: "V2 \<in> TE" using hV2 hV_open unfolding openin_on_def by (by100 blast)
        have hpre1: "{s\<in>I_set. ftilde_1 s \<in> V1} \<in> I_top"
          using hft1_cont hV1_open unfolding top1_continuous_map_on_def by (by100 blast)
        have hpre2: "{s\<in>I_set. ftilde_2 s \<in> V2} \<in> I_top"
          using hft2_cont hV2_open unfolding top1_continuous_map_on_def by (by100 blast)
        let ?N = "{s\<in>I_set. ftilde_1 s \<in> V1} \<inter> {s\<in>I_set. ftilde_2 s \<in> V2}"
        have hN_open: "?N \<in> I_top" by (rule topology_inter2[OF hTI hpre1 hpre2])
        have hs0_N: "s0 \<in> ?N" using hs0I hft1_V1 hft2_V2 by (by100 blast)
        have hN_sub: "?N \<subseteq> I_set - ?S"
        proof (intro subsetI)
          fix s assume hs: "s \<in> ?N"
          hence hsI: "s \<in> I_set" and hft1s: "ftilde_1 s \<in> V1" and hft2s: "ftilde_2 s \<in> V2"
            by (by100 blast)+
          have "ftilde_1 s \<noteq> ftilde_2 s"
          proof
            assume heq: "ftilde_1 s = ftilde_2 s"
            have "ftilde_2 s \<in> V1" using hft1s heq by simp
            hence "ftilde_2 s \<in> V1 \<inter> V2" using hft2s by (by100 blast)
            thus False using hV1V2_disj by (by100 blast)
          qed
          thus "s \<in> I_set - ?S" using hsI by (by100 blast)
        qed
        show "\<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> I_set - ?S"
          by (metis (no_types, lifting) hN_open hN_sub hs0_N)
      qed
      hence "I_set - ?S = \<Union>{N \<in> I_top. N \<subseteq> I_set - ?S}" by (by100 blast)
      moreover have "{N \<in> I_top. N \<subseteq> I_set - ?S} \<subseteq> I_top" by (by100 blast)
      moreover hence "\<Union>{N \<in> I_top. N \<subseteq> I_set - ?S} \<in> I_top"
        using conjunct1[OF conjunct2[OF conjunct2[OF hTI[unfolded is_topology_on_def]]]]
        by (by100 blast)
      ultimately show ?thesis by simp
    qed
  qed
  have hI_connected: "top1_connected_on I_set I_top"
    by (rule top1_unit_interval_connected)
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have "?S = I_set"
  proof -
    have hS_in_TX: "?S \<in> I_top" using hS_open unfolding openin_on_def by blast
    have hS_sub: "?S \<subseteq> I_set" by blast
    have "?S = {} \<or> ?S = I_set"
      using connected_iff_clopen[OF hTI] hI_connected hS_in_TX hS_closed by blast
    moreover have "?S \<noteq> {}" using hS_nonempty by blast
    ultimately show ?thesis by blast
  qed
  thus ?thesis by blast
qed

(** from \<S>54 Lemma 54.2: homotopy-lifting lemma **)
lemma Lemma_54_2_homotopy_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
      and "F (0, 0) = b0"
  shows "\<exists>Ftilde. top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde
    \<and> (\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t))
    \<and> Ftilde (0, 0) = e0"
proof -
  \<comment> \<open>Munkres 54.2: Lift F: I\<times>I \<rightarrow> B to Ftilde: I\<times>I \<rightarrow> E.\<close>
  \<comment> \<open>Step 1: Subdivide I\<times>I into rectangles mapping into evenly covered sets (Lebesgue).\<close>
  have "\<exists>m n. m > 0 \<and> n > 0 \<and>
    (\<forall>i<m. \<forall>j<n. \<exists>U. top1_evenly_covered_on E TE B TB p U \<and>
       F ` ({s\<in>I_set. real i/real m \<le> s \<and> s \<le> real(Suc i)/real m} \<times>
             {t\<in>I_set. real j/real n \<le> t \<and> t \<le> real(Suc j)/real n}) \<subseteq> U)" sorry
  \<comment> \<open>Step 2: Lift bottom edge using Lemma 54.1, then extend rectangle by rectangle.\<close>
  \<comment> \<open>At each rectangle: Ftilde already defined on left+bottom edges (connected).
     Image lies in one slice V0. Extend via p0\<inverse> \<circ> F on the rectangle.\<close>
  \<comment> \<open>Step 3: Pasting lemma gives continuity. p \<circ> Ftilde = F by construction.\<close>
  show ?thesis sorry
qed

(** from \<S>54 Theorem 54.3: path-homotopic paths lift to path-homotopic paths.

    Munkres' proof:
    (1) By definition of path homotopy, there is F: I\<times>I \<rightarrow> B with F(s,0)=f(s),
        F(s,1)=g(s), F(0,t)=b0, F(1,t)=b1.
    (2) Lift F to Ftilde: I\<times>I \<rightarrow> E with Ftilde(0,0)=e0, p\<circ>Ftilde=F (Lemma 54.2).
    (3) Ftilde(0,t) lies in p^{-1}(b0) (fiber), which is discrete, so it is
        constantly e0. Similarly Ftilde(1,t) is constant \<Rightarrow> e1 = e1'.
    (4) Ftilde(s,0) is a lift of f starting at e0, so = ftilde (by uniqueness).
        Ftilde(s,1) is a lift of g starting at e0, so = gtilde.
    (5) Hence Ftilde is a path homotopy from ftilde to gtilde. **)
theorem Theorem_54_3:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
      and hg: "top1_is_path_on B TB b0 b1 g"
      and hfg: "top1_path_homotopic_on B TB b0 b1 f g"
      and hft: "top1_is_path_on E TE e0 e1 ftilde"
      and hftp: "(\<forall>s\<in>I_set. p (ftilde s) = f s)"
      and hgt: "top1_is_path_on E TE e0 e1' gtilde"
      and hgtp: "(\<forall>s\<in>I_set. p (gtilde s) = g s)"
  shows "e1 = e1' \<and> top1_path_homotopic_on E TE e0 e1 ftilde gtilde"
proof -
  \<comment> \<open>Step 1: obtain a homotopy F from f to g in B by unfolding path-homotopy.\<close>
  obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
             and hF_f: "\<forall>s\<in>I_set. F (s, 0) = f s"
             and hF_g: "\<forall>s\<in>I_set. F (s, 1) = g s"
             and hF_b0: "\<forall>t\<in>I_set. F (0, t) = b0"
             and hF_b1: "\<forall>t\<in>I_set. F (1, t) = b1"
    using hfg unfolding top1_path_homotopic_on_def by blast
  \<comment> \<open>Step 2: lift F to Ftilde via Lemma 54.2. F(0,0) = f(0) = b0.\<close>
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hF_00: "F (0, 0) = b0"
    using hF_f[rule_format, OF h0I] hf unfolding top1_is_path_on_def by simp
  obtain Ftilde where
        hFt_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde"
    and hFt_lift: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t)"
    and hFt_00: "Ftilde (0, 0) = e0"
    using Lemma_54_2_homotopy_lifting[OF hcov he0 hpe0 hF_cont hF_00] by blast
  \<comment> \<open>Step 3: Ftilde(0,t) is constant e0; Ftilde(1,t) is constant, so e1 = e1'\<close>
  have hFt_left: "\<forall>t\<in>I_set. Ftilde (0, t) = e0"
  proof -
    have h0I0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (0, t))"
      by (rule pair_const_t_continuous[OF h0I0])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (0, t)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont_left: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (0, t))"
      using hcomp by (simp add: comp_def)
    have hleft_lift: "\<forall>t\<in>I_set. p (Ftilde (0, t)) = b0"
      using hFt_lift hF_b0 h0I0 by auto
    have hpath_left: "top1_is_path_on E TE e0 (Ftilde (0, 1)) (\<lambda>t. Ftilde (0, t))"
      unfolding top1_is_path_on_def using hcont_left hFt_00 by simp
    \<comment> \<open>Constant path at b_0, lifted to constant path at e_0.\<close>
    have hb0_in_B: "b0 \<in> B"
      using hf unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h0I0 by blast
    have hconst_B: "top1_is_path_on B TB b0 b0 (top1_constant_path b0)"
      by (rule top1_constant_path_is_path[OF hTB hb0_in_B])
    have hconst_E: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0])
    have hconst_lift: "\<forall>s\<in>I_set. p (top1_constant_path e0 s) = top1_constant_path b0 s"
      unfolding top1_constant_path_def using hpe0 by simp
    have hleft_const_lift': "\<forall>s\<in>I_set. p (Ftilde (0, s)) = top1_constant_path b0 s"
      using hleft_lift unfolding top1_constant_path_def by simp
    have "\<forall>t\<in>I_set. Ftilde (0, t) = top1_constant_path e0 t"
      using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hconst_B hpath_left
                                      hleft_const_lift' hconst_E hconst_lift] .
    thus ?thesis unfolding top1_constant_path_def by simp
  qed
  have hFt_right_const: "\<exists>e. \<forall>t\<in>I_set. Ftilde (1, t) = e"
  proof -
    let ?e1loc = "Ftilde (1, 0)"
    have h0I_: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have h1I_: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (1, t))"
      by (rule pair_const_t_continuous[OF h1I_])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (1, t)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont_right: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (1, t))"
      using hcomp by (simp add: comp_def)
    have hright_lift: "\<forall>t\<in>I_set. p (Ftilde (1, t)) = b1"
      using hFt_lift hF_b1 h1I_ by auto
    have he1_in_E: "?e1loc \<in> E"
      using hcont_right h0I_ unfolding top1_continuous_map_on_def by blast
    have hpe1: "p ?e1loc = b1" using hright_lift h0I_ by blast
    have hpath_right: "top1_is_path_on E TE ?e1loc (Ftilde (1, 1)) (\<lambda>t. Ftilde (1, t))"
      unfolding top1_is_path_on_def using hcont_right by simp
    \<comment> \<open>Constant path at b_1 in B, lifted to constant path at ?e1loc in E.\<close>
    have hb1_in_B: "b1 \<in> B" using hf unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h1I_ by blast
    have hconst_B: "top1_is_path_on B TB b1 b1 (top1_constant_path b1)"
      by (rule top1_constant_path_is_path[OF hTB hb1_in_B])
    have hconst_E: "top1_is_path_on E TE ?e1loc ?e1loc (top1_constant_path ?e1loc)"
      by (rule top1_constant_path_is_path[OF hTE he1_in_E])
    have hconst_lift: "\<forall>s\<in>I_set. p (top1_constant_path ?e1loc s) = top1_constant_path b1 s"
      unfolding top1_constant_path_def using hpe1 by simp
    have hright_const_lift': "\<forall>s\<in>I_set. p (Ftilde (1, s)) = top1_constant_path b1 s"
      using hright_lift unfolding top1_constant_path_def by simp
    have "\<forall>t\<in>I_set. Ftilde (1, t) = top1_constant_path ?e1loc t"
      using Lemma_54_1_uniqueness[OF hcov he1_in_E hpe1 hconst_B hpath_right
                                      hright_const_lift' hconst_E hconst_lift] .
    hence "\<forall>t\<in>I_set. Ftilde (1, t) = ?e1loc"
      unfolding top1_constant_path_def by simp
    thus ?thesis by blast
  qed
  \<comment> \<open>Step 4: Ftilde(s,0) = ftilde and Ftilde(s,1) = gtilde by uniqueness of path lifting.\<close>
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  \<comment> \<open>Ftilde(·, 0) is a path in E lifting f, starting at e0.\<close>
  have hFt_bot_path: "top1_is_path_on E TE e0 (Ftilde (1, 0)) (\<lambda>s. Ftilde (s, 0))"
  proof -
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 0))"
      by (rule pair_s_const_continuous[OF h0I])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 0)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont: "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 0))"
      using hcomp by (simp add: comp_def)
    show ?thesis
      unfolding top1_is_path_on_def using hcont hFt_00 by simp
  qed
  have hFt_bot_lift: "\<forall>s\<in>I_set. p (Ftilde (s, 0)) = f s"
    using hFt_lift hF_f h0I by auto
  have hFt_bot: "\<forall>s\<in>I_set. Ftilde (s, 0) = ftilde s"
    using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf hFt_bot_path hFt_bot_lift hft hftp] by blast
  \<comment> \<open>Ftilde(·, 1) is a path in E lifting g, starting at Ftilde(0,1).\<close>
  have h1I0: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hFt_top_start: "Ftilde (0, 1) = e0"
    using hFt_left h1I0 by blast
  have hFt_top_path: "top1_is_path_on E TE e0 (Ftilde (1, 1)) (\<lambda>s. Ftilde (s, 1))"
  proof -
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 1))"
      by (rule pair_s_const_continuous[OF h1I0])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 1)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont: "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 1))"
      using hcomp by (simp add: comp_def)
    show ?thesis
      unfolding top1_is_path_on_def using hcont hFt_top_start by simp
  qed
  have hFt_top_lift: "\<forall>s\<in>I_set. p (Ftilde (s, 1)) = g s"
    using hFt_lift hF_g unfolding top1_unit_interval_def by auto
  have hFt_top: "\<forall>s\<in>I_set. Ftilde (s, 1) = gtilde s"
    using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hg hFt_top_path hFt_top_lift hgt hgtp] by blast
  \<comment> \<open>Step 5: assemble endpoints equal and path homotopy.\<close>
  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hft_1: "ftilde 1 = e1"
    using hft unfolding top1_is_path_on_def by simp
  have hgt_1: "gtilde 1 = e1'"
    using hgt unfolding top1_is_path_on_def by simp
  \<comment> \<open>Ftilde(1, 0) = ftilde(1) = e1 and Ftilde(1, 1) = gtilde(1) = e1', and the fiber is constant.\<close>
  have heq: "e1 = e1'"
  proof -
    obtain e where hc: "\<forall>t\<in>I_set. Ftilde (1, t) = e" using hFt_right_const by blast
    have h0: "Ftilde (1, 0) = e" using hc h0I by blast
    have h1: "Ftilde (1, 1) = e" using hc h1I by blast
    have "Ftilde (1, 0) = ftilde 1" using hFt_bot h1I by blast
    hence "e1 = e" using hft_1 h0 by simp
    moreover have "Ftilde (1, 1) = gtilde 1" using hFt_top h1I by blast
    hence "e1' = e" using hgt_1 h1 by simp
    ultimately show ?thesis by simp
  qed
  have hhomo: "top1_path_homotopic_on E TE e0 e1 ftilde gtilde"
  proof -
    \<comment> \<open>Ftilde is the path homotopy: cont, boundary ftilde/gtilde, sides e0/e1.\<close>
    have hgt': "top1_is_path_on E TE e0 e1 gtilde" using hgt heq by simp
    have hFt_b0: "\<forall>s\<in>I_set. Ftilde (s, 0) = ftilde s" using hFt_bot .
    have hFt_b1: "\<forall>s\<in>I_set. Ftilde (s, 1) = gtilde s" using hFt_top .
    have hFt_l0: "\<forall>t\<in>I_set. Ftilde (0, t) = e0" using hFt_left .
    have hFt_r1: "\<forall>t\<in>I_set. Ftilde (1, t) = e1"
    proof -
      obtain e where hc: "\<forall>t\<in>I_set. Ftilde (1, t) = e" using hFt_right_const by blast
      have "Ftilde (1, 0) = e" using hc h0I by blast
      moreover have "Ftilde (1, 0) = ftilde 1" using hFt_bot h1I by blast
      ultimately have "e = e1" using hft_1 by simp
      thus ?thesis using hc by simp
    qed
    show ?thesis
      unfolding top1_path_homotopic_on_def
      using hft hgt' hFt_cont hFt_b0 hFt_b1 hFt_l0 hFt_r1 by blast
  qed
  show ?thesis using heq hhomo by blast
qed

text \<open>Helper: continuous maps preserve path homotopy.
  If f ≃ g in X and h: X → Y is continuous, then h∘f ≃ h∘g in Y.\<close>
lemma continuous_preserves_path_homotopic:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hhom: "top1_path_homotopic_on X TX x0 x1 f g"
  shows "top1_path_homotopic_on Y TY (h x0) (h x1) (h \<circ> f) (h \<circ> g)"
proof -
  have hf: "top1_is_path_on X TX x0 x1 f"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have hg: "top1_is_path_on X TX x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = x0" and hFr: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hhom unfolding top1_path_homotopic_on_def by (by100 auto)
  \<comment> \<open>h \<circ> F is a path homotopy from h\<circ>f to h\<circ>g in Y.\<close>
  have hhF: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (h \<circ> F)"
    by (rule top1_continuous_map_on_comp[OF hF hh])
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
    using hg unfolding top1_is_path_on_def by (by100 blast)
  have hhf_path: "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf_cont hh])
    show "(h \<circ> f) 0 = h x0" using hf unfolding top1_is_path_on_def by simp
    show "(h \<circ> f) 1 = h x1" using hf unfolding top1_is_path_on_def by simp
  qed
  have hhg_path: "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> g)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> g)"
      by (rule top1_continuous_map_on_comp[OF hg_cont hh])
    show "(h \<circ> g) 0 = h x0" using hg unfolding top1_is_path_on_def by simp
    show "(h \<circ> g) 1 = h x1" using hg unfolding top1_is_path_on_def by simp
  qed
  show ?thesis unfolding top1_path_homotopic_on_def
  proof (intro conjI exI)
    show "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> f)" by (rule hhf_path)
    show "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> g)" by (rule hhg_path)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (h \<circ> F)" by (rule hhF)
    show "\<forall>s\<in>I_set. (h \<circ> F) (s, 0) = (h \<circ> f) s" using hF0 by simp
    show "\<forall>s\<in>I_set. (h \<circ> F) (s, 1) = (h \<circ> g) s" using hF1 by simp
    show "\<forall>t\<in>I_set. (h \<circ> F) (0, t) = h x0" using hFl by simp
    show "\<forall>t\<in>I_set. (h \<circ> F) (1, t) = h x1" using hFr by simp
  qed
qed

text \<open>Helper: if two functions agree on I\_set, they give the same loop.\<close>
lemma loop_agree_on_I:
  assumes hf: "top1_is_loop_on X TX x0 f"
      and hagree: "\<forall>s\<in>I_set. g s = f s"
  shows "top1_is_loop_on X TX x0 g \<and> top1_path_homotopic_on X TX x0 x0 f g"
proof -
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hagree': "\<forall>s\<in>I_set. f s = g s" using hagree by simp
  have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
    by (rule top1_continuous_map_on_agree'[OF hf_cont hagree'])
  have hf0: "f 0 = x0" and hf1: "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have h0I: "(0::real) \<in> I_set" and h1I: "(1::real) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hg0: "g 0 = x0" using hagree h0I hf0 by simp
  have hg1: "g 1 = x0" using hagree h1I hf1 by simp
  have hg_loop: "top1_is_loop_on X TX x0 g"
    unfolding top1_is_loop_on_def top1_is_path_on_def using hg_cont hg0 hg1 by simp
  have hfg_eq: "\<forall>s\<in>I_set. f s = g s" using hagree by simp
  have "top1_path_homotopic_on X TX x0 x0 f g"
    unfolding top1_path_homotopic_on_def
  proof -
    have hf_path: "top1_is_path_on X TX x0 x0 f"
      using hf unfolding top1_is_loop_on_def .
    have hg_path: "top1_is_path_on X TX x0 x0 g"
      using hg_loop unfolding top1_is_loop_on_def .
    \<comment> \<open>Constant homotopy works since f=g on I_set. Use F(s,t) = f(s) = g(s).\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
      by (rule top1_continuous_map_on_comp[OF hpi1 hf_cont])
    have hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
      using hF_cont unfolding pi1_def comp_def by simp
    show "top1_is_path_on X TX x0 x0 f \<and> top1_is_path_on X TX x0 x0 g \<and>
      (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F \<and>
           (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s) \<and>
           (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x0))"
      using hf_path hg_path hF hfg_eq hf0 hf1 by auto
  qed
  thus ?thesis using hg_loop by blast
qed

text \<open>Helper: in a simply connected space, any two paths with the same endpoints
  are path-homotopic. Uses: gt*ft⁻¹ is a loop, simply connected → nulhomotopic,
  then path algebra gives ft ≃ gt.\<close>
lemma simply_connected_paths_homotopic:
  assumes hsc: "top1_simply_connected_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x0 x1 g"
      and hx0: "x0 \<in> X"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  have hTE: "is_topology_on X TX"
    using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
  let ?loop = "top1_path_product g (top1_path_reverse f)"
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have hloop_path: "top1_is_path_on X TX x0 x0 ?loop"
    by (rule top1_path_product_is_path[OF hTE hg hrev])
  have hloop: "top1_is_loop_on X TX x0 ?loop"
    unfolding top1_is_loop_on_def using hloop_path by (by100 simp)
  have hloop_nul: "top1_path_homotopic_on X TX x0 x0 ?loop (top1_constant_path x0)"
    using hsc hx0 hloop unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>(g*f⁻¹)*f ≃ const*f ≃ f and (g*f⁻¹)*f ≃ g*(f⁻¹*f) ≃ g*const ≃ g. So f ≃ g.\<close>
  have s1: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?loop f) (top1_path_product (top1_constant_path x0) f)"
    by (rule path_homotopic_product_left[OF hTE hloop_nul hf])
  have s2: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product (top1_constant_path x0) f) f"
    by (rule Theorem_51_2_left_identity[OF hTE hf])
  have s12: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?loop f) f"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTE s1 s2])
  have s3: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?loop f)
      (top1_path_product g (top1_path_product (top1_path_reverse f) f))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTE hg hrev hf]])
  have s4: "top1_path_homotopic_on X TX x1 x1
      (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
    by (rule Theorem_51_2_invgerse_right[OF hTE hf])
  have s5: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product g (top1_path_product (top1_path_reverse f) f))
      (top1_path_product g (top1_constant_path x1))"
    by (rule path_homotopic_product_right[OF hTE s4 hg])
  have s6: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product g (top1_constant_path x1)) g"
    by (rule Theorem_51_2_right_identity[OF hTE hg])
  have s_chain: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?loop f) g"
  proof (rule Lemma_51_1_path_homotopic_trans[OF hTE s3])
    show "top1_path_homotopic_on X TX x0 x1
        (top1_path_product g (top1_path_product (top1_path_reverse f) f)) g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTE s5 s6])
  qed
  have s12_sym: "top1_path_homotopic_on X TX x0 x1 f (top1_path_product ?loop f)"
    by (rule Lemma_51_1_path_homotopic_sym[OF s12])
  show ?thesis by (rule Lemma_51_1_path_homotopic_trans[OF hTE s12_sym s_chain])
qed

(** from \<S>54 Theorem 54.4: lifting correspondence.
    Given a covering p : (E, e_0) \<to> (B, b_0) and E path-connected, the map
    \<Phi> : \<pi>_1(B, b_0) \<to> p\<inverse>(b_0) sending [f] to \<tilde>f(1) (where \<tilde>f is the lift
    starting at e_0) is surjective. **)
theorem Theorem_54_4_lifting_correspondence:
  assumes he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
      and "is_topology_on B TB"
  shows "\<exists>\<phi>. (\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
                \<phi> c \<in> {e\<in>E. p e = b0})
           \<and> \<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}
           \<and> (\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
                \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
                  \<and> top1_is_path_on E TE e0 (\<phi> c) ft
                  \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
proof -
  \<comment> \<open>Munkres 54.4: Define \<phi>([f]) = ftilde(1) where ftilde lifts f starting at e0.\<close>
  \<comment> \<open>Well-defined: by Theorem 54.3, path-homotopic loops lift to same endpoint.\<close>
  have hTE: "is_topology_on E TE"
    using assms(4) unfolding top1_path_connected_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" by (rule assms(5))
  have hphi_wd: "\<forall>f g. top1_is_loop_on B TB b0 f \<and> top1_is_loop_on B TB b0 g
      \<and> top1_path_homotopic_on B TB b0 b0 f g
      \<longrightarrow> (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)
          \<and> top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)
          \<longrightarrow> ft 1 = gt 1)"
  proof (intro allI impI, elim conjE)
    fix f g ft gt
    assume hfl: "top1_is_loop_on B TB b0 f" and hgl: "top1_is_loop_on B TB b0 g"
        and hfg: "top1_path_homotopic_on B TB b0 b0 f g"
        and hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f s"
        and hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = g s"
    have hf_path: "top1_is_path_on B TB b0 b0 f"
      using hfl unfolding top1_is_loop_on_def .
    have hg_path: "top1_is_path_on B TB b0 b0 g"
      using hgl unfolding top1_is_loop_on_def .
    show "ft 1 = gt 1"
      using conjunct1[OF Theorem_54_3[OF assms(3) hTE hTB he0 hpe0 hf_path hg_path hfg hft hftp hgt hgtp]]
      .
  qed
  \<comment> \<open>Surjectivity: for e1 \<in> p\<inverse>(b0), path f_tilde from e0 to e1 projects to loop at b0.\<close>
  have hphi_surj: "\<forall>e1\<in>{e\<in>E. p e = b0}. \<exists>f. top1_is_loop_on B TB b0 f \<and>
      (\<exists>ft. top1_is_path_on E TE e0 e1 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
  proof
    fix e1 assume he1: "e1 \<in> {e\<in>E. p e = b0}"
    hence he1E: "e1 \<in> E" and hpe1: "p e1 = b0" by (by100 blast)+
    \<comment> \<open>Path \<alpha> from e0 to e1 in E (path-connected).\<close>
    obtain \<alpha> where h\<alpha>: "top1_is_path_on E TE e0 e1 \<alpha>"
      using assms(4) he0 he1E unfolding top1_path_connected_on_def by (by100 auto)
    \<comment> \<open>f = p \<circ> \<alpha> is a loop at b0: f(0) = p(e0) = b0, f(1) = p(e1) = b0.\<close>
    let ?f = "p \<circ> \<alpha>"
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(3) unfolding top1_covering_map_on_def by (by100 blast)
    have h\<alpha>_cont: "top1_continuous_map_on I_set I_top E TE \<alpha>"
      using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
    have hf_cont: "top1_continuous_map_on I_set I_top B TB ?f"
      by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hp_cont])
    have hf0: "?f 0 = b0" using h\<alpha> hpe0 unfolding top1_is_path_on_def by simp
    have hf1: "?f 1 = b0" using h\<alpha> hpe1 unfolding top1_is_path_on_def by simp
    have hf_loop: "top1_is_loop_on B TB b0 ?f"
      unfolding top1_is_loop_on_def top1_is_path_on_def using hf_cont hf0 hf1 by simp
    have hft_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = ?f s" by simp
    show "\<exists>f. top1_is_loop_on B TB b0 f \<and>
        (\<exists>ft. top1_is_path_on E TE e0 e1 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
      using hf_loop h\<alpha> hft_lift by (by100 blast)
  qed
  \<comment> \<open>Define \<phi>(c): pick any representative loop f from class c, lift it, take endpoint.\<close>
  let ?\<phi> = "\<lambda>c. let f = SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f in
               let ft = SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)
               in ft 1"
  \<comment> \<open>Well-definedness from hphi_wd + existence from path-lifting.\<close>
  have hphi_mem: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
      ?\<phi> c \<in> {e\<in>E. p e = b0}"
  proof
    fix c assume hc: "c \<in> top1_fundamental_group_carrier B TB b0"
    \<comment> \<open>c is an equivalence class {g. loop_equiv f g} for some loop f.\<close>
    obtain f0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 f0 g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    have hf0_in: "f0 \<in> c"
    proof -
      have "top1_is_path_on B TB b0 b0 f0" using hf0_loop unfolding top1_is_loop_on_def .
      hence "top1_path_homotopic_on B TB b0 b0 f0 f0"
        by (rule Lemma_51_1_path_homotopic_refl)
      hence "top1_loop_equiv_on B TB b0 f0 f0"
        unfolding top1_loop_equiv_on_def using hf0_loop by (by100 simp)
      thus ?thesis unfolding hc_eq by (by100 simp)
    qed
    \<comment> \<open>SOME picks a representative from c.\<close>
    let ?f = "SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f"
    have hf_props: "?f \<in> c \<and> top1_is_loop_on B TB b0 ?f"
      using someI_ex[of "\<lambda>f. f \<in> c \<and> top1_is_loop_on B TB b0 f"] hf0_in hf0_loop by (by100 blast)
    \<comment> \<open>Path-lift ?f to get ft.\<close>
    have hf_path: "top1_is_path_on B TB b0 b0 ?f"
      using hf_props unfolding top1_is_loop_on_def by (by100 blast)
    obtain ft0 where hft0: "top1_is_path_on E TE e0 (ft0 1) ft0"
        and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = ?f s"
      using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf_path] by (by100 auto)
    \<comment> \<open>SOME picks a lift.\<close>
    let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"
    have hft_props: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = ?f s)"
      using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"]
        hft0 hft0p by (by100 blast)
    \<comment> \<open>ft(1) \<in> E and p(ft(1)) = f(1) = b0.\<close>
    have "?ft 1 \<in> E"
    proof -
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "top1_continuous_map_on I_set I_top E TE ?ft"
        using hft_props unfolding top1_is_path_on_def by (by100 blast)
      hence "\<forall>s\<in>I_set. ?ft s \<in> E" unfolding top1_continuous_map_on_def by (by100 blast)
      thus "?ft 1 \<in> E" using h1I by (by100 blast)
    qed
    moreover have "p (?ft 1) = b0"
    proof -
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "p (?ft 1) = ?f 1" using hft_props h1I by (by100 blast)
      also have "?f 1 = b0" using hf_props unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      finally show ?thesis .
    qed
    ultimately show "?\<phi> c \<in> {e\<in>E. p e = b0}" by (simp add: Let_def)
  qed
  have hphi_surj_full: "?\<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> ?\<phi> ` (top1_fundamental_group_carrier B TB b0)"
    thus "e \<in> {e\<in>E. p e = b0}" using hphi_mem by (by100 blast)
  next
    fix e1 assume he1: "e1 \<in> {e\<in>E. p e = b0}"
    \<comment> \<open>By hphi_surj, \<exists>f loop whose lift reaches e1.\<close>
    obtain f0 ft0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hft0: "top1_is_path_on E TE e0 e1 ft0" and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = f0 s"
      using hphi_surj he1 by (by100 auto)
    \<comment> \<open>The equivalence class of f0 is in the carrier.\<close>
    let ?c = "{g. top1_loop_equiv_on B TB b0 f0 g}"
    have hc_carrier: "?c \<in> top1_fundamental_group_carrier B TB b0"
      unfolding top1_fundamental_group_carrier_def using hf0_loop by (by100 blast)
    \<comment> \<open>\<phi>(?c) = e1 by well-definedness: \<phi> picks a representative and lifts it,
       and by hphi_wd, all lifts of equivalent loops end at the same point.\<close>
    have "?\<phi> ?c = e1"
    proof -
      \<comment> \<open>SOME picks f' \<in> ?c with f' a loop. f0 is such, so f' exists.\<close>
      have hf0_in_c: "f0 \<in> ?c"
      proof -
        have "top1_is_path_on B TB b0 b0 f0" using hf0_loop unfolding top1_is_loop_on_def .
        hence "top1_path_homotopic_on B TB b0 b0 f0 f0" by (rule Lemma_51_1_path_homotopic_refl)
        thus ?thesis unfolding top1_loop_equiv_on_def using hf0_loop by (by100 simp)
      qed
      let ?f' = "SOME f. f \<in> ?c \<and> top1_is_loop_on B TB b0 f"
      have hf'_props: "?f' \<in> ?c \<and> top1_is_loop_on B TB b0 ?f'"
        using someI_ex[of "\<lambda>f. f \<in> ?c \<and> top1_is_loop_on B TB b0 f"] hf0_in_c hf0_loop
        by (by100 blast)
      \<comment> \<open>f' is loop-equivalent to f0.\<close>
      have hf'_equiv: "top1_loop_equiv_on B TB b0 f0 ?f'"
        using hf'_props by simp
      hence hf0_f': "top1_path_homotopic_on B TB b0 b0 f0 ?f'"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      \<comment> \<open>Lift ?f' from e0.\<close>
      have hf'_path: "top1_is_path_on B TB b0 b0 ?f'"
        using hf'_props unfolding top1_is_loop_on_def by (by100 blast)
      obtain ft' where hft': "top1_is_path_on E TE e0 (ft' 1) ft'"
          and hft'p: "\<forall>s\<in>I_set. p (ft' s) = ?f' s"
        using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf'_path] by (by100 auto)
      \<comment> \<open>SOME picks a lift of ?f'.\<close>
      let ?ft' = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f' s)"
      have hft'_props: "top1_is_path_on E TE e0 (?ft' 1) ?ft' \<and> (\<forall>s\<in>I_set. p (?ft' s) = ?f' s)"
        using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f' s)"]
          hft' hft'p by (by100 blast)
      \<comment> \<open>By hphi_wd: ft0(1) = ft'(1) since f0 \<simeq> f'.\<close>
      have "ft0 1 = ?ft' 1"
      proof -
        have hf'_loop: "top1_is_loop_on B TB b0 ?f'" using hf'_props by (by100 blast)
        have h_ft0_1: "ft0 1 = e1" using hft0 unfolding top1_is_path_on_def by simp
        have h_ft0': "top1_is_path_on E TE e0 (ft0 1) ft0"
          using hft0 h_ft0_1 by simp
        have h_ft'_path: "top1_is_path_on E TE e0 (?ft' 1) ?ft'"
          using hft'_props by (by100 blast)
        have h_ft'p: "\<forall>s\<in>I_set. p (?ft' s) = ?f' s"
          using hft'_props by (by100 blast)
        \<comment> \<open>Apply hphi_wd with f = f0, g = ?f', ft = ft0, gt = ?ft'.\<close>
        have hwd: "top1_is_loop_on B TB b0 f0 \<and> top1_is_loop_on B TB b0 ?f'
            \<and> top1_path_homotopic_on B TB b0 b0 f0 ?f'
            \<longrightarrow> (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f0 s)
                \<and> top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = ?f' s)
                \<longrightarrow> ft 1 = gt 1)"
          using hphi_wd by blast
        have hpremise: "top1_is_loop_on B TB b0 f0 \<and> top1_is_loop_on B TB b0 ?f'
            \<and> top1_path_homotopic_on B TB b0 b0 f0 ?f'"
          using hf0_loop hf'_loop hf0_f' by (by100 blast)
        have hlifts: "top1_is_path_on E TE e0 (ft0 1) ft0 \<and> (\<forall>s\<in>I_set. p (ft0 s) = f0 s)
            \<and> top1_is_path_on E TE e0 (?ft' 1) ?ft' \<and> (\<forall>s\<in>I_set. p (?ft' s) = ?f' s)"
          using h_ft0' hft0p h_ft'_path h_ft'p by (by100 blast)
        show ?thesis using hwd hpremise hlifts by blast
      qed
      \<comment> \<open>ft0(1) = e1 by assumption, so ?ft'(1) = e1.\<close>
      hence "?ft' 1 = e1" using hft0 unfolding top1_is_path_on_def by simp
      \<comment> \<open>\<phi>(?c) = ?ft'(1) = e1.\<close>
      thus ?thesis by (simp add: Let_def)
    qed
    thus "e1 \<in> ?\<phi> ` (top1_fundamental_group_carrier B TB b0)"
      using hc_carrier by (by100 blast)
  qed
  \<comment> \<open>Lift characterization: \<phi>(c) is the endpoint of a lift of a representative.\<close>
  have hphi_lift: "\<forall>c\<in>top1_fundamental_group_carrier B TB b0.
      \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
        \<and> top1_is_path_on E TE e0 (?\<phi> c) ft
        \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
  proof
    fix c assume hc: "c \<in> top1_fundamental_group_carrier B TB b0"
    obtain f0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 f0 g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    let ?f = "SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f"
    have hf_props: "?f \<in> c \<and> top1_is_loop_on B TB b0 ?f"
    proof -
      have "f0 \<in> c" unfolding hc_eq
        using top1_loop_equiv_on_refl[OF hf0_loop] by simp
      thus ?thesis using someI_ex[of "\<lambda>f. f \<in> c \<and> top1_is_loop_on B TB b0 f"] hf0_loop
        by (by100 blast)
    qed
    let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"
    have hft_props: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = ?f s)"
    proof -
      have hf_path: "top1_is_path_on B TB b0 b0 ?f"
        using hf_props unfolding top1_is_loop_on_def by (by100 blast)
      obtain ft0 where "top1_is_path_on E TE e0 (ft0 1) ft0"
          "(\<forall>s\<in>I_set. p (ft0 s) = ?f s)"
        using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf_path] by (by100 auto)
      thus ?thesis using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"]
        by (by100 blast)
    qed
    show "\<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
        \<and> top1_is_path_on E TE e0 (?\<phi> c) ft
        \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
      using hf_props hft_props by (simp add: Let_def) blast
  qed
  show ?thesis
    apply (rule exI[of _ ?\<phi>])
    using hphi_mem hphi_surj_full hphi_lift by (by100 blast)
qed

theorem Theorem_54_4_bijective_simply_connected:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_simply_connected_on E TE"
      and "is_topology_on B TB"
  shows "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier B TB b0) {e\<in>E. p e = b0}"
proof -
  \<comment> \<open>Munkres 54.4 bijectivity: surjectivity from path-connectedness (which follows
     from simple connectivity), injectivity from simple connectivity of E.\<close>
  have hpc: "top1_path_connected_on E TE"
    using assms(4) top1_simply_connected_on_path_connected by (by100 blast)
  have hTB_outer: "is_topology_on B TB" by (rule assms(5))
  \<comment> \<open>Injectivity: if \<phi>([f])=\<phi>([g]) then lifts end at same point. E simply connected
     gives path homotopy Ftilde between lifts; p\<circ>Ftilde homotopizes f to g.\<close>
  have hinj: "\<forall>f g. top1_is_loop_on B TB b0 f \<and> top1_is_loop_on B TB b0 g \<and>
      (\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)) \<and>
      (\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)) \<and>
      (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = g s) \<longrightarrow>
               ft 1 = gt 1)
      \<longrightarrow> top1_path_homotopic_on B TB b0 b0 f g"
  proof (intro allI impI, elim conjE)
    fix f g assume hfl: "top1_is_loop_on B TB b0 f" and hgl: "top1_is_loop_on B TB b0 g"
    assume "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    then obtain ft where hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f s"
      by (by100 blast)
    assume "\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)"
    then obtain gt where hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = g s"
      by (by100 blast)
    assume "\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = g s) \<longrightarrow>
               ft 1 = gt 1"
    hence hend_eq: "ft 1 = gt 1" using hft hftp hgt hgtp by (by100 blast)
    have hTE: "is_topology_on E TE" using hpc unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>E simply connected: ft \<simeq> gt.\<close>
    have hft': "top1_is_path_on E TE e0 (ft 1) ft" using hft .
    have hgt': "top1_is_path_on E TE e0 (ft 1) gt" using hgt hend_eq by simp
    have "top1_path_homotopic_on E TE e0 (ft 1) ft gt"
      by (rule simply_connected_paths_homotopic[OF assms(4) hft' hgt' assms(2)])
    \<comment> \<open>Apply p: p\<circ>ft \<simeq> p\<circ>gt.\<close>
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hTB: "is_topology_on B TB" by (rule hTB_outer)
    have hpft_pgt: "top1_path_homotopic_on B TB (p e0) (p (ft 1)) (p \<circ> ft) (p \<circ> gt)"
      by (rule continuous_preserves_path_homotopic[OF hTE hTB hp_cont
            \<open>top1_path_homotopic_on E TE e0 (ft 1) ft gt\<close>])
    \<comment> \<open>p\<circ>ft = f and p\<circ>gt = g on I_set. Use loop_agree_on_I.\<close>
    have hpft_f: "\<forall>s\<in>I_set. (p \<circ> ft) s = f s" using hftp by simp
    have hpgt_g: "\<forall>s\<in>I_set. (p \<circ> gt) s = g s" using hgtp by simp
    have hpe0: "p e0 = b0" using assms(3) .
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hpft1: "p (ft 1) = b0"
      using hftp h1I hfl unfolding top1_is_loop_on_def top1_is_path_on_def by simp
    have "top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)"
      using hpft_pgt hpe0 hpft1 by simp
    \<comment> \<open>p\<circ>ft agrees with f on I_set, p\<circ>gt agrees with g. Transfer homotopy.\<close>
    have hpft_loop: "top1_is_loop_on B TB b0 (p \<circ> ft)"
      using \<open>top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)\<close>
      unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
    have hf_loop_agree: "\<forall>s\<in>I_set. (p \<circ> ft) s = f s" using hftp by simp
    have hg_loop_agree: "\<forall>s\<in>I_set. (p \<circ> gt) s = g s" using hgtp by simp
    have hf_equiv_pft: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> ft)"
      using conjunct2[OF loop_agree_on_I[OF hfl hf_loop_agree]] .
    have hpgt_loop: "top1_is_loop_on B TB b0 (p \<circ> gt)"
      using \<open>top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)\<close>
      unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
    have hg_equiv_pgt: "top1_path_homotopic_on B TB b0 b0 g (p \<circ> gt)"
      using conjunct2[OF loop_agree_on_I[OF hgl hg_loop_agree]] .
    \<comment> \<open>Chain: f \<simeq> p\<circ>ft \<simeq> p\<circ>gt \<simeq> g.\<close>
    have hf_pft: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> ft)"
      by (rule hf_equiv_pft)
    have hpft_pgt': "top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)"
      using hpft_pgt hpe0 hpft1 by simp
    have hpgt_g': "top1_path_homotopic_on B TB b0 b0 (p \<circ> gt) g"
      by (rule Lemma_51_1_path_homotopic_sym[OF hg_equiv_pgt])
    have hf_pgt: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> gt)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTB hf_pft hpft_pgt'])
    thus "top1_path_homotopic_on B TB b0 b0 f g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTB _ hpgt_g'])
  qed
  \<comment> \<open>From Theorem 54.4 (lifting correspondence), get surjective \<phi>.\<close>
  obtain \<phi> where h\<phi>_mem: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
        \<phi> c \<in> {e\<in>E. p e = b0}"
      and h\<phi>_surj: "\<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}"
      and h\<phi>_lift: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
        \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
          \<and> top1_is_path_on E TE e0 (\<phi> c) ft
          \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    using Theorem_54_4_lifting_correspondence[OF assms(2,3,1) hpc assms(5)] by (by100 auto)
  \<comment> \<open>Injectivity from hinj + lift characterization.\<close>
  have h\<phi>_inj: "inj_on \<phi> (top1_fundamental_group_carrier B TB b0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier B TB b0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier B TB b0"
       and heq: "\<phi> c1 = \<phi> c2"
    \<comment> \<open>Extract representatives and lifts from \<phi>'s characterization.\<close>
    obtain f1 ft1 where hf1_in: "f1 \<in> c1" and hf1_loop: "top1_is_loop_on B TB b0 f1"
        and hft1: "top1_is_path_on E TE e0 (\<phi> c1) ft1"
        and hft1p: "\<forall>s\<in>I_set. p (ft1 s) = f1 s"
      using h\<phi>_lift[rule_format, OF hc1] by (by100 blast)
    obtain f2 ft2 where hf2_in: "f2 \<in> c2" and hf2_loop: "top1_is_loop_on B TB b0 f2"
        and hft2: "top1_is_path_on E TE e0 (\<phi> c2) ft2"
        and hft2p: "\<forall>s\<in>I_set. p (ft2 s) = f2 s"
      using h\<phi>_lift[rule_format, OF hc2] by (by100 blast)
    \<comment> \<open>Lifts end at same point since \<phi>(c1) = \<phi>(c2).\<close>
    have hft1_end: "top1_is_path_on E TE e0 (\<phi> c1) ft1" using hft1 .
    have hft2_end: "top1_is_path_on E TE e0 (\<phi> c1) ft2" using hft2 heq by simp
    \<comment> \<open>Apply hinj: lifts of f1, f2 end at same point \<Rightarrow> f1 \<simeq> f2.\<close>
    have "top1_path_homotopic_on B TB b0 b0 f1 f2"
    proof -
      \<comment> \<open>Lifts ft1, ft2 end at \<phi>(c1) = \<phi>(c2), so same point.\<close>
      have hft1_1: "ft1 1 = \<phi> c1" using hft1 unfolding top1_is_path_on_def by simp
      have hft2_1: "ft2 1 = \<phi> c2" using hft2 unfolding top1_is_path_on_def by simp
      have hend_eq: "ft1 1 = ft2 1" using hft1_1 hft2_1 heq by simp
      have hft1': "top1_is_path_on E TE e0 (ft1 1) ft1"
        using hft1 hft1_1 by simp
      have hft2': "top1_is_path_on E TE e0 (ft2 1) ft2"
        using hft2 hft2_1 by simp
      \<comment> \<open>Assemble for hinj.\<close>
      have hexists_ft: "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f1 s)"
        using hft1' hft1p by (by100 blast)
      have hexists_gt: "\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = f2 s)"
        using hft2' hft2p by (by100 blast)
      have hf1_path: "top1_is_path_on B TB b0 b0 f1"
        using hf1_loop unfolding top1_is_loop_on_def .
      have hf2_path: "top1_is_path_on B TB b0 b0 f2"
        using hf2_loop unfolding top1_is_loop_on_def .
      have hcov: "top1_covering_map_on E TE B TB p"
        using assms(1) .
      have he0: "e0 \<in> E" using assms(2) .
      have hpe0: "p e0 = b0" using assms(3) .
      have hall_eq: "\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f1 s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = f2 s) \<longrightarrow>
               ft 1 = gt 1"
      proof (intro allI impI)
        fix ft gt
        assume hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f1 s"
           and hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = f2 s"
        \<comment> \<open>ft lifts f1 from e0, ft1 also lifts f1 from e0 \<Rightarrow> ft(1) = ft1(1).\<close>
        have "ft 1 = ft1 1"
        proof -
          have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          have "\<forall>s\<in>I_set. ft s = ft1 s"
            by (rule Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf1_path hft hftp hft1' hft1p])
          thus ?thesis using h1I by (by100 blast)
        qed
        \<comment> \<open>gt lifts f2 from e0, ft2 also lifts f2 from e0 \<Rightarrow> gt(1) = ft2(1).\<close>
        moreover have "gt 1 = ft2 1"
        proof -
          have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          have "\<forall>s\<in>I_set. gt s = ft2 s"
            by (rule Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf2_path hgt hgtp hft2' hft2p])
          thus ?thesis using h1I by (by100 blast)
        qed
        ultimately show "ft 1 = gt 1" using hend_eq by simp
      qed
      show ?thesis using hinj hf1_loop hf2_loop hexists_ft hexists_gt hall_eq by blast
    qed
    \<comment> \<open>f1 \<simeq> f2 + f1 \<in> c1, f2 \<in> c2 \<Rightarrow> c1 = c2.\<close>
    obtain l1 where hl1: "top1_is_loop_on B TB b0 l1"
        and hc1_eq: "c1 = {h. top1_loop_equiv_on B TB b0 l1 h}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain l2 where hl2: "top1_is_loop_on B TB b0 l2"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on B TB b0 l2 h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hf1_equiv_l1: "top1_loop_equiv_on B TB b0 l1 f1"
      using hf1_in unfolding hc1_eq by simp
    have hf2_equiv_l2: "top1_loop_equiv_on B TB b0 l2 f2"
      using hf2_in unfolding hc2_eq by simp
    have hf1_f2: "top1_loop_equiv_on B TB b0 f1 f2"
      unfolding top1_loop_equiv_on_def
      using hf1_loop hf2_loop \<open>top1_path_homotopic_on B TB b0 b0 f1 f2\<close>
      by (by100 blast)
    have hl1_l2: "top1_loop_equiv_on B TB b0 l1 l2"
      by (rule top1_loop_equiv_on_trans[OF hTB_outer
            top1_loop_equiv_on_trans[OF hTB_outer hf1_equiv_l1 hf1_f2]
            top1_loop_equiv_on_sym[OF hf2_equiv_l2]])
    show "c1 = c2"
    proof -
      have "\<And>h. top1_loop_equiv_on B TB b0 l1 h \<longleftrightarrow> top1_loop_equiv_on B TB b0 l2 h"
        using hl1_l2 top1_loop_equiv_on_trans[OF hTB_outer]
              top1_loop_equiv_on_trans[OF hTB_outer top1_loop_equiv_on_sym[OF hl1_l2]]
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  show ?thesis unfolding bij_betw_def using h\<phi>_inj h\<phi>_surj by (by100 blast)
qed

text \<open>Helper: subspace of UNIV with top1_open_sets is top1_open_sets itself.\<close>
lemma subspace_topology_UNIV_self:
  "subspace_topology UNIV (T::'a set set) UNIV = T"
  unfolding subspace_topology_def by auto

text \<open>Helper: R is path-connected via the straight-line path t \<mapsto> (1-t)\<cdot>x + t\<cdot>y.\<close>
lemma top1_R_path_connected':
  "top1_path_connected_on (UNIV::real set) top1_open_sets"
proof -
  have hTop: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hpath: "\<forall>x::real\<in>UNIV. \<forall>y::real\<in>UNIV. \<exists>f. top1_is_path_on UNIV top1_open_sets x y f"
  proof (intro ballI)
    fix x y :: real
    assume "x \<in> UNIV" "y \<in> UNIV"
    let ?f = "\<lambda>t::real. (1-t)*x + t*y"
    have hfcont: "continuous_on UNIV ?f"
      by (intro continuous_intros)
    have hmap: "\<And>s. s \<in> I_set \<Longrightarrow> ?f s \<in> UNIV" by simp
    have hcont_sub: "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set)
          UNIV (subspace_topology UNIV top1_open_sets UNIV) ?f"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hfcont])
    have hI_top: "(subspace_topology UNIV top1_open_sets I_set) = I_top"
      unfolding top1_unit_interval_topology_def by rule
    have hUNIV_top: "(subspace_topology UNIV top1_open_sets UNIV) = top1_open_sets"
      by (rule subspace_topology_UNIV_self)
    have hcont: "top1_continuous_map_on I_set I_top UNIV top1_open_sets ?f"
      using hcont_sub unfolding hI_top hUNIV_top .
    have hstart: "?f 0 = x" by simp
    have hend: "?f 1 = y" by simp
    show "\<exists>f. top1_is_path_on UNIV top1_open_sets x y f"
      unfolding top1_is_path_on_def using hcont hstart hend by blast
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTop hpath by simp
qed

definition top1_slh_ext :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "top1_slh_ext f x0 p = (1 - snd p) * f (max 0 (min 1 (fst p))) + snd p * x0"

lemma top1_slh_ext_continuous:
  assumes "continuous_on I_set f"
  shows "continuous_on UNIV (top1_slh_ext f x0)"
proof -
  have h2: "continuous_on UNIV (\<lambda>x::real. f (max 0 (min 1 x)))"
    by (rule continuous_on_compose2[OF assms]) (intro continuous_intros, auto simp: top1_unit_interval_def)
  show ?thesis unfolding top1_slh_ext_def
    by (intro continuous_intros continuous_on_compose2[OF h2 continuous_on_fst]) auto
qed

lemma top1_slh_ext_agrees:
  "p \<in> I_set \<times> I_set \<Longrightarrow>
   top1_slh_ext f x0 p = (1 - snd p) * f (fst p) + snd p * x0"
  unfolding top1_slh_ext_def top1_unit_interval_def by auto

lemma top1_continuous_map_on_II_to_UNIV:
  fixes F :: "real \<times> real \<Rightarrow> real"
  assumes "continuous_on UNIV F"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology (UNIV::real set) top1_open_sets F"
proof -
  have "\<forall>V\<in>(top1_open_sets :: real set set). {p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology"
  proof
    fix V :: "real set" assume "V \<in> (top1_open_sets :: real set set)"
    hence hVo: "open V" unfolding top1_open_sets_def by blast
    have hFV: "open (F -` V)" by (rule open_vimage[OF hVo assms])
    hence "F -` V \<in> (top1_open_sets :: (real\<times>real) set set)" unfolding top1_open_sets_def by blast
    hence "F -` V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
      using product_topology_on_open_sets_real2 by metis
    hence "(I_set \<times> I_set) \<inter> (F -` V) \<in> product_topology_on I_top I_top"
      unfolding II_topology_eq_subspace subspace_topology_def by blast
    moreover have "{p \<in> I_set \<times> I_set. F p \<in> V} = (I_set \<times> I_set) \<inter> (F -` V)" by auto
    ultimately show "{p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology" unfolding II_topology_def by simp
  qed
  thus ?thesis unfolding top1_continuous_map_on_def by simp
qed

text \<open>Helper: R is simply connected — any loop f is homotopic to constant via
  F(s, t) = (1 - t) * f(s) + t * x0 (straight-line homotopy to the basepoint).\<close>
lemma top1_R_simply_connected':
  "top1_simply_connected_on (UNIV::real set) top1_open_sets"
proof -
  have hpc: "top1_path_connected_on (UNIV::real set) top1_open_sets"
    by (rule top1_R_path_connected')
  have hloops: "\<forall>x0\<in>(UNIV::real set). \<forall>f. top1_is_loop_on UNIV top1_open_sets x0 f \<longrightarrow>
        top1_path_homotopic_on UNIV top1_open_sets x0 x0 f (top1_constant_path x0)"
  proof (intro ballI allI impI)
    fix x0 :: real and f assume hloop: "top1_is_loop_on UNIV top1_open_sets x0 f"
    have hfcont: "top1_continuous_map_on I_set I_top UNIV top1_open_sets f"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
    \<comment> \<open>Use top1_slh_ext as the homotopy (agrees with (1-t)*f(s)+t*x0 on I\<times>I).\<close>
    have hf_cont_I: "continuous_on I_set f"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "real set" assume hBo: "open B"
      have "B \<in> top1_open_sets" using hBo unfolding top1_open_sets_def by blast
      hence hpre: "{s \<in> I_set. f s \<in> B} \<in> I_top"
        using hfcont unfolding top1_continuous_map_on_def by blast
      hence "{s \<in> I_set. f s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def .
      then obtain W where hW: "W \<in> top1_open_sets" and heq: "{s \<in> I_set. f s \<in> B} = I_set \<inter> W"
        unfolding subspace_topology_def by blast
      have "open W" using hW unfolding top1_open_sets_def by blast
      moreover have "W \<inter> I_set = f -` B \<inter> I_set" using heq by auto
      ultimately show "\<exists>A. open A \<and> A \<inter> I_set = f -` B \<inter> I_set" by blast
    qed
    have hext_cont: "continuous_on UNIV (top1_slh_ext f x0)"
      by (rule top1_slh_ext_continuous[OF hf_cont_I])
    have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology UNIV top1_open_sets (top1_slh_ext f x0)"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hext_cont])
    have hfpath: "top1_is_path_on UNIV top1_open_sets x0 x0 f"
      using hloop unfolding top1_is_loop_on_def .
    have hTR: "is_topology_on (UNIV :: real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hcpath: "top1_is_path_on UNIV top1_open_sets x0 x0 (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTR]) simp
    have hFs0: "\<forall>s\<in>I_set. top1_slh_ext f x0 (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "top1_slh_ext f x0 (s, 0) = (1 - 0) * f s + 0 * x0"
        using top1_slh_ext_agrees[of "(s, 0)"] hs unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (s, 0) = f s" by simp
    qed
    have hFs1: "\<forall>s\<in>I_set. top1_slh_ext f x0 (s, 1) = (\<lambda>_. x0) s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "top1_slh_ext f x0 (s, 1) = (1 - 1) * f s + 1 * x0"
        using top1_slh_ext_agrees[of "(s, 1)"] hs unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (s, 1) = x0" by simp
    qed
    have hF0t: "\<forall>t\<in>I_set. top1_slh_ext f x0 (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have "top1_slh_ext f x0 (0, t) = (1 - t) * f 0 + t * x0"
        using top1_slh_ext_agrees[of "(0, t)"] ht unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (0, t) = x0" using hf0 by (simp add: algebra_simps)
    qed
    have hF1t: "\<forall>t\<in>I_set. top1_slh_ext f x0 (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have "top1_slh_ext f x0 (1, t) = (1 - t) * f 1 + t * x0"
        using top1_slh_ext_agrees[of "(1, t)"] ht unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (1, t) = x0" using hf1 by (simp add: algebra_simps)
    qed
    show "top1_path_homotopic_on UNIV top1_open_sets x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def top1_constant_path_def
      using hfpath hcpath hF_cont hFs0 hFs1 hF0t hF1t
      unfolding top1_is_path_on_def top1_constant_path_def by blast
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc hloops by blast
qed

text \<open>Helper: the fiber p^{-1}(b_0) of the canonical S^1 covering is Z.
  top1_R_to_S1 x = (1, 0) iff cos(2\<pi>x) = 1 and sin(2\<pi>x) = 0 iff 2\<pi>x = 2\<pi>n, i.e. x = n \<in> Z.\<close>
lemma top1_R_to_S1_fiber_is_Z':
  "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n | n. True}"
proof (intro subset_antisym subsetI)
  fix x :: real assume "x \<in> {x. top1_R_to_S1 x = (1, 0)}"
  hence hcos: "cos (2 * pi * x) = 1" and hsin: "sin (2 * pi * x) = 0"
    unfolding top1_R_to_S1_def by simp_all
  from hcos obtain n :: int where hn: "2 * pi * x = 2 * pi * of_int n"
    by (auto simp: cos_one_2pi_int)
  have "x = of_int n" using hn by simp
  thus "x \<in> {of_int n | n. True}" by blast
next
  fix x :: real assume "x \<in> {of_int n | n. True}"
  then obtain n :: int where hn: "x = of_int n" by blast
  have "cos (2 * pi * of_int n) = 1"
    using cos_int_2pin by (simp add: mult.commute)
  moreover have "sin (2 * pi * of_int n) = 0"
    using sin_int_2pin by (simp add: mult.commute)
  ultimately show "x \<in> {x. top1_R_to_S1 x = (1, 0)}"
    unfolding top1_R_to_S1_def using hn by simp
qed

text \<open>Periodicity of the covering map: p(x + n) = p(x) for integer n.
  This is the key property enabling the homomorphism proof for \<pi>_1(S^1) \<cong> Z.\<close>
lemma top1_R_to_S1_int_shift:
  "top1_R_to_S1 (x + of_int n) = top1_R_to_S1 x"
proof -
  have hexp: "2 * pi * (x + of_int n) = 2 * pi * x + (2 * pi) * of_int n"
    by (simp add: algebra_simps)
  have hc: "cos ((2 * pi) * of_int n) = 1" by (rule cos_int_2pin)
  have hs: "sin ((2 * pi) * of_int n) = 0" by (rule sin_int_2pin)
  have hcos: "cos (2 * pi * (x + of_int n)) = cos (2 * pi * x)"
    by (simp add: hexp cos_add hc hs)
  have hsin: "sin (2 * pi * (x + of_int n)) = sin (2 * pi * x)"
    by (simp add: hexp sin_add hc hs)
  show ?thesis unfolding top1_R_to_S1_def using hcos hsin by (by100 simp)
qed

lemma top1_R_to_S1_int_shift':
  "top1_R_to_S1 (of_int n + x) = top1_R_to_S1 x"
  using top1_R_to_S1_int_shift[of x n] by (simp add: add.commute)

text \<open>Key property: the translated lift f'(s) = n + f(s) covers the same base path as f.
  p(n + f(s)) = p(f(s)) by periodicity.\<close>
lemma top1_R_to_S1_translate_lift:
  "top1_R_to_S1 \<circ> (\<lambda>s. of_int n + f s) = top1_R_to_S1 \<circ> f"
  by (rule ext) (simp add: top1_R_to_S1_int_shift')

text \<open>If gtilde is a lift of g (loop at b0) starting at 0, then
  (\<lambda>s. of_int n + gtilde s) is a lift of g starting at n, by periodicity.\<close>
lemma top1_R_to_S1_translated_lift_is_lift:
  assumes hgt: "top1_is_path_on UNIV top1_open_sets (0::real) (gtilde 1) gtilde"
      and hgtp: "\<forall>s\<in>I_set. top1_R_to_S1 (gtilde s) = g s"
  shows "\<forall>s\<in>I_set. top1_R_to_S1 (of_int n + gtilde s) = g s"
  using hgtp by (simp add: top1_R_to_S1_int_shift')

text \<open>The translated lift starts at n (when gtilde starts at 0).\<close>
lemma top1_R_to_S1_translated_lift_start:
  assumes "gtilde 0 = (0::real)"
  shows "(of_int n + gtilde 0) = of_int n"
  using assms by simp

text \<open>The translated lift ends at n + gtilde(1).\<close>
lemma top1_R_to_S1_translated_lift_end:
  "(of_int n + gtilde 1) = of_int n + gtilde 1" by simp

(** from \<S>54 Theorem 54.5: fundamental group of S^1 is isomorphic to Z.
    Munkres' proof: use covering p: R \<rightarrow> S^1 (Theorem 53.1). Since R is simply
    connected, the lifting correspondence (Theorem 54.4) is bijective onto
    p^{-1}(b_0) = Z. Then show it's a homomorphism. **)
theorem Theorem_54_5:
  "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
    (UNIV::int set)"
proof -
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have h0R: "(0::real) \<in> UNIV" by simp
  have hp0: "top1_R_to_S1 0 = (1, 0)"
    unfolding top1_R_to_S1_def by simp
  have hRsc: "top1_simply_connected_on (UNIV::real set) top1_open_sets"
    by (rule top1_R_simply_connected')
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  qed
  obtain \<phi>' where hbij: "bij_betw \<phi>'
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)}"
    using Theorem_54_4_bijective_simply_connected[OF hcov h0R hp0 hRsc hTS1] by blast
  have hfiber_Z: "\<exists>\<psi>. bij_betw \<psi> {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
  proof -
    have hfib_eq: "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n | n::int. True}"
      using top1_R_to_S1_fiber_is_Z' .
    have hinj: "inj_on (\<lambda>x::real. floor x) {x::real. top1_R_to_S1 x = (1, 0)}"
    proof (rule inj_onI)
      fix a b assume "a \<in> {x. top1_R_to_S1 x = (1, 0)}" "b \<in> {x. top1_R_to_S1 x = (1, 0)}"
      hence "\<exists>n. a = of_int n" "\<exists>n. b = of_int n" using hfib_eq by auto
      thus "floor a = floor b \<Longrightarrow> a = b" by auto
    qed
    have hsurj: "(\<lambda>x::real. floor x) ` {x::real. top1_R_to_S1 x = (1, 0)} = UNIV"
    proof
      show "(\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)} \<subseteq> UNIV" by simp
      show "UNIV \<subseteq> (\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)}"
      proof
        fix n :: int assume "n \<in> UNIV"
        have "of_int n \<in> {x::real. top1_R_to_S1 x = (1, 0)}" using hfib_eq by auto
        moreover have "floor (of_int n :: real) = n" by simp
        ultimately show "n \<in> (\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)}" by force
      qed
    qed
    show ?thesis using hinj hsurj unfolding bij_betw_def by auto
  qed
  obtain \<psi> where h\<psi>: "bij_betw \<psi> {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
    using hfiber_Z by blast
  have hcomp: "bij_betw (\<psi> \<circ> \<phi>')
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
    by (rule bij_betw_trans[OF hbij h\<psi>])
  thus ?thesis by blast
qed

text \<open>The integers Z as an additive abelian group (moved here to support Theorem_54_5_iso).\<close>
definition top1_Z_group :: "int set" where
  "top1_Z_group = UNIV"

definition top1_Z_mul :: "int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Z_mul a b = a + b"

definition top1_Z_id :: "int" where
  "top1_Z_id = 0"

definition top1_Z_invg :: "int \<Rightarrow> int" where
  "top1_Z_invg a = - a"

lemma top1_Z_is_abelian_group:
  "top1_is_abelian_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
  unfolding top1_is_abelian_group_on_def top1_is_group_on_def
            top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def
  by auto

(** Strengthened version: \<pi>_1(S^1, (1,0)) is isomorphic to Z as groups (not just bijective). **)
theorem Theorem_54_5_iso:
  "top1_groups_isomorphic_on
     (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
     (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
     top1_Z_group
     top1_Z_mul"
proof -
  \<comment> \<open>Munkres 54.5: Use covering p: R \<rightarrow> S^1, with R simply connected.\<close>
  \<comment> \<open>Step 1: \<phi> is bijective (from Theorem 54.4 + R simply connected).\<close>
  have hbij: "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (UNIV::int set)"
    using Theorem_54_5 by (by100 blast)
  \<comment> \<open>Step 2: \<phi> is a homomorphism.
     For lifts ftilde(1) = n, gtilde(1) = m, define g'(s) = n + gtilde(s).
     Since p(n + x) = p(x), g' lifts g starting at n. So ftilde * g' lifts f * g,
     ending at n + m. Hence \<phi>([f]*[g]) = n + m = \<phi>([f]) + \<phi>([g]).\<close>
  \<comment> \<open>The bijection maps endpoints of lifts to integers.
     Homomorphism: endpoints add because translated lifts concatenate.\<close>
  \<comment> \<open>We construct \<phi> from the covering map: \<phi>([f]) = lift endpoint.
     Homomorphism follows from the key lemma: translated lifts concatenate.
     Specifically: if ftilde lifts f from 0 to n, and gtilde lifts g from 0 to m,
     then (\<lambda>s. n + gtilde s) lifts g from n to n+m (using p(n+x) = p(x)),
     and ftilde * (\<lambda>s. n + gtilde s) lifts f*g from 0 to n+m.\<close>
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have hp0: "top1_R_to_S1 0 = (1, 0)"
    unfolding top1_R_to_S1_def by simp
  have h0R: "(0::real) \<in> (UNIV::real set)" by simp
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
            simplified]]) simp
  \<comment> \<open>Step 1: Define \<phi> via lifting correspondence (already have bijection).\<close>
  \<comment> \<open>The lifting correspondence sends [f] to the endpoint of the unique lift
     starting at 0. This endpoint lies in p^{-1}(1,0) = Z.\<close>
  obtain \<phi>' where h\<phi>'_bij: "bij_betw \<phi>'
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)}"
    using Theorem_54_4_bijective_simply_connected[OF hcov h0R hp0
          top1_R_simply_connected' hTS1] by blast
  \<comment> \<open>\<phi>'([f]) is the endpoint of the lift of f. Since the endpoint is an integer,
     define \<phi>([f]) = floor(\<phi>'([f])).\<close>
  define \<phi> where "\<phi> = (\<lambda>c. \<lfloor>\<phi>' c\<rfloor>)"
  \<comment> \<open>Step 2: \<phi> is bijective (composition of bijections).\<close>
  have h\<phi>_bij: "bij_betw \<phi>
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (UNIV::int set)"
  proof -
    have hfib: "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n |n::int. True}"
      using top1_R_to_S1_fiber_is_Z' .
    have hfloor_inj: "inj_on floor {x::real. top1_R_to_S1 x = (1, 0)}"
    proof (rule inj_onI)
      fix a b :: real
      assume "a \<in> {x. top1_R_to_S1 x = (1, 0)}" "b \<in> {x. top1_R_to_S1 x = (1, 0)}"
      hence "a \<in> {of_int n |n::int. True}" "b \<in> {of_int n |n::int. True}"
        using hfib by (by100 blast)+
      then obtain na nb :: int where hna: "a = of_int na" and hnb: "b = of_int nb"
        by (by100 auto)
      assume "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
      thus "a = b" using hna hnb by (by100 simp)
    qed
    have hfloor_surj: "floor ` {x::real. top1_R_to_S1 x = (1, 0)} = (UNIV::int set)"
    proof
      show "floor ` {x::real. top1_R_to_S1 x = (1, 0)} \<subseteq> UNIV" by (by100 simp)
    next
      show "UNIV \<subseteq> floor ` {x::real. top1_R_to_S1 x = (1, 0)}"
      proof
        fix n :: int
        have "of_int n \<in> {x::real. top1_R_to_S1 x = (1, 0)}" using hfib by (by100 auto)
        moreover have "\<lfloor>of_int n :: real\<rfloor> = n" by simp
        ultimately show "n \<in> floor ` {x::real. top1_R_to_S1 x = (1, 0)}" by (by100 force)
      qed
    qed
    have hfloor_bij: "bij_betw floor {x::real. top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
      unfolding bij_betw_def using hfloor_inj hfloor_surj by (by100 blast)
    have heq: "{x \<in> (UNIV::real set). top1_R_to_S1 x = (1, 0)} = {x::real. top1_R_to_S1 x = (1, 0)}"
      by (by100 simp)
    have hcomp: "bij_betw (floor \<circ> \<phi>')
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
      by (rule bij_betw_trans[OF h\<phi>'_bij[unfolded heq] hfloor_bij])
    have "\<phi> = floor \<circ> \<phi>'" unfolding \<phi>_def comp_def by (rule refl)
    show ?thesis using hcomp unfolding \<open>\<phi> = floor \<circ> \<phi>'\<close> .
  qed
  \<comment> \<open>Step 3: \<phi> is a homomorphism.
     Key: if lift of f from 0 ends at n and lift of g from 0 ends at m,
     then lift of f*g from 0 ends at n+m.\<close>
  have h\<phi>_hom: "\<forall>c\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
      \<forall>d\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
      \<phi> (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d)
      = \<phi> c + \<phi> d"
  proof (intro ballI)
    fix c d
    assume hc: "c \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
       and hd: "d \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
    \<comment> \<open>Let f, g be representative loops. ftilde, gtilde their lifts from 0.
       n = ftilde(1) (integer), m = gtilde(1) (integer).
       Translated lift: s \<mapsto> n + gtilde(s) covers g starting at n.
       Concatenation of ftilde with translated-gtilde covers f*g from 0 to n+m.
       By uniqueness of lifts, the lift of f*g from 0 ends at n+m.
       \<phi>(c*d) = floor(n+m) = floor(n) + floor(m) = \<phi>(c) + \<phi>(d).\<close>
    show "\<phi> (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d)
        = \<phi> c + \<phi> d"
      sorry \<comment> \<open>Translated lift concatenation + uniqueness.\<close>
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
      top1_group_hom_on_def top1_Z_group_def top1_Z_mul_def
    apply (intro exI[of _ \<phi>] conjI)
    using h\<phi>_bij unfolding bij_betw_def apply (by100 blast)
    using h\<phi>_hom apply (by100 blast)
    using h\<phi>_bij apply (by100 blast)
    done
qed

section \<open>\<S>55 Retractions and Fixed Points\<close>

text \<open>Retraction: r: X \<rightarrow> A continuous with r|A = id_A.\<close>
definition top1_is_retraction_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_retraction_on X TX A r \<longleftrightarrow>
     A \<subseteq> X \<and>
     top1_continuous_map_on X TX A (subspace_topology X TX A) r \<and>
     (\<forall>a\<in>A. r a = a)"

text \<open>A is a retract of X if there exists a retraction X \<rightarrow> A.\<close>
definition top1_retract_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_retract_of_on X TX A \<longleftrightarrow> (\<exists>r. top1_is_retraction_on X TX A r)"

lemma top1_is_retraction_on_subset:
  assumes "top1_is_retraction_on X TX A r"
  shows "A \<subseteq> X"
  using assms unfolding top1_is_retraction_on_def by blast

lemma top1_is_retraction_on_continuous:
  assumes "top1_is_retraction_on X TX A r"
  shows "top1_continuous_map_on X TX A (subspace_topology X TX A) r"
  using assms unfolding top1_is_retraction_on_def by blast

lemma top1_is_retraction_on_fixes_A:
  assumes "top1_is_retraction_on X TX A r" and "a \<in> A"
  shows "r a = a"
  using assms unfolding top1_is_retraction_on_def by blast

text \<open>Every space is a retract of itself (via identity).\<close>
lemma top1_retract_self:
  assumes hTX: "is_topology_on X TX"
  shows "top1_retract_of_on X TX X"
proof -
  have hX: "X \<in> TX" using hTX unfolding is_topology_on_def by blast
  have hid: "top1_continuous_map_on X TX X (subspace_topology X TX X) id"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x \<in> X. id x \<in> X" by simp
  next
    show "\<forall>V \<in> subspace_topology X TX X. {x \<in> X. id x \<in> V} \<in> TX"
    proof
      fix V assume hV: "V \<in> subspace_topology X TX X"
      then obtain U where hU: "U \<in> TX" and hVeq: "V = X \<inter> U"
        unfolding subspace_topology_def by blast
      have "X \<inter> U \<in> TX" by (rule topology_inter2[OF hTX hX hU])
      hence "V \<in> TX" using hVeq by simp
      moreover have "{x \<in> X. id x \<in> V} = V" using hVeq by auto
      ultimately show "{x \<in> X. id x \<in> V} \<in> TX" by simp
    qed
  qed
  have hret: "top1_is_retraction_on X TX X id"
    unfolding top1_is_retraction_on_def using hid by simp
  thus ?thesis unfolding top1_retract_of_on_def by blast
qed

text \<open>Helper: fst is continuous from any subspace of R^2 to R.\<close>
lemma top1_fst_continuous_R2_subspace:
  fixes S :: "(real \<times> real) set"
  shows "top1_continuous_map_on S
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
    (UNIV::real set) top1_open_sets fst"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "fst p \<in> (UNIV::real set)" by simp
next
  fix V :: "real set" assume hV: "V \<in> top1_open_sets"
  have hVo: "open V" using hV unfolding top1_open_sets_def by blast
  have hBxU_open: "open (V \<times> (UNIV::real set))" by (rule open_Times[OF hVo open_UNIV])
  have hBxU_prod: "V \<times> (UNIV::real set) \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "V \<times> (UNIV::real set) \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hBxU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have "{p \<in> S. fst p \<in> V} = S \<inter> (V \<times> UNIV)" by (auto simp: mem_Times_iff prod.collapse[symmetric])
  thus "{p \<in> S. fst p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def using hBxU_prod by blast
qed

lemma top1_snd_continuous_R2_subspace:
  fixes S :: "(real \<times> real) set"
  shows "top1_continuous_map_on S
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
    (UNIV::real set) top1_open_sets snd"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "snd p \<in> (UNIV::real set)" by simp
next
  fix V :: "real set" assume hV: "V \<in> top1_open_sets"
  have hVo: "open V" using hV unfolding top1_open_sets_def by blast
  have hUxB_open: "open ((UNIV::real set) \<times> V)" by (rule open_Times[OF open_UNIV hVo])
  have hUxB_prod: "(UNIV::real set) \<times> V \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "(UNIV::real set) \<times> V \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUxB_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have "{p \<in> S. snd p \<in> V} = S \<inter> (UNIV \<times> V)" by (auto simp: mem_Times_iff prod.collapse[symmetric])
  thus "{p \<in> S. snd p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def using hUxB_prod by blast
qed

text \<open>Helper: restriction of continuous map to subspace domain.\<close>
lemma top1_continuous_map_on_subspace_restrict:
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
      and hAX: "A \<subseteq> X"
  shows "top1_continuous_map_on A (subspace_topology X TX A) Y TY f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix a assume "a \<in> A"
  hence "a \<in> X" using hAX by blast
  thus "f a \<in> Y" using hcont unfolding top1_continuous_map_on_def by blast
next
  fix V assume hV: "V \<in> TY"
  have "{a \<in> X. f a \<in> V} \<in> TX"
    using hcont hV unfolding top1_continuous_map_on_def by blast
  moreover have "{a \<in> A. f a \<in> V} = A \<inter> {a \<in> X. f a \<in> V}"
    using hAX by auto
  ultimately show "{a \<in> A. f a \<in> V} \<in> subspace_topology X TX A"
    unfolding subspace_topology_def by blast
qed

text \<open>The closed disc B^2 and unit sphere S^1 as subspaces of R^2.\<close>
definition top1_B2 :: "(real \<times> real) set" where
  "top1_B2 = {p. fst p ^ 2 + snd p ^ 2 \<le> 1}"

definition top1_B2_topology :: "(real \<times> real) set set" where
  "top1_B2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_B2"

text \<open>Helper: if f : X \<rightarrow> A is continuous (with subspace topology from ambient Z),
  and A \<subseteq> B \<subseteq> Z, then f : X \<rightarrow> B is also continuous (with subspace topology from Z).\<close>
lemma top1_continuous_map_on_codomain_enlarge:
  assumes hcont: "top1_continuous_map_on X TX A (subspace_topology Z TZ A) f"
      and hAB: "A \<subseteq> B" and hBZ: "B \<subseteq> Z"
  shows "top1_continuous_map_on X TX B (subspace_topology Z TZ B) f"
proof -
  have hfA: "\<forall>x\<in>X. f x \<in> A"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hfB: "\<forall>x\<in>X. f x \<in> B" using hfA hAB by blast
  have hpreimage: "\<forall>V\<in>subspace_topology Z TZ B. {x\<in>X. f x \<in> V} \<in> TX"
  proof (intro ballI)
    fix V assume hV: "V \<in> subspace_topology Z TZ B"
    obtain U where hU: "U \<in> TZ" and hV_eq: "V = B \<inter> U"
      using hV unfolding subspace_topology_def by blast
    have hAU_in: "A \<inter> U \<in> subspace_topology Z TZ A"
      unfolding subspace_topology_def using hU by blast
    have hpre_eq: "{x\<in>X. f x \<in> V} = {x\<in>X. f x \<in> A \<inter> U}"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x\<in>X. f x \<in> V} \<longleftrightarrow> x \<in> {x\<in>X. f x \<in> A \<inter> U}"
        using hfA hAB hV_eq by auto
    qed
    have "{x\<in>X. f x \<in> A \<inter> U} \<in> TX"
      using hcont hAU_in unfolding top1_continuous_map_on_def by blast
    thus "{x\<in>X. f x \<in> V} \<in> TX" using hpre_eq by simp
  qed
  show ?thesis
    unfolding top1_continuous_map_on_def using hfB hpreimage by blast
qed

(** from \<S>55 Lemma 55.1: if A is a retract of X, then (\<pi>_1 A, x0) \<rightarrow> (\<pi>_1 X, x0)
    is injective (induced by inclusion) **)
lemma Lemma_55_1_retract_injective:
  assumes hret: "top1_retract_of_on X TX A"
      and hx0A: "x0 \<in> A"
      and hf_loop: "top1_is_loop_on A (subspace_topology X TX A) x0 f"
      and hg_loop: "top1_is_loop_on A (subspace_topology X TX A) x0 g"
      and hfg_hom: "top1_path_homotopic_on X TX x0 x0 f g"
  shows "top1_path_homotopic_on A (subspace_topology X TX A) x0 x0 f g"
proof -
  obtain r where hr: "top1_is_retraction_on X TX A r"
    using hret unfolding top1_retract_of_on_def by blast
  have hr_cont: "top1_continuous_map_on X TX A (subspace_topology X TX A) r"
    using hr unfolding top1_is_retraction_on_def by blast
  have hr_fix: "\<forall>a\<in>A. r a = a"
    using hr unfolding top1_is_retraction_on_def by blast
  obtain F where hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s"
      and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0t: "\<forall>t\<in>I_set. F (0, t) = x0"
      and hF1t: "\<forall>t\<in>I_set. F (1, t) = x0"
    using hfg_hom unfolding top1_path_homotopic_on_def by blast
  have hf_path: "top1_is_path_on A (subspace_topology X TX A) x0 x0 f"
    using hf_loop unfolding top1_is_loop_on_def .
  have hg_path: "top1_is_path_on A (subspace_topology X TX A) x0 x0 g"
    using hg_loop unfolding top1_is_loop_on_def .
  let ?G = "\<lambda>p. r (F p)"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology A (subspace_topology X TX A) ?G"
    using top1_continuous_map_on_comp[OF hFcont hr_cont] by (simp add: comp_def)
  have hf_in_A: "\<forall>s\<in>I_set. f s \<in> A"
    using hf_path unfolding top1_is_path_on_def top1_continuous_map_on_def by blast
  have hg_in_A: "\<forall>s\<in>I_set. g s \<in> A"
    using hg_path unfolding top1_is_path_on_def top1_continuous_map_on_def by blast
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "F (s, 0) = f s" using hs hFs0 by blast
    hence "r (F (s, 0)) = r (f s)" by simp
    also have "... = f s" using hr_fix hf_in_A hs by blast
    finally show "?G (s, 0) = f s" by simp
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = g s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "F (s, 1) = g s" using hs hFs1 by blast
    hence "r (F (s, 1)) = r (g s)" by simp
    also have "... = g s" using hr_fix hg_in_A hs by blast
    finally show "?G (s, 1) = g s" by simp
  qed
  have hG0t: "\<forall>t\<in>I_set. ?G (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "F (0, t) = x0" using ht hF0t by blast
    hence "r (F (0, t)) = r x0" by simp
    also have "... = x0" using hr_fix hx0A by blast
    finally show "?G (0, t) = x0" by simp
  qed
  have hG1t: "\<forall>t\<in>I_set. ?G (1, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "F (1, t) = x0" using ht hF1t by blast
    hence "r (F (1, t)) = r x0" by simp
    also have "... = x0" using hr_fix hx0A by blast
    finally show "?G (1, t) = x0" by simp
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hf_path hg_path hGcont hGs0 hGs1 hG0t hG1t by blast
qed

text \<open>Helper: \<pi>_1(S^1) is nontrivial — follows from Theorem 54.5 since Z has \<ge> 2 elements.\<close>
lemma top1_S1_fundamental_group_nontrivial:
  "\<exists>f g. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
       \<and> top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g
       \<and> \<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
proof -
  obtain \<phi> where hbij: "bij_betw \<phi>
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
    using Theorem_54_5 by blast
  \<comment> \<open>Since UNIV::int has \<ge> 2 elements and \<phi> is a bijection, the carrier has \<ge> 2 elements.
      Each element is an equivalence class of a loop; distinct classes give non-homotopic loops.\<close>
  obtain c1 c2 where hc1: "c1 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      and hc2: "c2 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      and hne: "c1 \<noteq> c2"
  proof -
    have "card (UNIV::int set) \<noteq> 1" by simp
    hence "card (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) \<noteq> 1"
      using bij_betw_same_card[OF hbij] by simp
    hence "\<exists>x y. x \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)
               \<and> y \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0) \<and> x \<noteq> y"
    proof -
      have hsurj: "\<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0) = UNIV"
        using hbij unfolding bij_betw_def by blast
      have hinj: "inj_on \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))"
        using hbij unfolding bij_betw_def by blast
      have h0mem: "(0::int) \<in> \<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        using hsurj by blast
      obtain xa where hxa_mem: "xa \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          and hxa: "\<phi> xa = 0"
        using h0mem by (auto simp: image_iff)
      have h1mem: "(1::int) \<in> \<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        using hsurj by blast
      obtain xb where hxb_mem: "xb \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          and hxb: "\<phi> xb = 1"
        using h1mem by (auto simp: image_iff)
      have "xa \<noteq> xb" using hxa hxb by (metis zero_neq_one)
      thus ?thesis using hxa_mem hxb_mem by blast
    qed
    thus ?thesis using that by blast
  qed
  \<comment> \<open>Each class is {g. f \<simeq>_p g} for some loop f at (1,0). Pick representatives.\<close>
  obtain f where hf: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
      and hc1_eq: "c1 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g}"
    using hc1 unfolding top1_fundamental_group_carrier_def by blast
  obtain g where hg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
      and hc2_eq: "c2 = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h}"
    using hc2 unfolding top1_fundamental_group_carrier_def by blast
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using hTR2' unfolding hUU .
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2], simp)
  qed
  \<comment> \<open>Since c1 \<ne> c2, f and g are not loop-equivalent, i.e., not path-homotopic.\<close>
  have hne_eq: "\<not> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g"
  proof (rule ccontr)
    assume "\<not> \<not> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g"
    hence heq: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g" by simp
    have "c1 \<subseteq> c2"
    proof
      fix h assume "h \<in> c1"
      hence hfh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f h" using hc1_eq by blast
      have hgf: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g f"
        by (rule top1_loop_equiv_on_sym[OF heq])
      have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h"
        by (rule top1_loop_equiv_on_trans[OF hTS1 hgf hfh])
      thus "h \<in> c2" using hc2_eq by blast
    qed
    moreover have "c2 \<subseteq> c1"
    proof
      fix h assume "h \<in> c2"
      hence hgh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h" using hc2_eq by blast
      have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f h"
        by (rule top1_loop_equiv_on_trans[OF hTS1 heq hgh])
      thus "h \<in> c1" using hc1_eq by blast
    qed
    ultimately have "c1 = c2" by blast
    thus False using hne by blast
  qed
  hence hnot_pho: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using hf hg unfolding top1_loop_equiv_on_def by blast
  show ?thesis using hf hg hnot_pho by blast
qed

text \<open>Helper: B^2 is convex.\<close>
lemma top1_B2_convex:
  assumes hp: "p \<in> top1_B2" and hq: "q \<in> top1_B2" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
  shows "((1-t) * fst p + t * fst q, (1-t) * snd p + t * snd q) \<in> top1_B2"
proof -
  let ?a = "fst p" and ?b = "snd p" and ?c = "fst q" and ?d = "snd q"
  have hp2: "?a^2 + ?b^2 \<le> 1" using hp unfolding top1_B2_def by simp
  have hq2: "?c^2 + ?d^2 \<le> 1" using hq unfolding top1_B2_def by simp
  have hs: "0 \<le> 1 - t" using ht1 by simp
  \<comment> \<open>Use: ((1-t)a+tc)^2 + ((1-t)b+td)^2
       = (1-t)^2(a^2+b^2) + 2t(1-t)(ac+bd) + t^2(c^2+d^2)
       \<le> (1-t)^2 + 2t(1-t)|ac+bd| + t^2
       \<le> (1-t)^2 + 2t(1-t) + t^2 = 1.
     The last step uses |ac+bd| \<le> 1, which follows from Cauchy-Schwarz:
       |ac+bd| \<le> sqrt(a^2+b^2)*sqrt(c^2+d^2) \<le> 1.\<close>
  \<comment> \<open>Cauchy-Schwarz: (ac+bd)^2 \<le> (a^2+b^2)(c^2+d^2), from (ad-bc)^2 \<ge> 0.\<close>
  have hnn: "0 \<le> (?a * ?d - ?b * ?c)^2" by simp
  have hCS: "(?a * ?c + ?b * ?d)^2 \<le> (?a^2 + ?b^2) * (?c^2 + ?d^2)"
  proof -
    have "(?a * ?c + ?b * ?d)^2 + (?a * ?d - ?b * ?c)^2
          = (?a^2 + ?b^2) * (?c^2 + ?d^2)"
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis using hnn by linarith
  qed
  have hprod_le1: "(?a^2 + ?b^2) * (?c^2 + ?d^2) \<le> 1"
  proof -
    have "0 \<le> ?a^2 + ?b^2" by (simp add: sum_power2_ge_zero)
    thus ?thesis using hp2 hq2 by (simp add: mult_le_one)
  qed
  have hCS_le1: "(?a * ?c + ?b * ?d)^2 \<le> 1"
    using hCS hprod_le1 by linarith
  \<comment> \<open>From x^2 \<le> 1 derive -1 \<le> x \<le> 1 via (1-x)(1+x) = 1 - x^2 \<ge> 0.\<close>
  have hdiff: "0 \<le> 1 - (?a * ?c + ?b * ?d)^2" using hCS_le1 by linarith
  have hprod: "0 \<le> (1 - (?a * ?c + ?b * ?d)) * (1 + (?a * ?c + ?b * ?d))"
  proof -
    have "(1 - (?a * ?c + ?b * ?d)) * (1 + (?a * ?c + ?b * ?d))
          = 1 - (?a * ?c + ?b * ?d) * (?a * ?c + ?b * ?d)"
      by (simp add: algebra_simps)
    also have "\<dots> = 1 - (?a * ?c + ?b * ?d)^2"
      by (simp add: power2_eq_square)
    finally show ?thesis using hdiff by linarith
  qed
  have hac_le1: "?a * ?c + ?b * ?d \<le> 1"
    using hprod by (simp add: zero_le_mult_iff, linarith)
  have hac_ge: "-1 \<le> ?a * ?c + ?b * ?d"
    using hprod by (simp add: zero_le_mult_iff, linarith)
  \<comment> \<open>Main estimate: decompose 1 - LHS into three nonneg terms.\<close>
  have hgoal: "((1-t) * ?a + t * ?c)^2 + ((1-t) * ?b + t * ?d)^2 \<le> 1"
  proof -
    have hexp: "((1-t) * ?a + t * ?c)^2 + ((1-t) * ?b + t * ?d)^2
      = (1-t)^2 * (?a^2 + ?b^2) + t^2 * (?c^2 + ?d^2)
        + 2 * t * (1-t) * (?a * ?c + ?b * ?d)"
      by (simp add: power2_eq_square algebra_simps)
    have ht1: "(1-t)^2 * (?a^2 + ?b^2) \<le> (1-t)^2"
      using hp2 by (simp add: power2_eq_square mult_left_le)
    have ht2: "t^2 * (?c^2 + ?d^2) \<le> t^2"
      using hq2 by (simp add: power2_eq_square mult_left_le)
    have ht3: "2 * t * (1-t) * (?a * ?c + ?b * ?d) \<le> 2 * t * (1-t)"
      using hac_le1 hs ht0 by (simp add: mult_left_le)
    have hsum: "(1-t)^2 + t^2 + 2 * t * (1-t) = 1"
      by (simp add: power2_eq_square algebra_simps)
    show ?thesis using hexp ht1 ht2 ht3 hsum by linarith
  qed
  show ?thesis unfolding top1_B2_def using hgoal by simp
qed

text \<open>Helper: extracting continuous\_on from top1\_continuous\_map\_on for B^2 paths.\<close>
lemma top1_B2_cont_fst:
  assumes hf: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
  shows "continuous_on I_set (fst \<circ> f)"
  unfolding continuous_on_open_invariant
proof (intro allI impI)
  fix B :: "real set" assume hBo: "open B"
  have hfB2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
    using hf unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>B \<times> UNIV is open in R^2, hence in product_topology_on.\<close>
  have hBxU_open: "open (B \<times> (UNIV::real set))" by (rule open_Times[OF hBo open_UNIV])
  have hBxU_prod: "B \<times> (UNIV::real set) \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "B \<times> (UNIV::real set) \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hBxU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  \<comment> \<open>Intersect with B^2 to get element of B^2\_topology.\<close>
  have hV: "top1_B2 \<inter> (B \<times> UNIV) \<in> top1_B2_topology"
    unfolding top1_B2_topology_def subspace_topology_def using hBxU_prod by blast
  \<comment> \<open>Preimage under f is in I\_top.\<close>
  have hpre: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} \<in> I_top"
    using hf hV unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>Simplify: f s \<in> B^2 \<inter> (B \<times> UNIV) iff fst(f s) \<in> B.\<close>
  have heq: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} = {s \<in> I_set. fst (f s) \<in> B}"
  proof (rule set_eqI)
    fix s show "s \<in> {s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} \<longleftrightarrow>
                s \<in> {s \<in> I_set. fst (f s) \<in> B}"
      using hfB2 by (auto simp: mem_Times_iff prod.collapse[symmetric])
  qed
  have hpre': "{s \<in> I_set. fst (f s) \<in> B} \<in> I_top" using hpre heq by simp
  \<comment> \<open>Extract open set from I\_top = subspace\_topology.\<close>
  obtain W where hW: "W \<in> top1_open_sets" and hWeq: "{s \<in> I_set. fst (f s) \<in> B} = I_set \<inter> W"
    using hpre' unfolding top1_unit_interval_topology_def subspace_topology_def by blast
  have "open W" using hW unfolding top1_open_sets_def by blast
  moreover have "W \<inter> I_set = (fst \<circ> f) -` B \<inter> I_set" using hWeq by (auto simp: comp_def)
  ultimately show "\<exists>A. open A \<and> A \<inter> I_set = (fst \<circ> f) -` B \<inter> I_set" by blast
qed

lemma top1_B2_cont_snd:
  assumes hf: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
  shows "continuous_on I_set (snd \<circ> f)"
  unfolding continuous_on_open_invariant
proof (intro allI impI)
  fix B :: "real set" assume hBo: "open B"
  have hfB2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
    using hf unfolding top1_continuous_map_on_def by blast
  have hUxB_open: "open ((UNIV::real set) \<times> B)" by (rule open_Times[OF open_UNIV hBo])
  have hUxB_prod: "(UNIV::real set) \<times> B \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "(UNIV::real set) \<times> B \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUxB_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have hV: "top1_B2 \<inter> (UNIV \<times> B) \<in> top1_B2_topology"
    unfolding top1_B2_topology_def subspace_topology_def using hUxB_prod by blast
  have hpre: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} \<in> I_top"
    using hf hV unfolding top1_continuous_map_on_def by blast
  have heq: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} = {s \<in> I_set. snd (f s) \<in> B}"
  proof (rule set_eqI)
    fix s show "s \<in> {s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} \<longleftrightarrow>
                s \<in> {s \<in> I_set. snd (f s) \<in> B}"
      using hfB2 by (auto simp: mem_Times_iff prod.collapse[symmetric])
  qed
  have hpre': "{s \<in> I_set. snd (f s) \<in> B} \<in> I_top" using hpre heq by simp
  obtain W where hW: "W \<in> top1_open_sets" and hWeq: "{s \<in> I_set. snd (f s) \<in> B} = I_set \<inter> W"
    using hpre' unfolding top1_unit_interval_topology_def subspace_topology_def by blast
  have "open W" using hW unfolding top1_open_sets_def by blast
  moreover have "W \<inter> I_set = (snd \<circ> f) -` B \<inter> I_set" using hWeq by (auto simp: comp_def)
  ultimately show "\<exists>A. open A \<and> A \<inter> I_set = (snd \<circ> f) -` B \<inter> I_set" by blast
qed

text \<open>Helper: B^2 is path-connected via straight-line paths.\<close>
lemma top1_B2_path_connected:
  "top1_path_connected_on top1_B2 top1_B2_topology"
proof -
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
              (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    thus ?thesis by simp
  qed
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    unfolding top1_B2_topology_def
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by rule
  have hUNIV_eq: "subspace_topology UNIV top1_open_sets (UNIV::real set) = top1_open_sets"
    by (rule subspace_topology_UNIV_self)
  have hpath: "\<forall>x\<in>top1_B2. \<forall>y\<in>top1_B2. \<exists>f. top1_is_path_on top1_B2 top1_B2_topology x y f"
  proof (intro ballI)
    fix x y :: "real \<times> real" assume hx: "x \<in> top1_B2" and hy: "y \<in> top1_B2"
    let ?f = "\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y)"
    \<comment> \<open>Each component is continuous\_on UNIV.\<close>
    have hc1: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst x + t * fst y)"
      by (intro continuous_intros)
    have hc2: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd x + t * snd y)"
      by (intro continuous_intros)
    \<comment> \<open>Each component: top1\_continuous\_map\_on I\_set I\_top UNIV top1\_open\_sets.\<close>
    have hcm1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * fst x + t * fst y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*fst x + t*fst y" UNIV, OF _ hc1]
      unfolding hI_eq hUNIV_eq by auto
    have hcm2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * snd x + t * snd y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*snd x + t*snd y" UNIV, OF _ hc2]
      unfolding hI_eq hUNIV_eq by auto
    \<comment> \<open>pi1 \<circ> ?f and pi2 \<circ> ?f.\<close>
    have hpi1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi1 \<circ> ?f)"
    proof -
      have "pi1 \<circ> ?f = (\<lambda>t. (1-t) * fst x + t * fst y)" unfolding pi1_def comp_def by auto
      thus ?thesis using hcm1 by simp
    qed
    have hpi2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi2 \<circ> ?f)"
    proof -
      have "pi2 \<circ> ?f = (\<lambda>t. (1-t) * snd x + t * snd y)" unfolding pi2_def comp_def by auto
      thus ?thesis using hcm2 by simp
    qed
    \<comment> \<open>Combine via Theorem 18.4.\<close>
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hf_cont_R2: "top1_continuous_map_on I_set I_top
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?f"
      using iffD2[OF Theorem_18_4[OF hTI hTR hTR, of ?f]]
      using hpi1 hpi2 unfolding hUU by blast
    \<comment> \<open>Image is in B^2.\<close>
    have hf_in_B2: "\<forall>t\<in>I_set. ?f t \<in> top1_B2"
    proof
      fix t assume ht: "t \<in> I_set"
      have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
      show "?f t \<in> top1_B2" by (rule top1_B2_convex[OF hx hy ht0 ht1])
    qed
    have hf_img: "?f ` I_set \<subseteq> top1_B2" using hf_in_B2 by blast
    \<comment> \<open>Restrict codomain to B^2.\<close>
    have hf_cont_B2: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology ?f"
      using top1_continuous_map_on_codomain_shrink[OF hf_cont_R2 hf_img]
      unfolding top1_B2_topology_def by simp
    \<comment> \<open>Endpoints.\<close>
    have hstart: "?f 0 = x" by simp
    have hend: "?f 1 = y" by simp
    show "\<exists>f. top1_is_path_on top1_B2 top1_B2_topology x y f"
      unfolding top1_is_path_on_def using hf_cont_B2 hstart hend by blast
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTB2 hpath by blast
qed

text \<open>Helper: B^2 is simply connected.\<close>
lemma top1_B2_simply_connected:
  "top1_simply_connected_on top1_B2 top1_B2_topology"
proof -
  have hpc: "top1_path_connected_on top1_B2 top1_B2_topology"
    by (rule top1_B2_path_connected)
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
  proof -
    have hTI: "is_topology_on I_set I_top"
      by (rule top1_unit_interval_topology_is_topology_on)
    show ?thesis
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  qed
  have hloops: "\<forall>x0\<in>top1_B2. \<forall>f. top1_is_loop_on top1_B2 top1_B2_topology x0 f \<longrightarrow>
      top1_path_homotopic_on top1_B2 top1_B2_topology x0 x0 f (top1_constant_path x0)"
  proof (intro ballI allI impI)
    fix x0 :: "real \<times> real" and f
    assume hx0: "x0 \<in> top1_B2" and hloop: "top1_is_loop_on top1_B2 top1_B2_topology x0 f"
    have hfcont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
    have hf_in_B2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
      using hfcont unfolding top1_continuous_map_on_def by blast
    \<comment> \<open>Build the straight-line homotopy using slh_ext for each component.\<close>
    let ?H1 = "top1_slh_ext (fst \<circ> f) (fst x0)"
    let ?H2 = "top1_slh_ext (snd \<circ> f) (snd x0)"
    let ?H = "\<lambda>p. (?H1 p, ?H2 p)"
    \<comment> \<open>Each component is continuous_on UNIV.\<close>
    have hfst_cont: "continuous_on I_set (fst \<circ> f)"
      by (rule top1_B2_cont_fst[OF hfcont])
    have hsnd_cont: "continuous_on I_set (snd \<circ> f)"
      by (rule top1_B2_cont_snd[OF hfcont])
    have hH1_cont_univ: "continuous_on UNIV ?H1"
      by (rule top1_slh_ext_continuous[OF hfst_cont])
    have hH2_cont_univ: "continuous_on UNIV ?H2"
      by (rule top1_slh_ext_continuous[OF hsnd_cont])
    \<comment> \<open>Each component is continuous II_topology \<rightarrow> top1_open_sets.\<close>
    have hH1_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H1"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH1_cont_univ])
    have hH2_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H2"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH2_cont_univ])
    \<comment> \<open>Combine via Theorem 18.4: pair is continuous to product topology.\<close>
    have hH_pi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi1 \<circ> ?H)"
    proof -
      have "pi1 \<circ> ?H = ?H1" unfolding pi1_def comp_def by auto
      thus ?thesis using hH1_cont by simp
    qed
    have hH_pi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi2 \<circ> ?H)"
    proof -
      have "pi2 \<circ> ?H = ?H2" unfolding pi2_def comp_def by auto
      thus ?thesis using hH2_cont by simp
    qed
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hH_cont_R2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?H"
      using iffD2[OF Theorem_18_4[OF hTII hTR hTR, of ?H]]
      using hH_pi1 hH_pi2 unfolding hUU by blast
    \<comment> \<open>Image of I\<times>I is in B^2 (by convexity).\<close>
    have hH_in_B2: "\<forall>p\<in>I_set \<times> I_set. ?H p \<in> top1_B2"
    proof (intro ballI)
      fix p assume hp: "p \<in> I_set \<times> I_set"
      have hs: "fst p \<in> I_set" and ht: "snd p \<in> I_set" using hp by auto
      have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
        using ht unfolding top1_unit_interval_def by auto
      have hfp: "f (fst p) \<in> top1_B2"
        using hf_in_B2 hs by blast
      have hagree1: "?H1 p = (1 - snd p) * (fst \<circ> f) (fst p) + snd p * fst x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have hagree2: "?H2 p = (1 - snd p) * (snd \<circ> f) (fst p) + snd p * snd x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have "?H p = ((1 - snd p) * fst (f (fst p)) + snd p * fst x0,
                     (1 - snd p) * snd (f (fst p)) + snd p * snd x0)"
        using hagree1 hagree2 by (simp add: comp_def)
      also have "\<dots> \<in> top1_B2"
        by (rule top1_B2_convex[OF hfp hx0 ht0 ht1])
      finally show "?H p \<in> top1_B2" .
    qed
    \<comment> \<open>Restrict codomain to B^2.\<close>
    have hB2_sub: "top1_B2 \<subseteq> (UNIV::(real\<times>real) set)" by simp
    have hH_img: "?H ` (I_set \<times> I_set) \<subseteq> top1_B2"
      using hH_in_B2 by blast
    have hH_cont_B2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        top1_B2 top1_B2_topology ?H"
      using top1_continuous_map_on_codomain_shrink[OF hH_cont_R2 hH_img hB2_sub]
      unfolding top1_B2_topology_def .
    \<comment> \<open>Boundary conditions.\<close>
    have hFs0: "\<forall>s\<in>I_set. ?H (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 0::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by auto
      have "?H1 (s, 0) = (1 - 0) * (fst \<circ> f) s + 0 * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (s, 0) = fst (f s)" by (simp add: comp_def)
      have "?H2 (s, 0) = (1 - 0) * (snd \<circ> f) s + 0 * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (s, 0) = snd (f s)" by (simp add: comp_def)
      show "?H (s, 0) = f s" using h1 h2 by simp
    qed
    have hFs1: "\<forall>s\<in>I_set. ?H (s, 1) = x0"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 1::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by auto
      have "?H1 (s, 1) = (1 - 1) * (fst \<circ> f) s + 1 * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (s, 1) = fst x0" by simp
      have "?H2 (s, 1) = (1 - 1) * (snd \<circ> f) s + 1 * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (s, 1) = snd x0" by simp
      show "?H (s, 1) = x0" using h1 h2 by simp
    qed
    have hF0t: "\<forall>t\<in>I_set. ?H (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(0::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by auto
      have "?H1 (0, t) = (1 - t) * (fst \<circ> f) 0 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (0, t) = fst x0"
        using hf0 by (simp add: comp_def algebra_simps)
      have "?H2 (0, t) = (1 - t) * (snd \<circ> f) 0 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (0, t) = snd x0"
        using hf0 by (simp add: comp_def algebra_simps)
      show "?H (0, t) = x0" using h1 h2 by simp
    qed
    have hF1t: "\<forall>t\<in>I_set. ?H (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(1::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by auto
      have "?H1 (1, t) = (1 - t) * (fst \<circ> f) 1 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (1, t) = fst x0"
        using hf1 by (simp add: comp_def algebra_simps)
      have "?H2 (1, t) = (1 - t) * (snd \<circ> f) 1 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (1, t) = snd x0"
        using hf1 by (simp add: comp_def algebra_simps)
      show "?H (1, t) = x0" using h1 h2 by simp
    qed
    \<comment> \<open>Assemble: f is a path, constant is a path.\<close>
    have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    proof -
      have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                    (product_topology_on top1_open_sets top1_open_sets)"
        by (rule product_topology_on_is_topology_on[OF hTR hTR])
      show ?thesis unfolding top1_B2_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2'[unfolded hUU]]) simp
    qed
    have hfpath: "top1_is_path_on top1_B2 top1_B2_topology x0 x0 f"
      using hloop unfolding top1_is_loop_on_def .
    have hcpath: "top1_is_path_on top1_B2 top1_B2_topology x0 x0 (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTB2 hx0])
    \<comment> \<open>Now the homotopy witnesses are H with II_topology.\<close>
    have hH_cont_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology top1_B2 top1_B2_topology ?H"
      by (rule hH_cont_B2)
    show "top1_path_homotopic_on top1_B2 top1_B2_topology x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def top1_constant_path_def
      using hfpath hcpath hH_cont_II hFs0 hFs1 hF0t hF1t
      unfolding top1_is_path_on_def top1_constant_path_def by blast
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc hloops by blast
qed

(** from \<S>55 Theorem 55.2: No-retraction theorem: no retraction B^2 \<rightarrow> S^1.
    Munkres' proof: if S^1 were a retract of B^2, then the inclusion-induced
    homomorphism would be injective (Lemma 55.1). But \<pi>_1(S^1) is nontrivial
    and \<pi>_1(B^2) is trivial — contradiction. **)
theorem Theorem_55_2_no_retraction:
  "\<not> top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
proof
  assume hret: "top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
  \<comment> \<open>By Lemma 55.1, inclusion S^1 \<rightarrow> B^2 induces injective hom on \<pi>_1.\<close>
  \<comment> \<open>But \<pi>_1(S^1) is nontrivial and \<pi>_1(B^2) is trivial — contradiction.\<close>
  obtain f g where hf: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
    and hg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
    and hne: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using top1_S1_fundamental_group_nontrivial by blast
  \<comment> \<open>Step 1: S^1 \<subseteq> B^2 and (1,0) is in S^1 = subspace\<close>
  have hSsub: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by auto
  have hx0: "(1::real, 0::real) \<in> top1_S1"
    unfolding top1_S1_def by simp
  \<comment> \<open>Step 2: f, g are also loops in B^2 (via inclusion).\<close>
  have hS1sub_UNIV: "top1_S1 \<subseteq> UNIV" by simp
  have hB2sub_UNIV: "top1_B2 \<subseteq> UNIV" by simp
  have hf_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hg_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology g"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hf_B2_cont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
    using top1_continuous_map_on_codomain_enlarge[OF hf_cont[unfolded top1_S1_topology_def] hSsub hB2sub_UNIV]
    unfolding top1_B2_topology_def .
  have hg_B2_cont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology g"
    using top1_continuous_map_on_codomain_enlarge[OF hg_cont[unfolded top1_S1_topology_def] hSsub hB2sub_UNIV]
    unfolding top1_B2_topology_def .
  have hf_0: "f 0 = (1, 0)" "f 1 = (1, 0)"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hg_0: "g 0 = (1, 0)" "g 1 = (1, 0)"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hf_B2: "top1_is_loop_on top1_B2 top1_B2_topology (1, 0) f"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hf_B2_cont hf_0 by blast
  have hg_B2: "top1_is_loop_on top1_B2 top1_B2_topology (1, 0) g"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hg_B2_cont hg_0 by blast
  \<comment> \<open>Step 3: Since B^2 is simply connected, f and g are path-homotopic in B^2.\<close>
  have hf_path_B2: "top1_is_path_on top1_B2 top1_B2_topology (1, 0) (1, 0) f"
    using hf_B2 unfolding top1_is_loop_on_def .
  have hg_path_B2: "top1_is_path_on top1_B2 top1_B2_topology (1, 0) (1, 0) g"
    using hg_B2 unfolding top1_is_loop_on_def .
  have hx0_B2: "(1::real, 0::real) \<in> top1_B2"
    unfolding top1_B2_def by simp
  have hf_const_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                             f (top1_constant_path (1, 0))"
    using top1_B2_simply_connected hf_B2 hx0_B2
    unfolding top1_simply_connected_on_def by blast
  have hg_const_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                             g (top1_constant_path (1, 0))"
    using top1_B2_simply_connected hg_B2 hx0_B2
    unfolding top1_simply_connected_on_def by blast
  have hg_const_sym: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                              (top1_constant_path (1, 0)) g"
    by (rule Lemma_51_1_path_homotopic_sym[OF hg_const_B2])
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using hTR2' unfolding hUU .
    show ?thesis unfolding top1_B2_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2], simp)
  qed
  have hfg_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0) f g"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTB2 hf_const_B2 hg_const_sym])
  \<comment> \<open>Step 4: Apply Lemma 55.1 to transfer path-homotopy back to S^1.\<close>
  \<comment> \<open>Identify subspace_topology top1_B2 top1_B2_topology top1_S1 with top1_S1_topology.\<close>
  have htop_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
    unfolding top1_B2_topology_def top1_S1_topology_def
    by (rule subspace_topology_trans[OF hSsub])
  have hf_sub: "top1_is_loop_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) f"
    using hf unfolding htop_eq .
  have hg_sub: "top1_is_loop_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) g"
    using hg unfolding htop_eq .
  have hfg_sub: "top1_path_homotopic_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) (1,0) f g"
    using Lemma_55_1_retract_injective[OF hret hx0 hf_sub hg_sub hfg_B2] .
  have hfg_S1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using hfg_sub unfolding htop_eq .
  show False using hne hfg_S1 by blast
qed

text \<open>Helper for Brouwer: v = f - id is continuous B^2 \<rightarrow> R^2.\<close>
lemma top1_B2_diff_continuous:
  assumes hf: "top1_continuous_map_on top1_B2 top1_B2_topology top1_B2 top1_B2_topology f"
  shows "top1_continuous_map_on top1_B2 top1_B2_topology
    (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)
    (\<lambda>x. (fst (f x) - fst x, snd (f x) - snd x))"
proof -
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    unfolding top1_B2_topology_def
    by (rule subspace_topology_is_topology_on) (use product_topology_on_is_topology_on[OF hTR hTR] in simp_all)
  have hfst: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets fst"
    using top1_fst_continuous_R2_subspace[of top1_B2] unfolding top1_B2_topology_def .
  have hsnd: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets snd"
    using top1_snd_continuous_R2_subspace[of top1_B2] unfolding top1_B2_topology_def .
  have hfstf: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (fst \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hf hfst])
  have hsndf: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (snd \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hf hsnd])
  let ?v = "\<lambda>x::real\<times>real. (fst (f x) - fst x, snd (f x) - snd x)"
  \<comment> \<open>Each component via composition with pairing + subtraction.\<close>
  have hcomp_cont: "\<And>g h. \<lbrakk>top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets g;
      top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets h\<rbrakk> \<Longrightarrow>
    top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (\<lambda>x. g x - h x)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix g h :: "real \<times> real \<Rightarrow> real" and x V
    assume hg: "(\<forall>x\<in>top1_B2. g x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. g x \<in> V} \<in> top1_B2_topology)"
    and hh: "(\<forall>x\<in>top1_B2. h x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. h x \<in> V} \<in> top1_B2_topology)"
    show "g x - h x \<in> UNIV" by simp
  next
    fix g h :: "real \<times> real \<Rightarrow> real" and V :: "real set"
    assume hg: "(\<forall>x\<in>top1_B2. g x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. g x \<in> V} \<in> top1_B2_topology)"
    and hh: "(\<forall>x\<in>top1_B2. h x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. h x \<in> V} \<in> top1_B2_topology)"
    and hV: "V \<in> top1_open_sets"
    \<comment> \<open>Preimage via (g, h) and subtraction.\<close>
    have hVo: "open V" using hV unfolding top1_open_sets_def by blast
    have "open ((\<lambda>p::real\<times>real. fst p - snd p) -` V)"
    proof (rule open_vimage[OF hVo])
      show "continuous_on UNIV (\<lambda>p::real\<times>real. fst p - snd p)" by (intro continuous_intros)
    qed
    hence hW: "(\<lambda>p::real\<times>real. fst p - snd p) -` V \<in> product_topology_on top1_open_sets top1_open_sets"
    proof -
      assume "open ((\<lambda>p::real\<times>real. fst p - snd p) -` V)"
      hence "(\<lambda>p::real\<times>real. fst p - snd p) -` V \<in> (top1_open_sets :: (real\<times>real) set set)"
        unfolding top1_open_sets_def by blast
      thus ?thesis using product_topology_on_open_sets_real2 by metis
    qed
    have hpair: "top1_continuous_map_on top1_B2 top1_B2_topology
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)
        (\<lambda>x. (g x, h x))"
    proof -
      have hp1: "pi1 \<circ> (\<lambda>x. (g x, h x)) = g" unfolding pi1_def by (rule ext) simp
      have hp2: "pi2 \<circ> (\<lambda>x. (g x, h x)) = h" unfolding pi2_def by (rule ext) simp
      have hg_cont: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi1 \<circ> (\<lambda>x. (g x, h x)))"
        using hg unfolding hp1 top1_continuous_map_on_def by blast
      have hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi2 \<circ> (\<lambda>x. (g x, h x)))"
        using hh unfolding hp2 top1_continuous_map_on_def by blast
      have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
      show ?thesis using iffD2[OF Theorem_18_4[OF hTB2 hTR hTR, of "\<lambda>x. (g x, h x)"]]
        hg_cont hh_cont unfolding hUU by blast
    qed
    have heq: "{x \<in> top1_B2. g x - h x \<in> V}
        = {x \<in> top1_B2. (\<lambda>x. (g x, h x)) x \<in> (\<lambda>p. fst p - snd p) -` V}"
      by auto
    show "{x \<in> top1_B2. g x - h x \<in> V} \<in> top1_B2_topology"
      unfolding heq using hpair hW unfolding top1_continuous_map_on_def by blast
  qed
  have hv1: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets
      (\<lambda>x. fst (f x) - fst x)"
    using hcomp_cont[OF hfstf hfst] by (simp add: comp_def)
  have hv2: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets
      (\<lambda>x. snd (f x) - snd x)"
    using hcomp_cont[OF hsndf hsnd] by (simp add: comp_def)
  have hpi1_v: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi1 \<circ> ?v)"
  proof -
    have "pi1 \<circ> ?v = (\<lambda>x. fst (f x) - fst x)" unfolding pi1_def comp_def by auto
    thus ?thesis using hv1 by simp
  qed
  have hpi2_v: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi2 \<circ> ?v)"
  proof -
    have "pi2 \<circ> ?v = (\<lambda>x. snd (f x) - snd x)" unfolding pi2_def comp_def by auto
    thus ?thesis using hv2 by simp
  qed
  have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
  show ?thesis using iffD2[OF Theorem_18_4[OF hTB2 hTR hTR, of ?v]]
    hpi1_v hpi2_v unfolding hUU by blast
qed

text \<open>Backward direction of Lemma 55.3: extension to B^2 implies nulhomotopic.\<close>
lemma Lemma_55_3_backward:
  fixes h :: "real \<times> real \<Rightarrow> 'a"
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and hTX: "is_topology_on X TX"
      and hk: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
      and hext: "\<forall>x\<in>top1_S1. k x = h x"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
proof -
  let ?c = "k (1::real, 0::real)"
  have hc_X: "?c \<in> X"
  proof -
    have "(1::real, 0::real) \<in> top1_B2" unfolding top1_B2_def by simp
    thus ?thesis using hk unfolding top1_continuous_map_on_def by blast
  qed
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  qed
  have hconst: "top1_continuous_map_on top1_S1 top1_S1_topology X TX (\<lambda>_. ?c)"
    by (rule top1_continuous_map_on_const[OF hTS1 hTX hc_X])
  \<comment> \<open>The homotopy F(x,t) = k((1-t)*fst x + t, (1-t)*snd x) shrinks S^1 to (1,0).\<close>
  let ?F = "\<lambda>(x::real\<times>real, t::real). k ((1-t) * fst x + t, (1-t) * snd x)"
  have hS1_in_B2: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by auto
  have h10_B2: "(1::real, 0::real) \<in> top1_B2" unfolding top1_B2_def by simp
  have hF_in_B2: "\<And>x t. x \<in> top1_S1 \<Longrightarrow> t \<in> I_set \<Longrightarrow>
    ((1-t) * fst x + t, (1-t) * snd x) \<in> top1_B2"
  proof -
    fix x :: "real \<times> real" and t :: real
    assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
    have hxB2: "x \<in> top1_B2" using hx hS1_in_B2 by blast
    have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
    show "((1-t) * fst x + t, (1-t) * snd x) \<in> top1_B2"
    proof -
      have "((1-t) * fst x + t * fst (1::real, 0::real),
             (1-t) * snd x + t * snd (1::real, 0::real)) \<in> top1_B2"
        by (rule top1_B2_convex[OF hxB2 h10_B2 ht0 ht1])
      thus ?thesis by simp
    qed
  qed
  \<comment> \<open>Continuity of F: composition of polynomial \<phi> and k.\<close>
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
      (product_topology_on top1_S1_topology I_top) X TX ?F"
  proof -
    let ?\<phi> = "\<lambda>(x::real\<times>real, t::real). ((1-t) * fst x + t, (1-t) * snd x)"
    \<comment> \<open>\<phi> is continuous S^1\<times>I \<rightarrow> B^2 (polynomial in components).\<close>
    have h\<phi>_cont_on: "continuous_on UNIV (\<lambda>p::((real\<times>real)\<times>real). ((1 - snd p) * fst (fst p) + snd p,
                                                                    (1 - snd p) * snd (fst p)))"
      by (intro continuous_intros)
    \<comment> \<open>Transfer to custom topology via the bridge lemmas.\<close>
    have hTP: "is_topology_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)"
      by (rule product_topology_on_is_topology_on[OF hTS1 hTI])
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    have hTB2: "is_topology_on top1_B2 top1_B2_topology"
      unfolding top1_B2_topology_def
      by (rule subspace_topology_is_topology_on)
         (use product_topology_on_is_topology_on[OF hTR hTR] in simp_all)
    \<comment> \<open>\<phi> maps S^1\<times>I into B^2.\<close>
    have h\<phi>_range: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?\<phi> p \<in> top1_B2"
      using hF_in_B2 by auto
    \<comment> \<open>\<phi> continuous via Theorem 18.4 + fst/snd projections.\<close>
    \<comment> \<open>Each component of \<phi> is continuous to R (polynomial in coordinates).\<close>
    \<comment> \<open>General helper: if f: R^3 \<rightarrow> R is continuous_on UNIV and maps S1\<times>I to R,
       then f is continuous from product_topology to top1_open_sets.\<close>
    have poly_cont: "\<And>f. continuous_on UNIV (f :: (real\<times>real)\<times>real \<Rightarrow> real) \<Longrightarrow>
        top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI allI impI)
      fix f :: "(real\<times>real)\<times>real \<Rightarrow> real" and p V
      assume hcont: "continuous_on UNIV f"
      show "f p \<in> (UNIV::real set)" by simp
    next
      fix f :: "(real\<times>real)\<times>real \<Rightarrow> real" and V :: "real set"
      assume hcont: "continuous_on UNIV f" and hV: "V \<in> top1_open_sets"
      have hVo: "open V" using hV unfolding top1_open_sets_def by blast
      have "open (f -` V)" by (rule open_vimage[OF hVo hcont])
      hence hfV: "f -` V \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        unfolding top1_open_sets_def by blast
      \<comment> \<open>f\<inverse>(V) is open in R^3. Its intersection with S1\<times>I is open in S1\<times>I.\<close>
      have hfV_prod: "f -` V \<in> product_topology_on
          (product_topology_on top1_open_sets top1_open_sets) top1_open_sets"
      proof -
        have heq: "product_topology_on (product_topology_on (top1_open_sets::real set set)
            (top1_open_sets::real set set)) (top1_open_sets::real set set)
          = (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
          using product_topology_on_open_sets_real2
                product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
          by metis
        show ?thesis unfolding heq by (rule hfV)
      qed
      have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> (f -` V)" by auto
      also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
      proof -
        have "product_topology_on top1_S1_topology I_top =
              subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::real set))
                (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                (top1_S1 \<times> I_set)"
        proof -
          have "product_topology_on top1_S1_topology I_top =
                product_topology_on
                  (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1)
                  (subspace_topology UNIV top1_open_sets I_set)"
            unfolding top1_S1_topology_def top1_unit_interval_topology_def by simp
          also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
                (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                (top1_S1 \<times> I_set)"
          proof -
            have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
              using product_topology_on_is_topology_on[OF hTR hTR] by simp
            show ?thesis by (rule Theorem_16_3[OF hTR2 hTR])
          qed
          finally show ?thesis by simp
        qed
        thus ?thesis using hfV_prod unfolding subspace_topology_def by blast
      qed
      finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in>
          product_topology_on top1_S1_topology I_top" .
    qed
    have hfst_\<phi>: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets
        (\<lambda>p. (1 - snd p) * fst (fst p) + snd p)"
      by (rule poly_cont) (intro continuous_intros)
    have hsnd_\<phi>: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets
        (\<lambda>p. (1 - snd p) * snd (fst p))"
      by (rule poly_cont) (intro continuous_intros)
    \<comment> \<open>Combine into pair by Theorem 18.4.\<close>
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    have hpi1_eq: "pi1 \<circ> ?\<phi> = (\<lambda>p. (1 - snd p) * fst (fst p) + snd p)"
      unfolding pi1_def comp_def by (rule ext) auto
    have hpi2_eq: "pi2 \<circ> ?\<phi> = (\<lambda>p. (1 - snd p) * snd (fst p))"
      unfolding pi2_def comp_def by (rule ext) auto
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have h\<phi>_R2: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets) ?\<phi>"
      using iffD2[OF Theorem_18_4[OF hTP hTR hTR, of ?\<phi>]]
            hfst_\<phi>[folded hpi1_eq] hsnd_\<phi>[folded hpi2_eq] unfolding hUU by blast
    have h\<phi>_img: "?\<phi> ` (top1_S1 \<times> I_set) \<subseteq> top1_B2"
      using h\<phi>_range by auto
    have h\<phi>_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) top1_B2 top1_B2_topology ?\<phi>"
      using top1_continuous_map_on_codomain_shrink[OF h\<phi>_R2 h\<phi>_img]
      unfolding top1_B2_topology_def by simp
    \<comment> \<open>F = k \<circ> \<phi>.\<close>
    have hF_eq: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?F p = (k \<circ> ?\<phi>) p"
      by (auto simp: comp_def case_prod_beta)
    have "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) X TX (k \<circ> ?\<phi>)"
      by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hk])
    thus ?thesis
      using hF_eq unfolding top1_continuous_map_on_def comp_def
      by (auto simp: case_prod_beta)
  qed
  have hF0: "\<forall>x\<in>top1_S1. ?F (x, 0) = h x"
  proof
    fix x assume hx: "x \<in> top1_S1"
    have "?F (x, 0) = k (fst x, snd x)" by simp
    also have "\<dots> = k x" by simp
    also have "\<dots> = h x" using hext hx by blast
    finally show "?F (x, 0) = h x" .
  qed
  have hF1: "\<forall>x\<in>top1_S1. ?F (x, 1) = ?c" by simp
  show ?thesis
    unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hc_X hh hconst hF_cont hF0 hF1 by blast
qed

(** from \<S>55 Lemma 55.3: nulhomotopic characterization **)
lemma Lemma_55_3_nulhomotopic_characterization:
  fixes h :: "real \<times> real \<Rightarrow> 'a"
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and hTX: "is_topology_on X TX"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h
      \<longleftrightarrow> (\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k
               \<and> (\<forall>x\<in>top1_S1. k x = h x))"
proof (intro iffI)
  \<comment> \<open>Forward (1)\<Rightarrow>(2): nulhomotopic \<Rightarrow> extension to B^2.
     Munkres: Let H: S^1\<times>I \<rightarrow> X be homotopy from h to const. The quotient map
     \<pi>(x,t) = (1-t)x collapses S^1\<times>{1} to 0 and is otherwise injective.
     Since H is constant on S^1\<times>{1}, it factors through \<pi>, giving k: B^2 \<rightarrow> X.\<close>
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
  \<comment> \<open>Munkres' proof: H: S^1 \<times> I \<rightarrow> X is homotopy from h to const c.
     Define \<pi>: S^1 \<times> I \<rightarrow> B^2 by \<pi>(x,t) = (1-t)x. This maps S^1 \<times> {0} to S^1 (homeomorphically)
     and collapses S^1 \<times> {1} to {0}. Since H is constant on S^1 \<times> {1},
     H factors through \<pi>: k(\<pi>(x,t)) = H(x,t), i.e., k((1-t)x) = H(x,t).\<close>
  obtain c where hc: "c \<in> X"
      and hhom: "top1_homotopic_on top1_S1 top1_S1_topology X TX h (\<lambda>_. c)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain H where hH_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) X TX H"
      and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
      and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  \<comment> \<open>Define k: B^2 \<rightarrow> X. For y \<in> B^2, write y = (1-t) \<cdot> (y/|y|) for t = 1-|y|,
     so k(y) = H(y/|y|, 1-|y|) for y \<ne> 0, and k(0) = c.\<close>
  define k where "k = (\<lambda>y. if y = (0::real, 0::real) then c
      else H ((fst y / sqrt (fst y ^ 2 + snd y ^ 2),
               snd y / sqrt (fst y ^ 2 + snd y ^ 2)),
              1 - sqrt (fst y ^ 2 + snd y ^ 2)))"
  \<comment> \<open>k extends h: for x \<in> S^1, |x| = 1, so k(x) = H(x, 0) = h(x).\<close>
  have hext: "\<forall>x\<in>top1_S1. k x = h x"
  proof
    fix x assume hx: "x \<in> top1_S1"
    have hx_eq: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 auto)
    have hx_ne: "x \<noteq> (0, 0)"
    proof
      assume "x = (0, 0)"
      hence "fst x ^ 2 + snd x ^ 2 = 0" by simp
      thus False using hx_eq by simp
    qed
    have hsqrt: "sqrt (fst x ^ 2 + snd x ^ 2) = 1"
      using hx_eq by simp
    have "k x = H ((fst x / 1, snd x / 1), 1 - 1)"
      unfolding k_def using hx_ne hsqrt by simp
    also have "\<dots> = H (x, 0)" by simp
    also have "\<dots> = h x" using hH0 hx by (by100 blast)
    finally show "k x = h x" .
  qed
  \<comment> \<open>k is continuous: on B^2 - {0}, continuous by composition; at 0, use H(x,1) = c.\<close>
  have hk_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k" sorry
  show "\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k \<and> (\<forall>x\<in>top1_S1. k x = h x)"
    using hk_cont hext by (by100 blast)
next
  \<comment> \<open>Backward: extension to B^2 \<Rightarrow> nulhomotopic (Lemma_55_3_backward).\<close>
  assume "\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k \<and> (\<forall>x\<in>top1_S1. k x = h x)"
  then obtain k where hk: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
      and hext: "\<forall>x\<in>top1_S1. k x = h x" by blast
  show "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
    by (rule Lemma_55_3_backward[OF hh hTX hk hext])
qed

(** from \<S>55 Corollary 55.4: inclusion S^1 \<rightarrow> R^2 - {0} is not nulhomotopic.
    Follows from Theorem 55.2 via retraction R^2 - {0} \<rightarrow> S^1 by x/|x|. **)
corollary Corollary_55_4_inclusion_not_nulhomotopic:
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology
           (UNIV - {(0, 0)})
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
           (\<lambda>x. x)"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
      (\<lambda>x. x)"
  \<comment> \<open>Munkres 55.4: The retraction r(x) = x/|x| makes j_* injective (Lemma 55.1).
     Since \<pi>_1(S^1) is nontrivial, j_* is nontrivial, so j is not nulhomotopic.\<close>
  \<comment> \<open>Step 1: r(x) = x/|x| is a retraction R^2-0 \<rightarrow> S^1.\<close>
  have hret: "top1_retract_of_on (UNIV - {(0::real, 0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
      top1_S1"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?r = "\<lambda>x::real\<times>real. (fst x / ?norm x, snd x / ?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by (by100 auto)
    have hr_map: "\<forall>x\<in>?R2_0. ?r x \<in> top1_S1"
    proof (intro ballI)
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0"
      hence hne: "x \<noteq> (0, 0)" by (by100 blast)
      hence hpos: "fst x ^ 2 + snd x ^ 2 > 0"
        by (cases x) (auto simp: sum_power2_gt_zero_iff)
      hence hnorm_pos: "?norm x > 0" by (simp add: real_sqrt_gt_zero)
      have "fst (?r x) ^ 2 + snd (?r x) ^ 2 = 1"
      proof -
        let ?d = "fst x ^ 2 + snd x ^ 2"
        have "fst x ^ 2 / ?d + snd x ^ 2 / ?d = ?d / ?d"
          by (metis add_divide_distrib)
        also have "?d / ?d = 1" using hpos by auto
        finally have hadd: "fst x ^ 2 / ?d + snd x ^ 2 / ?d = 1" .
        have h1: "fst (?r x) = fst x / ?norm x" by simp
        have h2: "snd (?r x) = snd x / ?norm x" by simp
        have hnorm_sq: "(?norm x) ^ 2 = ?d"
          using hpos by (simp add: real_sqrt_pow2)
        show ?thesis unfolding h1 h2 power_divide hnorm_sq using hadd by simp
      qed
      thus "?r x \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    qed
    have hr_fix: "\<forall>x\<in>top1_S1. ?r x = x"
    proof (intro ballI)
      fix x :: "real \<times> real" assume hx: "x \<in> top1_S1"
      have heq: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
      hence hnorm: "?norm x = 1" by (simp add: real_sqrt_eq_1_iff)
      show "?r x = x" using hnorm by (simp add: prod_eq_iff)
    qed
    have hr_cont: "top1_continuous_map_on ?R2_0 ?TR top1_S1
        (subspace_topology ?R2_0 ?TR top1_S1) ?r"
    proof -
      \<comment> \<open>Step 1: r is continuous_on R²-{0} using standard library.\<close>
      have hr_std: "continuous_on ?R2_0 ?r"
      proof (rule continuous_on_Pair)
        have hnorm_cont: "continuous_on ?R2_0 ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power
              continuous_on_fst continuous_on_snd) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0"
          hence "x \<noteq> (0, 0)" by (by100 blast)
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          hence "?norm x > 0" by (rule real_sqrt_gt_zero)
          thus "?norm x \<noteq> 0" by (by100 linarith)
        qed
        have hfst_cont: "continuous_on ?R2_0 fst"
          by (intro continuous_intros)
        have hsnd_cont: "continuous_on ?R2_0 snd"
          by (intro continuous_intros)
        show "continuous_on ?R2_0 (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide[OF hfst_cont hnorm_cont hnorm_nz])
        show "continuous_on ?R2_0 (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide[OF hsnd_cont hnorm_cont hnorm_nz])
      qed
      \<comment> \<open>Step 2: Transfer to top1_continuous_map_on via general subspace lemma.\<close>
      have hr_R2: "top1_continuous_map_on ?R2_0
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0)
          top1_S1
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1) ?r"
        by (rule top1_continuous_map_on_real2_subspace_general[OF _ hr_std])
           (use hr_map in blast)
      \<comment> \<open>Step 3: Codomain topology: subspace of R²-{0} restricted to S¹ = subspace of R² restricted to S¹.\<close>
      have hTR_eq: "subspace_topology ?R2_0 ?TR top1_S1 =
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1"
        using subspace_topology_trans[OF hS1sub] by simp
      show ?thesis using hr_R2 unfolding hTR_eq[symmetric] .
    qed
    show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
      using hS1sub hr_cont hr_fix by (by100 blast)
  qed
  \<comment> \<open>Step 2: j_* is injective (Lemma 55.1) hence nontrivial.\<close>
  \<comment> \<open>Step 3: nulhomotopic \<Rightarrow> j_* trivial (Lemma 55.3 (3)\<Rightarrow>(1)), contradicting nontrivial.\<close>
  \<comment> \<open>By retraction + Theorem 55.2 (no retract of B² to S¹) argument:
     j nulhomotopic ⟹ j extends to k: B² → R²-{0} with k|S¹ = j.
     Composing r∘k: B² → S¹ gives a retraction, contradicting Theorem 55.2.\<close>
  show False
  proof -
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})"
    have hTR2_full: "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by simp
    have hTR: "is_topology_on (UNIV - {(0::real, 0)}) ?TR"
      by (simp add: product_topology_on_open_sets
        subspace_topology_is_topology_on top1_open_sets_is_topology_on_UNIV)
    have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology (UNIV - {(0, 0)}) ?TR (\<lambda>x. x)"
    proof -
      have hS1_sub: "top1_S1 \<subseteq> UNIV - {(0::real, 0)}" unfolding top1_S1_def by (by100 auto)
      have hid_full: "top1_continuous_map_on (UNIV - {(0::real, 0)}) ?TR (UNIV - {(0, 0)}) ?TR id"
        by (rule top1_continuous_map_on_id[OF hTR])
      have hid_restr: "top1_continuous_map_on top1_S1
          (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) (UNIV - {(0, 0)}) ?TR id"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_full hS1_sub])
      have hS1_eq: "subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1 = top1_S1_topology"
        unfolding top1_S1_topology_def
        using subspace_topology_trans[OF hS1_sub] by simp
      have hid_eq: "(\<lambda>x::real\<times>real. x) = id" by (rule ext) simp
      show ?thesis using hid_restr unfolding hS1_eq hid_eq[symmetric] by simp
    qed
    \<comment> \<open>nulhomotopic ⟹ extends to B².\<close>
    obtain k where hk: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV - {(0, 0)}) ?TR k"
        and hkS1: "\<forall>x\<in>top1_S1. k x = x"
      using iffD1[OF Lemma_55_3_nulhomotopic_characterization[OF hid_cont hTR] hnul] by (by100 blast)
    \<comment> \<open>r∘k: B² → S¹ is a retraction (r∘k|S¹ = r|S¹ = id), contradicting no-retraction.\<close>
    have "top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
    proof -
      \<comment> \<open>From hret, get retraction r': R²-{0} → S¹.\<close>
      obtain r' where hr'_sub: "top1_S1 \<subseteq> UNIV - {(0::real, 0)}"
          and hr'_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?TR top1_S1
              (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) r'"
          and hr'_fix: "\<forall>a\<in>top1_S1. r' a = a"
        using hret unfolding top1_retract_of_on_def top1_is_retraction_on_def by (by100 blast)
      \<comment> \<open>r'∘k: B² → S¹ continuous (composition).\<close>
      have hrk_comp: "top1_continuous_map_on top1_B2 top1_B2_topology top1_S1
          (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) (r' \<circ> k)"
        by (rule top1_continuous_map_on_comp[OF hk hr'_cont])
      \<comment> \<open>Subspace topology equalities.\<close>
      have hTS1_eq: "subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1 = top1_S1_topology"
        unfolding top1_S1_topology_def using subspace_topology_trans[OF hr'_sub] by simp
      have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hTS1_B2: "top1_S1_topology = subspace_topology top1_B2 top1_B2_topology top1_S1"
        unfolding top1_S1_topology_def top1_B2_topology_def
        using subspace_topology_trans[OF hS1_B2] by simp
      have hrk_cont: "top1_continuous_map_on top1_B2 top1_B2_topology top1_S1
          (subspace_topology top1_B2 top1_B2_topology top1_S1) (r' \<circ> k)"
        using hrk_comp unfolding hTS1_eq hTS1_B2 .
      \<comment> \<open>r'∘k fixes S¹: k(x) = x and r'(x) = x for x \<in> S¹.\<close>
      have hrk_fix: "\<forall>a\<in>top1_S1. (r' \<circ> k) a = a"
      proof (intro ballI)
        fix a assume ha: "a \<in> top1_S1"
        show "(r' \<circ> k) a = a" using hkS1 hr'_fix ha by (simp add: comp_def)
      qed
      show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
        using hS1_B2 hrk_cont hrk_fix by (by100 blast)
    qed
    thus False using Theorem_55_2_no_retraction by (by100 metis)
  qed
qed

text \<open>Helper: if f is nulhomotopic and f \<simeq> g, then g is nulhomotopic.
  Proof: f \<simeq> const and g \<simeq> f (symmetry), compose homotopies (concatenation).\<close>
lemma nulhomotopic_homotopic_trans:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hnul: "top1_nulhomotopic_on X TX Y TY f"
      and hhom: "top1_homotopic_on X TX Y TY f g"
  shows "top1_nulhomotopic_on X TX Y TY g"
proof -
  obtain c where hcY: "c \<in> Y" and hfc: "top1_homotopic_on X TX Y TY f (\<lambda>_. c)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain F1 where hF1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F1"
      and hF1_0: "\<forall>x\<in>X. F1 (x, 0) = f x" and hF1_1: "\<forall>x\<in>X. F1 (x, 1) = c"
    using hfc unfolding top1_homotopic_on_def by (by100 blast)
  \<comment> \<open>Symmetry: from f \<simeq> g, get homotopy G(x,t) = F(x,1-t) from g to f.\<close>
  obtain F2 where hF2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F2"
      and hF2_0: "\<forall>x\<in>X. F2 (x, 0) = g x" and hF2_1: "\<forall>x\<in>X. F2 (x, 1) = f x"
  proof -
    obtain F0 where hF0: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F0"
        and hF0_0: "\<forall>x\<in>X. F0 (x, 0) = f x" and hF0_1: "\<forall>x\<in>X. F0 (x, 1) = g x"
      using hhom unfolding top1_homotopic_on_def by (by100 blast)
    let ?F2 = "\<lambda>(x, t). F0 (x, 1 - t)"
    have hF2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?F2"
    proof -
      have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
        (\<lambda>p. F0 (fst p, 1 - snd p))"
        by (rule homotopy_reverse_continuous[OF hF0 hTX])
      moreover have "(\<lambda>p. F0 (fst p, 1 - snd p)) = ?F2"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    have "\<forall>x\<in>X. ?F2 (x, 0) = g x" using hF0_1 by (by100 simp)
    moreover have "\<forall>x\<in>X. ?F2 (x, 1) = f x" using hF0_0 by (by100 simp)
    ultimately show ?thesis using hF2_cont that by (by100 blast)
  qed
  \<comment> \<open>Concatenate F2 and F1: G(x,t) = F2(x,2t) for t\<le>1/2, F1(x,2t-1) for t>1/2.\<close>
  have hmatch: "\<forall>x\<in>X. F2 (x, 1) = F1 (x, 0)"
    using hF2_1 hF1_0 by (by100 simp)
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F2 (fst p, 2 * snd p) else F1 (fst p, 2 * snd p - 1)"
  have hG_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_concat_continuous[OF hTX hTY hF2 hF1 hmatch])
  have hG_0: "\<forall>x\<in>X. ?G (x, 0) = g x"
    using hF2_0 by (by100 simp)
  have hG_1: "\<forall>x\<in>X. ?G (x, 1) = c"
    using hF1_1 by (by100 simp)
  have hg_cont: "top1_continuous_map_on X TX Y TY g"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  have hconst: "top1_continuous_map_on X TX Y TY (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTX hTY hcY])
  show ?thesis
    unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hcY hg_cont hconst hG_cont hG_0 hG_1 by (by100 blast)
qed

text \<open>Continuity transfer: continuous_on UNIV for R³ → R² gives
  top1_continuous_map_on on S¹×I → R²-{0} when the image avoids (0,0).\<close>
lemma S1_I_to_R2_minus_0_continuous:
  fixes f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on UNIV f"
      and hmap: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> f p \<in> UNIV - {(0::real, 0)}"
  shows "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>Step 1: f maps S¹×I into R² continuously (via product topology transfer).\<close>
  have hf_R2: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    \<comment> \<open>V is open in R².\<close>
    have hVo: "open V"
    proof -
      have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
        using hV product_topology_on_open_sets_real2 by metis
      thus ?thesis unfolding top1_open_sets_def by simp
    qed
    have hfV_open: "open (f -` V)" by (rule open_vimage[OF hVo hcont])
    \<comment> \<open>f⁻¹(V) is open in R³ = (R²)×R.\<close>
    have hfV_R3: "f -` V \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "f -` V \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hfV_open unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    \<comment> \<open>(S¹×I) ∩ f⁻¹(V) is open in the product subspace topology.\<close>
    have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> (f -` V)" by auto
    also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
    proof -
      have hTP_eq: "product_topology_on top1_S1_topology I_top =
          subspace_topology (UNIV \<times> UNIV)
            (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
              (top1_open_sets::real set set))
            (top1_S1 \<times> I_set)"
      proof -
        have "product_topology_on top1_S1_topology I_top =
              product_topology_on
                (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) top1_S1)
                (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
          unfolding top1_S1_topology_def top1_unit_interval_topology_def ..
        also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
            (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
              (top1_open_sets::real set set))
            (top1_S1 \<times> I_set)"
          by (rule Theorem_16_3[OF hTR2 hTR])
        finally show ?thesis .
      qed
      show ?thesis unfolding hTP_eq subspace_topology_def
        using hfV_R3 by (by100 blast)
    qed
    finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in> product_topology_on top1_S1_topology I_top" .
  qed
  \<comment> \<open>Step 2: Codomain shrink to R²-{0}.\<close>
  have himg: "f ` (top1_S1 \<times> I_set) \<subseteq> UNIV - {(0, 0)}"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (top1_S1 \<times> I_set)"
    then obtain p where hp: "p \<in> top1_S1 \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> UNIV - {(0, 0)}" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

text \<open>Reverse transfer: top1_continuous_map_on on R² subspaces implies continuous_on.\<close>
lemma top1_continuous_map_on_to_continuous_on_R2:
  fixes f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes hf: "top1_continuous_map_on S
      (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
      UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
  shows "continuous_on S f"
proof -
  {
    fix U :: "(real \<times> real) set"
    assume hUo: "open U"
    have hU_os: "U \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUo unfolding top1_open_sets_def by (by100 blast)
    have hU_prod: "U \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
      using hU_os product_topology_on_open_sets_real2 by (by100 metis)
    have hpre: "{x \<in> S. f x \<in> U} \<in> subspace_topology UNIV
        (product_topology_on (top1_open_sets::real set set) top1_open_sets) S"
      using hf hU_prod unfolding top1_continuous_map_on_def by (by100 blast)
    then obtain W where hW_prod: "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        and hpre_eq: "{x \<in> S. f x \<in> U} = S \<inter> W"
      unfolding subspace_topology_def by (by100 auto)
    have hW_os: "W \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hW_prod product_topology_on_open_sets_real2 by (by100 metis)
    have hWo: "open W" using hW_os unfolding top1_open_sets_def by (by100 simp)
    have "\<exists>A. open A \<and> A \<inter> S = f -` U \<inter> S"
    proof (intro exI[of _ W] conjI)
      show "open W" by (rule hWo)
      show "W \<inter> S = f -` U \<inter> S"
      proof (intro set_eqI iffI)
        fix x assume "x \<in> W \<inter> S"
        hence "x \<in> S \<inter> W" by (by100 blast)
        hence "x \<in> {x \<in> S. f x \<in> U}" using hpre_eq by (by100 simp)
        thus "x \<in> f -` U \<inter> S" by (by100 simp)
      next
        fix x assume "x \<in> f -` U \<inter> S"
        hence "x \<in> S" "f x \<in> U" by (by100 simp)+
        hence "x \<in> {x \<in> S. f x \<in> U}" by (by100 simp)
        thus "x \<in> W \<inter> S" using hpre_eq by (by100 simp)
      qed
    qed
  } note hstep = this
  show ?thesis unfolding continuous_on_open_invariant
  proof (intro allI impI)
    fix B :: "(real \<times> real) set" assume "open B"
    thus "\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S" by (rule hstep)
  qed
qed

text \<open>General variant: continuous_on (S×I) for any S ⊆ R².\<close>
lemma R2_subspace_I_continuous_on_transfer:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
    and f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on (S \<times> I_set) f"
      and hmap: "\<And>p. p \<in> S \<times> I_set \<Longrightarrow> f p \<in> T"
  shows "top1_continuous_map_on (S \<times> I_set)
      (product_topology_on
        (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
        I_top)
      T (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) T) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  let ?TS = "subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S"
  have hf_R2: "top1_continuous_map_on (S \<times> I_set) (product_topology_on ?TS I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    have hV': "V \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets" using hV .
    have hVo: "open V"
      using hV'[unfolded product_topology_on_open_sets_real2] unfolding top1_open_sets_def
      by (by100 simp)
    have hcont': "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> (S \<times> I_set) = f -` B \<inter> (S \<times> I_set))"
      using hcont unfolding continuous_on_open_invariant .
    obtain W where hWo: "open W" and hWeq: "W \<inter> (S \<times> I_set) = f -` V \<inter> (S \<times> I_set)"
      using hcont'[rule_format, OF hVo] by (by100 blast)
    have hW_R3: "W \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "W \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hWo unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    have hTP_eq: "product_topology_on ?TS I_top =
        subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (S \<times> I_set)"
    proof -
      have "product_topology_on ?TS I_top =
            product_topology_on
              (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_unit_interval_topology_def ..
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (S \<times> I_set)"
        by (rule Theorem_16_3[OF hTR2 hTR])
      finally show ?thesis .
    qed
    have "{p \<in> S \<times> I_set. f p \<in> V} = (S \<times> I_set) \<inter> W"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> {p \<in> S \<times> I_set. f p \<in> V}"
      hence "x \<in> S \<times> I_set" "f x \<in> V" by (by100 simp)+
      hence "x \<in> f -` V \<inter> (S \<times> I_set)" by (by100 simp)
      thus "x \<in> (S \<times> I_set) \<inter> W" using hWeq by (by100 blast)
    next
      fix x assume "x \<in> (S \<times> I_set) \<inter> W"
      hence "x \<in> W \<inter> (S \<times> I_set)" by (by100 blast)
      hence "x \<in> f -` V \<inter> (S \<times> I_set)" using hWeq by (by100 blast)
      thus "x \<in> {p \<in> S \<times> I_set. f p \<in> V}" by (by100 simp)
    qed
    also have "\<dots> \<in> product_topology_on ?TS I_top"
    proof -
      have "S \<times> I_set \<subseteq> (UNIV::(real\<times>real) set) \<times> (UNIV::real set)" by (by100 simp)
      hence hmem: "(S \<times> I_set) \<inter> W \<in> subspace_topology
          ((UNIV::(real\<times>real) set) \<times> (UNIV::real set))
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set)) (S \<times> I_set)"
        using hW_R3 unfolding subspace_topology_def by (by100 auto)
      show ?thesis using hmem unfolding hTP_eq by simp
    qed
    finally show "{p \<in> S \<times> I_set. f p \<in> V} \<in> product_topology_on ?TS I_top" .
  qed
  have himg: "f ` (S \<times> I_set) \<subseteq> T"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (S \<times> I_set)"
    then obtain p where hp: "p \<in> S \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> T" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

text \<open>Variant with continuous_on on the domain (for functions that are NOT continuous on UNIV).\<close>
lemma S1_I_to_R2_minus_0_continuous_on:
  fixes f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on (top1_S1 \<times> I_set) f"
      and hmap: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> f p \<in> UNIV - {(0::real, 0)}"
  shows "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  \<comment> \<open>Step 1: f maps S¹×I into R² continuously.\<close>
  have hf_R2: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    have hV': "V \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets" using hV .
    have hVo: "open V"
      using hV'[unfolded product_topology_on_open_sets_real2] unfolding top1_open_sets_def
      by (by100 simp)
    \<comment> \<open>continuous_on gives: \<exists>W open. W \<inter> (S¹×I) = f⁻¹(V) \<inter> (S¹×I).\<close>
    have hcont': "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> (top1_S1 \<times> I_set) = f -` B \<inter> (top1_S1 \<times> I_set))"
      using hcont unfolding continuous_on_open_invariant .
    obtain W where hWo: "open W" and hWeq: "W \<inter> (top1_S1 \<times> I_set) = f -` V \<inter> (top1_S1 \<times> I_set)"
      using hcont'[rule_format, OF hVo] by (by100 blast)
    \<comment> \<open>W open in R³.\<close>
    have hW_R3: "W \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "W \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hWo unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    \<comment> \<open>(S¹×I) ∩ W is open in product subspace topology.\<close>
    have hTP_eq: "product_topology_on top1_S1_topology I_top =
        subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (top1_S1 \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_topology I_top =
            product_topology_on
              (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) top1_S1)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_topology_def top1_unit_interval_topology_def ..
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (top1_S1 \<times> I_set)"
        by (rule Theorem_16_3[OF hTR2 hTR])
      finally show ?thesis .
    qed
    have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> W"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> {p \<in> top1_S1 \<times> I_set. f p \<in> V}"
      hence "x \<in> top1_S1 \<times> I_set" "f x \<in> V" by (by100 simp)+
      hence "x \<in> f -` V \<inter> (top1_S1 \<times> I_set)" by (by100 simp)
      thus "x \<in> (top1_S1 \<times> I_set) \<inter> W" using hWeq by (by100 blast)
    next
      fix x assume "x \<in> (top1_S1 \<times> I_set) \<inter> W"
      hence "x \<in> W \<inter> (top1_S1 \<times> I_set)" by (by100 blast)
      hence "x \<in> f -` V \<inter> (top1_S1 \<times> I_set)" using hWeq by (by100 blast)
      thus "x \<in> {p \<in> top1_S1 \<times> I_set. f p \<in> V}" by (by100 simp)
    qed
    also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
      unfolding hTP_eq subspace_topology_def using hW_R3 by (by100 blast)
    finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in> product_topology_on top1_S1_topology I_top" .
  qed
  \<comment> \<open>Step 2: Codomain shrink.\<close>
  have himg: "f ` (top1_S1 \<times> I_set) \<subseteq> UNIV - {(0, 0)}"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (top1_S1 \<times> I_set)"
    then obtain p where hp: "p \<in> top1_S1 \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> UNIV - {(0, 0)}" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

(** from \<S>55 Theorem 55.5: nonvanishing vector field on B^2 points outward at
    some point of S^1 (and inward at some point). **)
text \<open>Helper: a nonvanishing vector field on B² that doesn't point inward at any
  point of S¹ leads to a contradiction (because the inclusion S¹ → R²-{0} would be nulhomotopic).\<close>
lemma vector_field_must_point_inward:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) v"
      and "\<forall>x\<in>top1_B2. v x \<noteq> (0, 0)"
      and "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x))"
  shows False
proof -
  \<comment> \<open>w = v|S^1 extends to B^2 \<rightarrow> R^2-0 (via v itself), so w is nulhomotopic.\<close>
  have hw_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
         (UNIV - {(0, 0)}))
      (\<lambda>x. v x)"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR2_0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    have hv_S1: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
    proof -
      have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hv_B2_temp: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
      proof -
        have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0" using assms(2) by (by100 auto)
        show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg]) simp
      qed
      show ?thesis
      proof -
        have hrestr: "top1_continuous_map_on top1_S1
            (subspace_topology top1_B2 top1_B2_topology top1_S1) ?R2_0 ?TR2_0 (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hv_B2_temp hS1_B2])
        have hS1_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
          unfolding top1_B2_topology_def top1_S1_topology_def
          using subspace_topology_trans[OF hS1_B2, of UNIV "product_topology_on top1_open_sets top1_open_sets"]
          by simp
        show ?thesis using hrestr unfolding hS1_eq .
      qed
    qed
    have hv_B2: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
    proof -
      have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0"
        using assms(2) by (by100 auto)
      have hR2_sub: "?R2_0 \<subseteq> (UNIV :: (real\<times>real) set)" by simp
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg hR2_sub])
    qed
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hTR2': "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using hTR2 by simp
    have hTR2_0: "is_topology_on ?R2_0 ?TR2_0"
      by (rule subspace_topology_is_topology_on[OF hTR2']) simp
    have hext: "\<forall>x\<in>top1_S1. v x = v x" by simp
    show ?thesis by (rule Lemma_55_3_backward[OF hv_S1 hTR2_0 hv_B2 hext])
  qed
  \<comment> \<open>F(x,t) = tx + (1-t)v(x) is a homotopy from v|S^1 to inclusion j.
     F \<noteq> 0 because "no inward pointing" prevents cancellation.\<close>
  have hj_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
         (UNIV - {(0, 0)}))
      (\<lambda>x. x)"
  proof -
    let ?R2_0' = "UNIV - {(0::real, 0::real)}"
    let ?TR2_0' = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0'"
    have hhom_v_id: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x) (\<lambda>x. x)"
    proof -
      \<comment> \<open>F(x,t) = (1-t)*v(x) - t*x is a homotopy from v to -id in R²-{0}.
         F = 0 ⟹ v(x) = t/(1-t) · x with a = t/(1-t) > 0, contradicting assms(3).\<close>
      let ?F = "\<lambda>(x::real\<times>real, t::real). ((1-t) * fst (v x) - t * fst x,
                                          (1-t) * snd (v x) - t * snd x)"
      have hF0: "\<forall>x\<in>top1_S1. ?F (x, 0) = v x"
        by (by100 simp)
      have hF1: "\<forall>x\<in>top1_S1. ?F (x, 1) = (- fst x, - snd x)"
        by (by100 simp)
      have hF_nz: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?F (x, t) \<noteq> (0, 0)"
      proof (intro ballI)
        fix x :: "real \<times> real" and t :: real
        assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
        show "?F (x, t) \<noteq> (0, 0)"
        proof (cases "t = 0")
          case True
          \<comment> \<open>F(x,0) = v(x) \<noteq> 0 since v nonvanishing on B² \<supseteq> S¹.\<close>
          have "x \<in> top1_B2" using hx unfolding top1_S1_def top1_B2_def by (by100 auto)
          hence "v x \<noteq> (0, 0)" using assms(2) by (by100 blast)
          thus ?thesis using True by (by100 simp)
        next
          case False
          hence ht_pos: "t > 0" using ht unfolding top1_unit_interval_def by (by100 simp)
          show ?thesis
          proof (cases "t = 1")
            case True
            have "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
            hence hxnz: "x \<noteq> (0, 0)" by (cases x) (auto simp: sum_power2_gt_zero_iff)
            show ?thesis using hxnz True by (simp add: prod_eq_iff)
          next
            case False2: False
            hence h1mt_pos: "1 - t > 0" using ht unfolding top1_unit_interval_def by (by100 simp)
            show ?thesis
            proof
              assume habs: "?F (x, t) = (0, 0)"
              \<comment> \<open>From (1-t)*v_i(x) - t*x_i = 0, get v_i(x) = t/(1-t) * x_i.\<close>
              have habs1: "(1 - t) * fst (v x) = t * fst x"
                using habs by (simp add: prod_eq_iff)
              have habs2: "(1 - t) * snd (v x) = t * snd x"
                using habs by (simp add: prod_eq_iff)
              have hv1: "fst (v x) = t / (1 - t) * fst x"
                using habs1 h1mt_pos by (simp add: field_simps)
              have hv2: "snd (v x) = t / (1 - t) * snd x"
                using habs2 h1mt_pos by (simp add: field_simps)
              have ha_pos: "t / (1 - t) > 0" using ht_pos h1mt_pos by (by100 simp)
              have "v x = (t / (1 - t) * fst x, t / (1 - t) * snd x)"
                using hv1 hv2 by (simp add: prod_eq_iff)
              hence "\<exists>a>0. v x = (a * fst x, a * snd x)"
                using ha_pos by (by100 blast)
              hence "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
                using hx by (by100 blast)
              thus False using assms(3) by (by100 blast)
            qed
          qed
        qed
      qed
      have hv_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x)"
      proof -
        have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
        have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0'" using assms(2) by (by100 auto)
        have hv_B2: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0' ?TR2_0' (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg]) simp
        have hrestr: "top1_continuous_map_on top1_S1
            (subspace_topology top1_B2 top1_B2_topology top1_S1) ?R2_0' ?TR2_0' (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hv_B2 hS1_B2])
        have hS1_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
          unfolding top1_B2_topology_def top1_S1_topology_def
          using subspace_topology_trans[OF hS1_B2, of UNIV "product_topology_on top1_open_sets top1_open_sets"]
          by simp
        show ?thesis using hrestr unfolding hS1_eq .
      qed
      have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. x)"
      proof -
        have hS1_sub: "top1_S1 \<subseteq> ?R2_0'" unfolding top1_S1_def by (by100 auto)
        have hTR2_0_full: "is_topology_on ?R2_0' ?TR2_0'"
          by (simp add: product_topology_on_open_sets subspace_topology_is_topology_on
              top1_open_sets_is_topology_on_UNIV)
        have hid_full: "top1_continuous_map_on ?R2_0' ?TR2_0' ?R2_0' ?TR2_0' id"
          by (rule top1_continuous_map_on_id[OF hTR2_0_full])
        have hid_restr: "top1_continuous_map_on top1_S1
            (subspace_topology ?R2_0' ?TR2_0' top1_S1) ?R2_0' ?TR2_0' id"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_full hS1_sub])
        have hS1_eq: "subspace_topology ?R2_0' ?TR2_0' top1_S1 = top1_S1_topology"
          unfolding top1_S1_topology_def using subspace_topology_trans[OF hS1_sub] by simp
        have hid_eq: "(\<lambda>x::real\<times>real. x) = id" by (rule ext) simp
        show ?thesis using hid_restr unfolding hS1_eq hid_eq[symmetric] by simp
      qed
      have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
          ?R2_0' ?TR2_0' ?F"
      proof -
        \<comment> \<open>v is continuous_on B² (reverse transfer), hence on S¹.\<close>
        have hv_B2_std: "continuous_on top1_B2 v"
          using assms(1) unfolding top1_B2_topology_def
          by (rule top1_continuous_map_on_to_continuous_on_R2)
        have hS1_B2: "top1_S1 \<subseteq> top1_B2"
          unfolding top1_S1_def top1_B2_def by (by100 auto)
        have hv_S1_std: "continuous_on top1_S1 v"
          by (rule continuous_on_subset[OF hv_B2_std hS1_B2])
        \<comment> \<open>F(x,t) = ((1-t)*v₁(x)-t*x₁, (1-t)*v₂(x)-t*x₂) continuous on S¹×I.\<close>
        have hv_fst_cont: "continuous_on (top1_S1 \<times> I_set) (v \<circ> fst)"
          by (intro continuous_on_compose continuous_on_fst
              continuous_on_subset[OF hv_S1_std]) (by100 auto)
        have hfst_v: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. fst (v (fst p)))"
          by (intro continuous_on_fst[OF hv_fst_cont[unfolded comp_def]])
        have hsnd_v: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. snd (v (fst p)))"
          by (intro continuous_on_snd[OF hv_fst_cont[unfolded comp_def]])
        have hF_std: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            ((1 - snd p) * fst (v (fst p)) - snd p * fst (fst p),
             (1 - snd p) * snd (v (fst p)) - snd p * snd (fst p)))"
          by (intro continuous_on_Pair continuous_on_diff continuous_on_mult
              continuous_on_snd hfst_v hsnd_v continuous_intros)
        have hF_eq: "(\<lambda>p::(real\<times>real)\<times>real.
            ((1 - snd p) * fst (v (fst p)) - snd p * fst (fst p),
             (1 - snd p) * snd (v (fst p)) - snd p * snd (fst p)))
          = (\<lambda>p. ?F (fst p, snd p))" by (rule ext) (simp add: case_prod_beta)
        have hF_map: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?F p \<in> ?R2_0'"
          using hF_nz by (by100 auto)
        have hF_map': "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> (\<lambda>p. ?F (fst p, snd p)) p \<in> ?R2_0'"
          using hF_map by (simp add: case_prod_beta)
        have hF_std': "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. ?F (fst p, snd p))"
          using hF_std unfolding hF_eq .
        have "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
            ?R2_0' ?TR2_0' (\<lambda>p. ?F (fst p, snd p))"
          by (rule S1_I_to_R2_minus_0_continuous_on[OF hF_std' hF_map'])
        moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?F (fst p, snd p)) = ?F"
          by (rule ext) (simp add: case_prod_beta)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>F gives v ≃ -id. Need -id ≃ id (rotation). Then v ≃ id by transitivity.\<close>
      let ?neg = "\<lambda>x::real\<times>real. (- fst x, - snd x)"
      have hneg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' ?neg"
      proof -
        have hneg_std: "continuous_on UNIV ?neg"
          by (intro continuous_on_Pair continuous_intros)
        have hneg_map: "\<And>x. x \<in> top1_S1 \<Longrightarrow> ?neg x \<in> ?R2_0'"
          unfolding top1_S1_def by (by100 auto)
        have hneg_R2: "top1_continuous_map_on top1_S1
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1)
            ?R2_0' ?TR2_0' ?neg"
          by (rule top1_continuous_map_on_real2_subspace[OF hneg_map hneg_std])
        thus ?thesis unfolding top1_S1_topology_def .
      qed
      have hv_neg: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x) ?neg"
      proof -
        have hF1': "\<forall>x\<in>top1_S1. ?F (x, 1) = ?neg x" by (by100 simp)
        show ?thesis unfolding top1_homotopic_on_def
          using hv_cont hneg_cont hF_cont hF0 hF1' by (by100 blast)
      qed
      have hneg_id: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' ?neg (\<lambda>x. x)"
      proof -
        \<comment> \<open>Rotation R(x,t) = (cos(\<pi>(1-t)) a - sin(\<pi>(1-t)) b, sin(\<pi>(1-t)) a + cos(\<pi>(1-t)) b)
           R(x,0) = (-a,-b) = -x, R(x,1) = (a,b) = x. R maps into S¹ ⊂ R²-{0}.\<close>
        let ?R = "\<lambda>(x::real\<times>real, t::real).
            (cos (pi * (1 - t)) * fst x - sin (pi * (1 - t)) * snd x,
             sin (pi * (1 - t)) * fst x + cos (pi * (1 - t)) * snd x)"
        have hR0: "\<forall>x\<in>top1_S1. ?R (x, 0) = ?neg x" by (by100 simp)
        have hR1: "\<forall>x\<in>top1_S1. ?R (x, 1) = x" by (by100 simp)
        have hR_S1: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?R (x, t) \<in> top1_S1"
        proof (intro ballI)
          fix x :: "real \<times> real" and t :: real
          assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
          have hsum: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
          let ?c = "cos (pi * (1 - t))" and ?s = "sin (pi * (1 - t))"
          have "fst (?R (x, t)) ^ 2 + snd (?R (x, t)) ^ 2 = 1"
          proof -
            have "fst (?R (x, t)) ^ 2 + snd (?R (x, t)) ^ 2 =
                (?c * fst x - ?s * snd x) ^ 2 + (?s * fst x + ?c * snd x) ^ 2"
              by simp
            also have "\<dots> = (fst x ^ 2 + snd x ^ 2) * (?c ^ 2 + ?s ^ 2)"
              by algebra
            also have "\<dots> = 1" using hsum by simp
            finally show ?thesis .
          qed
          thus "?R (x, t) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
        qed
        have hR_R2: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?R (x, t) \<in> ?R2_0'"
        proof (intro ballI)
          fix x :: "real \<times> real" and t :: real
          assume "x \<in> top1_S1" and "t \<in> I_set"
          hence "?R (x, t) \<in> top1_S1" using hR_S1 by (by100 blast)
          thus "?R (x, t) \<in> ?R2_0'" unfolding top1_S1_def by (by100 auto)
        qed
        have hR_cont: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
            ?R2_0' ?TR2_0' ?R"
        proof -
          let ?Rf = "\<lambda>p::(real\<times>real)\<times>real.
              (cos (pi * (1 - snd p)) * fst (fst p) - sin (pi * (1 - snd p)) * snd (fst p),
               sin (pi * (1 - snd p)) * fst (fst p) + cos (pi * (1 - snd p)) * snd (fst p))"
          have hRf_eq: "?Rf = (\<lambda>p. ?R (fst p, snd p))"
            by (rule ext) (simp add: case_prod_beta)
          have hR_std: "continuous_on UNIV ?Rf"
            by (intro continuous_on_Pair continuous_intros)
          have hR_map: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?Rf p \<in> UNIV - {(0, 0)}"
            using hR_R2 unfolding hRf_eq by (by100 auto)
          have "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
              ?R2_0' ?TR2_0' ?Rf"
            by (rule S1_I_to_R2_minus_0_continuous[OF hR_std hR_map])
          moreover have "?Rf = ?R" unfolding hRf_eq
            by (rule ext) (simp add: case_prod_beta)
          ultimately show ?thesis by simp
        qed
        show ?thesis unfolding top1_homotopic_on_def
          using hneg_cont hid_cont hR_cont hR0 hR1 by (by100 blast)
      qed
      have hTR2_0': "is_topology_on ?R2_0' ?TR2_0'"
        by (simp add: product_topology_on_open_sets subspace_topology_is_topology_on
            top1_open_sets_is_topology_on_UNIV)
      have hTS1': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF hTR hTR] by simp
        show ?thesis unfolding top1_S1_topology_def
          by (rule subspace_topology_is_topology_on[OF hTR2]) simp
      qed
      show ?thesis
        by (rule Lemma_51_1_homotopic_trans[OF hTS1' hTR2_0' hv_neg hneg_id])
    qed
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR hTR] by simp
      show ?thesis unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    qed
    have hTR2_0': "is_topology_on ?R2_0' ?TR2_0'"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR hTR] by simp
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    qed
    show ?thesis
      by (rule nulhomotopic_homotopic_trans[OF hTS1 hTR2_0' hw_nul hhom_v_id])
  qed
  show False using Corollary_55_4_inclusion_not_nulhomotopic hj_nul by (by100 blast)
qed

theorem Theorem_55_5_vector_field:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) v"
      and "\<forall>x\<in>top1_B2. v x \<noteq> (0, 0)"
  shows "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
    and "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))"
  \<comment> \<open>Munkres Theorem 55.5: Suppose v doesn't point inward at any x\<in>S^1.
     Let w = v|S^1. Then w extends to B^2 \<rightarrow> R^2-0, so w is nulhomotopic.
     But F(x,t) = tx + (1-t)w(x) is a homotopy from w to inclusion j: S^1 \<rightarrow> R^2-0
     (F(x,t)\<noteq>0 because if tx+(1-t)w(x)=0 then w(x) = -t/(1-t) \<cdot> x points inward).
     So j is nulhomotopic, contradicting Corollary 55.4.
     For outward: apply to the vector field (x, -v(x)).\<close>
proof -
  \<comment> \<open>Inward: suppose v never points inward at any x \<in> S^1.\<close>
  have hinward: "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
  proof (rule ccontr)
    assume hnot: "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x))"
    show False by (rule vector_field_must_point_inward[OF assms hnot])
  qed
  \<comment> \<open>Outward: apply the inward result to -v.\<close>
  have houtward: "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))"
  proof -
    \<comment> \<open>Apply the inward result to -v: -v is continuous B^2 \<rightarrow> R^2 and nonvanishing.\<close>
    let ?neg_v = "\<lambda>x. (- fst (v x), - snd (v x))"
    have hnv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) ?neg_v"
    proof -
      \<comment> \<open>Negation (x,y) \<mapsto> (-x,-y) is continuous R^2 \<rightarrow> R^2.\<close>
      let ?neg = "\<lambda>p::real\<times>real. (- fst p, - snd p)"
      have hneg_cont: "continuous_on UNIV ?neg"
        by (intro continuous_on_Pair continuous_intros)
      have hneg_sub: "top1_continuous_map_on (UNIV :: (real\<times>real) set)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) UNIV)
          (UNIV :: (real\<times>real) set)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) UNIV) ?neg"
        by (rule top1_continuous_map_on_real2_subspace) (simp_all add: hneg_cont)
      have hneg_map: "top1_continuous_map_on UNIV (product_topology_on top1_open_sets top1_open_sets)
          UNIV (product_topology_on top1_open_sets top1_open_sets) ?neg"
        using hneg_sub unfolding subspace_topology_UNIV_self .
      \<comment> \<open>-v = neg \<circ> v.\<close>
      have heq: "?neg_v = ?neg \<circ> v" by (rule ext) (simp add: comp_def)
      have hv_full: "top1_continuous_map_on top1_B2 top1_B2_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) v" using assms(1) .
      show ?thesis unfolding heq
        by (rule top1_continuous_map_on_comp[OF hv_full hneg_map])
    qed
    have hnv_nz: "\<forall>x\<in>top1_B2. ?neg_v x \<noteq> (0, 0)"
    proof (intro ballI)
      fix x assume "x \<in> top1_B2"
      hence "v x \<noteq> (0, 0)" using assms(2) by (by100 blast)
      thus "?neg_v x \<noteq> (0, 0)" by (simp add: prod_eq_iff)
    qed
    \<comment> \<open>The inward argument for -v gives: \<exists>x\<in>S^1. \<exists>a>0. -v(x) = a*x.\<close>
    have "\<exists>x\<in>top1_S1. \<exists>a>0. ?neg_v x = (a * fst x, a * snd x)"
    proof (rule ccontr)
      assume "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. ?neg_v x = (a * fst x, a * snd x))"
      thus False by (rule vector_field_must_point_inward[OF hnv_cont hnv_nz])
    qed
    then obtain x a where hx: "x \<in> top1_S1" and ha: "a > 0"
        and hva: "?neg_v x = (a * fst x, a * snd x)" by (by100 blast)
    \<comment> \<open>-v(x) = a*x means v(x) = -a*x.\<close>
    have "v x = (-(a * fst x), -(a * snd x))"
      using hva by (simp add: prod_eq_iff)
    thus ?thesis using hx ha by (by100 blast)
  qed
  show "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)" by (rule hinward)
  show "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))" by (rule houtward)
qed

(** from \<S>55 Theorem 55.6: Brouwer fixed-point theorem for the disc.
    Munkres' proof: by contradiction. If f has no fixed point, v(x) = f(x) - x
    is a nonvanishing vector field on B^2. But v cannot point outward at any
    x \<in> S^1: that would mean f(x) - x = a x with a > 0, hence f(x) = (1+a)x has
    norm > 1, contradicting f: B^2 \<rightarrow> B^2. Theorem 55.5 gives such a point \<Rightarrow> \<bottom>. **)
theorem Theorem_55_6_brouwer:
  assumes hf: "top1_continuous_map_on top1_B2 top1_B2_topology top1_B2 top1_B2_topology f"
  shows "\<exists>x\<in>top1_B2. f x = x"
proof (rule ccontr)
  assume hnofix: "\<not> (\<exists>x\<in>top1_B2. f x = x)"
  \<comment> \<open>Step 1: define v(x) = f(x) - x.\<close>
  let ?v = "\<lambda>x::real\<times>real. (fst (f x) - fst x, snd (f x) - snd x)"
  \<comment> \<open>Step 2: v is continuous B^2 \<rightarrow> R^2.\<close>
  have hv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology
                  UNIV (product_topology_on top1_open_sets top1_open_sets) ?v"
    by (rule top1_B2_diff_continuous[OF hf])
  \<comment> \<open>Step 3: v is nonvanishing (from hnofix).\<close>
  have hv_nonzero: "\<forall>x\<in>top1_B2. ?v x \<noteq> (0, 0)"
  proof (intro ballI)
    fix x assume hxB2: "x \<in> top1_B2"
    have "f x \<noteq> x" using hnofix hxB2 by blast
    hence "fst (f x) \<noteq> fst x \<or> snd (f x) \<noteq> snd x"
      by (simp add: prod_eq_iff)
    thus "?v x \<noteq> (0, 0)" by auto
  qed
  \<comment> \<open>Step 4: by Theorem 55.5, some x \<in> S^1 has v(x) = a x for a > 0 (outward).\<close>
  obtain x a where hx: "x \<in> top1_S1" and ha: "a > 0"
      and hva: "?v x = (a * fst x, a * snd x)"
    using Theorem_55_5_vector_field(1)[OF hv_cont hv_nonzero] by blast
  \<comment> \<open>Step 5: then f(x) = (1+a) x. Since |x| = 1, |f(x)| = 1+a > 1, but f(x) \<in> B^2.\<close>
  have hfx: "f x = ((1 + a) * fst x, (1 + a) * snd x)"
  proof -
    have "fst (f x) - fst x = a * fst x" using hva by simp
    hence h1: "fst (f x) = (1 + a) * fst x" by (simp add: algebra_simps)
    have "snd (f x) - snd x = a * snd x" using hva by simp
    hence h2: "snd (f x) = (1 + a) * snd x" by (simp add: algebra_simps)
    show ?thesis using h1 h2 by (simp add: prod_eq_iff)
  qed
  have hx_norm: "fst x^2 + snd x^2 = 1" using hx unfolding top1_S1_def by simp
  have hfx_norm: "fst (f x)^2 + snd (f x)^2 = (1 + a)^2"
  proof -
    have h1: "fst (f x)^2 = (1 + a)^2 * fst x^2"
      using hfx by (simp add: power_mult_distrib)
    have h2: "snd (f x)^2 = (1 + a)^2 * snd x^2"
      using hfx by (simp add: power_mult_distrib)
    have "fst (f x)^2 + snd (f x)^2 = (1 + a)^2 * (fst x^2 + snd x^2)"
      using h1 h2 by (simp add: ring_distribs)
    also have "\<dots> = (1 + a)^2" using hx_norm by simp
    finally show ?thesis .
  qed
  have ha_pos: "(1 + a)^2 > 1"
  proof -
    have "(1 + a)^2 = 1 + 2*a + a^2" by (simp add: power2_sum)
    moreover have "2 * a + a^2 > 0" using ha by (simp add: add_pos_nonneg)
    ultimately show ?thesis by linarith
  qed
  hence "fst (f x)^2 + snd (f x)^2 > 1" using hfx_norm by simp
  moreover have "fst (f x)^2 + snd (f x)^2 \<le> 1"
  proof -
    have hxB2: "x \<in> top1_B2" using hx unfolding top1_S1_def top1_B2_def by simp
    have "f x \<in> top1_B2"
      using hf hxB2 unfolding top1_continuous_map_on_def by blast
    thus ?thesis unfolding top1_B2_def by simp
  qed
  ultimately show False by linarith
qed

section \<open>\<S>56 The Fundamental Theorem of Algebra\<close>

text \<open>Following Munkres' proof in 4 steps via the fundamental group of S^1:
  Step 1: f(z) = z^n on S^1 induces the "multiplication by n" homomorphism
          on pi_1(S^1), which is injective for n > 0.
  Step 2: g(z) = z^n as map S^1 -> R^2 - {0} is not nulhomotopic.
  Step 3: If |a_{n-1}| + ... + |a_0| < 1, the monic polynomial has a root in B^2.
  Step 4: General case by substitution x = cy with c large enough.\<close>

text \<open>Polymorphic subspace continuity transfer: if f is continuous_on UNIV
  and maps S to T, then f is top1_continuous_map_on with subspace topologies.\<close>
lemma top1_continuous_map_on_subspace_open_sets:
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on S (subspace_topology UNIV top1_open_sets S)
                               T (subspace_topology UNIV top1_open_sets T) f"
proof -
  have h1: "\<forall>x\<in>S. f x \<in> T" using hmap by (by100 blast)
  have h2: "\<forall>V\<in>subspace_topology UNIV top1_open_sets T.
      {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
  proof
    fix V assume "V \<in> subspace_topology UNIV top1_open_sets T"
    then obtain U where hUos: "U \<in> top1_open_sets" and hVeq: "V = T \<inter> U"
      unfolding subspace_topology_def by (by100 auto)
    have hUo: "open U" using hUos unfolding top1_open_sets_def by (by100 blast)
    have "open (f -` U \<inter> UNIV)"
      using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont] hUo by (by100 blast)
    hence hWo: "open (f -` U)" by (by100 simp)
    have "{x \<in> S. f x \<in> V} = S \<inter> (f -` U)"
      unfolding hVeq using hmap by (by100 auto)
    moreover have "(f -` U) \<in> top1_open_sets"
      using hWo unfolding top1_open_sets_def by (by100 blast)
    ultimately show "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def by (by100 blast)
  qed
  show ?thesis unfolding top1_continuous_map_on_def using h1 h2 by (by100 blast)
qed

text \<open>The complex unit circle.\<close>
definition top1_S1_complex :: "complex set" where
  "top1_S1_complex = {z. cmod z = 1}"

definition top1_S1_complex_topology :: "complex set set" where
  "top1_S1_complex_topology = subspace_topology UNIV top1_open_sets top1_S1_complex"

text \<open>The punctured complex plane C - {0}, same topology as ambient.\<close>
definition top1_C_minus_0 :: "complex set" where
  "top1_C_minus_0 = UNIV - {0}"

definition top1_C_minus_0_topology :: "complex set set" where
  "top1_C_minus_0_topology = subspace_topology UNIV top1_open_sets top1_C_minus_0"

(** Step 1: induced homomorphism of f(z) = z^n on S^1 is multiplication by n.

    Munkres' proof: the standard loop p_0(s) = e^{2\<pi>is} corresponds to 1 \<in> Z.
    Its image f \<circ> p_0(s) = e^{2\<pi>ins} lifts to s \<mapsto> ns, which corresponds to n.
    So f_* is multiplication by n on \<pi>_1(S^1, b_0) \<cong> Z, hence injective for n > 0.

    Here we only record the essential injectivity consequence: if two loops
    become path-homotopic after composition with z^n, then they were already
    path-homotopic. **)
lemma Theorem_56_1_step_1:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
                               top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)
       \<and> (\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
              \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
              \<and> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
                   (\<lambda>s. (f s)^n) (\<lambda>s. (g s)^n)
              \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g)"
  \<comment> \<open>Uses Theorem 54.5: \<pi>_1(S^1) \<cong> Z; f_* corresponds to multiplication by n.\<close>
proof -
  \<comment> \<open>Munkres: z^n is continuous on S^1 (polynomial).
     The induced map f_* on \<pi>_1(S^1) \<cong> Z is multiplication by n (since the standard
     generator lifts to s \<mapsto> s and f \<circ> p(s) = e^{2\<pi>ins} lifts to s \<mapsto> ns).
     Multiplication by n is injective for n > 0.\<close>
  have hcont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
      top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)"
    unfolding top1_S1_complex_topology_def
    by (rule top1_continuous_map_on_subspace_open_sets)
       (auto simp: top1_S1_complex_def norm_power intro: continuous_intros)
  have hinj: "\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
      \<and> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
           (\<lambda>s. (f s)^n) (\<lambda>s. (g s)^n)
      \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g" sorry
  show ?thesis using hcont hinj by blast
qed

(** Step 2: z^n as S^1 \<rightarrow> C - {0} is not nulhomotopic.

    Munkres' proof: g = j \<circ> f where j: S^1 \<hookrightarrow> C-{0} is inclusion and f = z^n.
    Since S^1 is a retract of C-{0} (retraction r(z) = z/|z|), j_* is injective.
    By Step 1, f_* is injective. So g_* = j_* \<circ> f_* is injective, hence nontrivial,
    hence g is not nulhomotopic. **)
lemma Theorem_56_1_step_2:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "\<not> top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
            top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
      top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
  \<comment> \<open>S^1 is a retract of C - {0} via r(z) = z/|z|. So j: S^1 \<hookrightarrow> C-{0} induces
     j_* injective. f = z^n induces f_* injective (Step 1).
     g = j \<circ> f: S^1 \<rightarrow> C-{0} induces g_* = j_* \<circ> f_* injective, hence nontrivial.\<close>
  have hj_inj: "\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
      \<and> top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1 f g
      \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g" sorry
  \<comment> \<open>g_* nontrivial contradicts g being nulhomotopic.\<close>
  \<comment> \<open>z^n nulhomotopic in C-{0} \<Rightarrow> for all loops f at 1, z^n \<circ> f ≃ const in C-{0}.
     By j_inj, z^n \<circ> f ≃ const in S^1. But z^n not nulhomotopic in S^1 (Step 1).\<close>
  \<comment> \<open>Actually: hnul says z^n (as S^1 \<rightarrow> C-{0}) is nulhomotopic.
     Since z^n: S^1 \<rightarrow> S^1 \<subseteq> C-{0}, nulhomotopic in C-{0} means
     (\<lambda>z. z^n) ≃ const in C-{0}.
     By hj_inj: homotopic in C-{0} \<Rightarrow> homotopic in S^1.
     Specifically, for any f with z^n \<circ> f ≃ const in C-{0}, by j_inj get in S^1.
     But this needs more structure than just the two facts.\<close>
  show False using hnul hj_inj sorry
qed

(** Step 3: FTA for polynomials with |a_{n-1}| + ... + |a_0| < 1.

    Munkres' proof: by contradiction. If there is no root in B^2, define
    k: B^2 \<rightarrow> C - {0} by k(z) = z^n + \<Sum> a_k z^k. Let h = k|_{S^1}. Since
    h extends over B^2, h is nulhomotopic. But F(z,t) = z^n + t*(\<Sum> a_k z^k)
    is a homotopy from g = z^n (Step 2: NOT nulhomotopic) to h in C - {0};
    F(z,t) \<ne> 0 because |F| \<ge> 1 - t*(\<Sum>|a_k|) > 0. Contradiction. **)
lemma Theorem_56_1_step_3:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes hn: "n > 0"
  and hbound: "(\<Sum>k<n. cmod (a k)) < 1"
  shows "\<exists>z. cmod z \<le> 1 \<and> z^n + (\<Sum>k<n. a k * z^k) = 0"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>z. cmod z \<le> 1 \<and> z^n + (\<Sum>k<n. a k * z^k) = 0)"
  \<comment> \<open>Define k: B^2 \<rightarrow> C-{0} by k(z) = z^n + \<Sum> a_j z^j.\<close>
  let ?k = "\<lambda>z::complex. z^n + (\<Sum>j<n. a j * z^j)"
  have hk_nonzero: "\<And>z. cmod z \<le> 1 \<Longrightarrow> ?k z \<noteq> 0" using hno by blast
  \<comment> \<open>Let h be k restricted to S^1.\<close>
  let ?h = "\<lambda>z::complex. ?k z"
  \<comment> \<open>h is nulhomotopic in C-{0} because it extends to B^2 \<rightarrow> C-{0}.\<close>
  have hh_nulhomo: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology ?h"
  proof -
    \<comment> \<open>Homotopy H(z,t) = k((1-t)*z) contracts S^1 to the point k(0).\<close>
    let ?H = "\<lambda>(z::complex, t::real). ?k ((1 - complex_of_real t) * z)"
    have hk0_nz: "?k 0 \<noteq> 0" using hk_nonzero[of 0] by simp
    have hk0_C: "?k 0 \<in> top1_C_minus_0" using hk0_nz unfolding top1_C_minus_0_def by (by100 blast)
    \<comment> \<open>H(z,0) = k(z) = h(z), H(z,1) = k(0).\<close>
    have hH0: "\<forall>z\<in>top1_S1_complex. ?H (z, 0) = ?h z" by (simp add: case_prod_beta)
    have hH1: "\<forall>z\<in>top1_S1_complex. ?H (z, 1) = ?k 0" by (simp add: case_prod_beta)
    \<comment> \<open>H maps S^1 \<times> I to C-{0}: (1-t)*z \<in> B^2 when z \<in> S^1, t \<in> I.\<close>
    have hH_range: "\<And>p. p \<in> top1_S1_complex \<times> I_set \<Longrightarrow> ?H p \<in> top1_C_minus_0"
    proof -
      fix p assume hp: "p \<in> top1_S1_complex \<times> I_set"
      have hz: "cmod (fst p) = 1" using hp unfolding top1_S1_complex_def by (by100 auto)
      have ht: "snd p \<in> I_set" using hp by (by100 auto)
      have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
        using ht unfolding top1_unit_interval_def by (by100 auto)+
      have "cmod ((1 - complex_of_real (snd p)) * fst p) = cmod (1 - complex_of_real (snd p))"
        using hz by (simp add: norm_mult)
      also have "\<dots> = \<bar>1 - snd p\<bar>"
        by (metis norm_of_real of_real_1 of_real_diff)
      finally have "cmod ((1 - complex_of_real (snd p)) * fst p) = \<bar>1 - snd p\<bar>" .
      also have "\<dots> = 1 - snd p" using ht0 ht1 by (by100 auto)
      also have "\<dots> \<le> 1" using ht0 by (by100 linarith)
      finally have "cmod ((1 - complex_of_real (snd p)) * fst p) \<le> 1" .
      hence "?k ((1 - complex_of_real (snd p)) * fst p) \<noteq> 0"
        by (rule hk_nonzero)
      thus "?H p \<in> top1_C_minus_0" unfolding top1_C_minus_0_def
        by (simp add: case_prod_beta)
    qed
    \<comment> \<open>H is continuous (polynomial composed with affine map).\<close>
    have hH_std: "continuous_on UNIV (\<lambda>p::complex\<times>real. ?k ((1 - complex_of_real (snd p)) * fst p))"
      by (intro continuous_intros)
    have hH_cont_univ: "continuous_on UNIV ?H"
      using hH_std by (simp add: case_prod_beta)
    \<comment> \<open>Transfer to custom topologies.\<close>
    have hdom_eq: "product_topology_on top1_S1_complex_topology I_top
        = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
            (top1_S1_complex \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_complex_topology I_top
          = product_topology_on
              (subspace_topology UNIV (top1_open_sets::complex set set) top1_S1_complex)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_complex_topology_def top1_unit_interval_topology_def by (rule refl)
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (top1_open_sets::complex set set) (top1_open_sets::real set set))
          (top1_S1_complex \<times> I_set)"
        by (rule Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV])
      also have "\<dots> = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
          (top1_S1_complex \<times> I_set)"
        by (simp add: product_topology_on_open_sets)
      finally show ?thesis .
    qed
    have hH_top: "top1_continuous_map_on (top1_S1_complex \<times> I_set)
        (product_topology_on top1_S1_complex_topology I_top)
        top1_C_minus_0 top1_C_minus_0_topology ?H"
    proof -
      have "top1_continuous_map_on (top1_S1_complex \<times> I_set)
          (subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set) (top1_S1_complex \<times> I_set))
          top1_C_minus_0 (subspace_topology UNIV (top1_open_sets :: complex set set) top1_C_minus_0) ?H"
        by (rule top1_continuous_map_on_subspace_open_sets[OF hH_range hH_cont_univ])
      thus ?thesis unfolding hdom_eq top1_C_minus_0_topology_def .
    qed
    \<comment> \<open>h is continuous (polynomial on S^1 to C-{0}).\<close>
    have hh_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
    proof (rule top1_continuous_map_on_subspace_open_sets)
      fix z assume "z \<in> top1_S1_complex"
      hence "cmod z = 1" unfolding top1_S1_complex_def by (by100 simp)
      hence "cmod z \<le> 1" by (by100 simp)
      hence "?k z \<noteq> 0" by (rule hk_nonzero)
      thus "?h z \<in> top1_C_minus_0" unfolding top1_C_minus_0_def by (by100 blast)
    next
      show "continuous_on UNIV ?h" by (intro continuous_intros)
    qed
    \<comment> \<open>const_{k(0)} is continuous.\<close>
    have hconst_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>_. ?k 0)"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
      by (rule top1_continuous_map_on_subspace_open_sets)
         (use hk0_C in \<open>auto simp: top1_C_minus_0_def intro: continuous_intros\<close>)
    \<comment> \<open>Assembly: homotopic h const → nulhomotopic.\<close>
    have "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h (\<lambda>_. ?k 0)"
      unfolding top1_homotopic_on_def using hh_cont hconst_cont hH_top hH0 hH1
      by (by100 blast)
    thus ?thesis unfolding top1_nulhomotopic_on_def using hk0_C by (by100 blast)
  qed
  \<comment> \<open>Homotopy F(z,t) = z^n + t*\<Sum>a_j z^j from g=z^n to h, all in C-{0}.\<close>
  let ?F = "\<lambda>(z::complex, t::real). z^n + complex_of_real t * (\<Sum>j<n. a j * z^j)"
  have hF_nonzero: "\<And>z t. cmod z = 1 \<Longrightarrow> t \<in> I_set \<Longrightarrow>
     z^n + complex_of_real t * (\<Sum>j<n. a j * z^j) \<noteq> 0"
    \<comment> \<open>Munkres inequality: |F| \<ge> 1 - t(\<Sum>|a_k|) > 0 since t \<le> 1 and \<Sum>|a_k| < 1.\<close>
  proof -
    fix z :: complex and t :: real
    assume hz: "cmod z = 1" and ht: "t \<in> I_set"
    have ht0: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
    have ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    have hzn: "cmod (z^n) = 1" using hz by (simp add: norm_power)
    have h_sum_bound: "cmod (\<Sum>j<n. a j * z^j) \<le> (\<Sum>j<n. cmod (a j))"
    proof -
      have "cmod (\<Sum>j<n. a j * z^j) \<le> (\<Sum>j<n. cmod (a j * z^j))"
        by (rule norm_sum)
      also have "\<dots> = (\<Sum>j<n. cmod (a j) * (cmod z)^j)"
        by (simp add: norm_mult norm_power)
      also have "\<dots> = (\<Sum>j<n. cmod (a j))" using hz by simp
      finally show ?thesis .
    qed
    have ht_sum: "t * (\<Sum>j<n. cmod (a j)) < 1"
    proof (cases "(\<Sum>j<n. cmod (a j)) = 0")
      case True thus ?thesis by simp
    next
      case False
      have hpos: "(\<Sum>j<n. cmod (a j)) > 0"
        using False sum_nonneg[of "{..<n}" "\<lambda>j. cmod (a j)"] by simp
      have "t * (\<Sum>j<n. cmod (a j)) \<le> 1 * (\<Sum>j<n. cmod (a j))"
        using ht1 hpos by (simp add: mult_right_mono)
      also have "\<dots> < 1" using hbound by simp
      finally show ?thesis .
    qed
    have hF_abs: "cmod (z^n + complex_of_real t * (\<Sum>j<n. a j * z^j))
                \<ge> 1 - t * (\<Sum>j<n. cmod (a j))"
    proof -
      let ?A = "z^n"
      let ?B = "complex_of_real t * (\<Sum>j<n. a j * z^j)"
      have htri: "cmod ?A \<le> cmod (?A + ?B) + cmod ?B"
        using norm_triangle_ineq4[of "?A + ?B" ?B] by (simp add: norm_minus_commute)
      have hnormB: "cmod ?B = t * cmod (\<Sum>j<n. a j * z^j)"
        by (simp add: norm_mult ht0)
      have hB_le: "cmod ?B \<le> t * (\<Sum>j<n. cmod (a j))"
        using hnormB h_sum_bound ht0 by (simp add: mult_left_mono)
      show ?thesis using htri hzn hB_le by linarith
    qed
    have "1 - t * (\<Sum>j<n. cmod (a j)) > 0" using ht_sum by simp
    hence "cmod (z^n + complex_of_real t * (\<Sum>j<n. a j * z^j)) > 0" using hF_abs by linarith
    thus "z^n + complex_of_real t * (\<Sum>j<n. a j * z^j) \<noteq> 0" by auto
  qed
  have hF_cont: "top1_continuous_map_on (top1_S1_complex \<times> I_set)
                   (product_topology_on top1_S1_complex_topology I_top)
                   top1_C_minus_0 top1_C_minus_0_topology ?F"
  proof -
    have hF_std: "continuous_on UNIV (\<lambda>p::complex\<times>real. fst p^n +
        complex_of_real (snd p) * (\<Sum>j<n. a j * fst p^j))"
      by (intro continuous_intros)
    have hF_range: "\<And>p. p \<in> top1_S1_complex \<times> I_set \<Longrightarrow> ?F p \<in> top1_C_minus_0"
    proof -
      fix p assume hp: "p \<in> top1_S1_complex \<times> I_set"
      have "cmod (fst p) = 1" using hp unfolding top1_S1_complex_def by (by100 auto)
      have "snd p \<in> I_set" using hp by (by100 auto)
      have "?F p \<noteq> 0" using hF_nonzero[OF \<open>cmod (fst p) = 1\<close> \<open>snd p \<in> I_set\<close>]
        by (simp add: case_prod_beta)
      thus "?F p \<in> top1_C_minus_0" unfolding top1_C_minus_0_def by (by100 blast)
    qed
    have hdom_eq: "product_topology_on top1_S1_complex_topology I_top
        = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
            (top1_S1_complex \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_complex_topology I_top
          = product_topology_on
              (subspace_topology UNIV (top1_open_sets::complex set set) top1_S1_complex)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_complex_topology_def top1_unit_interval_topology_def by (rule refl)
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (top1_open_sets::complex set set) (top1_open_sets::real set set))
          (top1_S1_complex \<times> I_set)"
        by (rule Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV])
      also have "\<dots> = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
          (top1_S1_complex \<times> I_set)"
        by (simp add: product_topology_on_open_sets)
      finally show ?thesis .
    qed
    have hF_cont_univ: "continuous_on UNIV ?F"
      using hF_std by (simp add: case_prod_beta comp_def)
    have "top1_continuous_map_on (top1_S1_complex \<times> I_set)
        (subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set) (top1_S1_complex \<times> I_set))
        top1_C_minus_0 (subspace_topology UNIV (top1_open_sets :: complex set set) top1_C_minus_0) ?F"
      by (rule top1_continuous_map_on_subspace_open_sets[OF hF_range hF_cont_univ])
    thus ?thesis unfolding hdom_eq top1_C_minus_0_topology_def .
  qed
  \<comment> \<open>g(z) = z^n is NOT nulhomotopic by Step 2, but would be nulhomotopic via F.\<close>
  have hg_notnull: "\<not> top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
    using Theorem_56_1_step_2[OF hn] .
  have hg_nulhomo: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
  proof -
    have hTR_c: "is_topology_on (UNIV::complex set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR_c]) simp
    have hTC0: "is_topology_on top1_C_minus_0 top1_C_minus_0_topology"
      unfolding top1_C_minus_0_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR_c]) simp
    \<comment> \<open>F(z,0) = z^n, F(z,1) = h(z).\<close>
    have hF0: "\<forall>z\<in>top1_S1_complex. ?F (z, 0) = z^n"
      by (simp add: case_prod_beta)
    have hF1: "\<forall>z\<in>top1_S1_complex. ?F (z, 1) = ?h z"
      by (simp add: case_prod_beta)
    \<comment> \<open>z^n is continuous S^1 \<rightarrow> C-{0} (polynomial, nonvanishing on S^1).\<close>
    have hg_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
      by (rule top1_continuous_map_on_subspace_open_sets)
         (auto simp: top1_S1_complex_def top1_C_minus_0_def norm_power hn
               intro: continuous_intros)
    \<comment> \<open>h is continuous (from nulhomotopic).\<close>
    have hh_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h"
      using hh_nulhomo unfolding top1_nulhomotopic_on_def top1_homotopic_on_def by (by100 blast)
    \<comment> \<open>F gives homotopy from z^n to h.\<close>
    have hhom_g_h: "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n) ?h"
      unfolding top1_homotopic_on_def
      using hg_cont hh_cont hF_cont hF0 hF1 by (by100 blast)
    \<comment> \<open>Symmetry: h ≃ z^n.\<close>
    have hhom_h_g: "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h (\<lambda>z. z^n)"
      by (rule Lemma_51_1_homotopic_sym[OF hhom_g_h hTS1c])
    \<comment> \<open>Transitivity: h nulhomotopic + h ≃ z^n \<Rightarrow> z^n nulhomotopic.\<close>
    show ?thesis
      by (rule nulhomotopic_homotopic_trans[OF hTS1c hTC0 hh_nulhomo hhom_h_g])
  qed
  show False using hg_notnull hg_nulhomo by blast
qed

(** Step 4: FTA general case: any monic polynomial has a root.
    Reduction: substitute x = cy for large c to reduce to Step 3.
    This is the statement of Theorem_56_1 proper in Munkres. **)
theorem Theorem_56_1_FTA:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes "n > 0"
  shows "\<exists>z. z^n + (\<Sum>k<n. a k * z^k) = 0"
proof -
  \<comment> \<open>Munkres Step 4: Choose c large so that \<Sum> |a_k/c^{n-k}| < 1.\<close>
  \<comment> \<open>Substitute x = cy: equation becomes y^n + \<Sum> (a_k / c^{n-k}) y^k = 0.\<close>
  \<comment> \<open>By Step 3, there's a root y_0 with |y_0| \<le> 1; then x_0 = c y_0 is a root.\<close>
  \<comment> \<open>Pick c = max 1 (1 + 2 * n * \<Sum> cmod (a k)). Then c \<ge> 1 and c > 2 n M where
      M = \<Sum> cmod (a k), so each term cmod(a k)/c^(n-k) \<le> cmod(a k)/c < M/(2nM) = 1/(2n)
      when M > 0, giving sum < 1/2 < 1. When M = 0 each cmod(a k) = 0, sum = 0 < 1.\<close>
  define M where "M = (\<Sum>k<n. cmod (a k))"
  define c where "c = M + 1"
  have hM: "M \<ge> 0" unfolding M_def by (simp add: sum_nonneg)
  have hc: "c > 0" unfolding c_def using hM by simp
  have hc_ge1: "c \<ge> 1" unfolding c_def using hM by simp
  have hc_pow_ge: "\<forall>k<n. c ^ (n - k) \<ge> c"
  proof (intro allI impI)
    fix k assume hk: "k < n"
    have hge1: "n - k \<ge> 1" using hk by simp
    have "c ^ 1 \<le> c ^ (n - k)"
      by (rule power_increasing[OF hge1 hc_ge1])
    thus "c ^ (n - k) \<ge> c" by simp
  qed
  have hsum_small: "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) < 1"
  proof -
    have h_each: "\<forall>k<n. cmod (a k) / c ^ (n - k) \<le> cmod (a k) / c"
    proof (intro allI impI)
      fix k assume hk: "k < n"
      have hcpos: "c ^ (n - k) > 0" using hc by (simp add: zero_less_power)
      have hcpow_ge_c: "c ^ (n - k) \<ge> c" using hc_pow_ge hk by blast
      have hak: "cmod (a k) \<ge> 0" by simp
      show "cmod (a k) / c ^ (n - k) \<le> cmod (a k) / c"
        using hc hcpos hcpow_ge_c hak by (simp add: frac_le)
    qed
    have h_sum_le: "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) \<le> (\<Sum>k<n. cmod (a k) / c)"
      by (rule sum_mono, simp add: h_each)
    also have "(\<Sum>k<n. cmod (a k) / c) = M / c"
      unfolding M_def by (simp add: sum_divide_distrib)
    also have "\<dots> < 1"
    proof -
      have "M / c < 1 \<longleftrightarrow> M < c" using hc by (simp add: divide_less_eq)
      moreover have "M < c" unfolding c_def by simp
      ultimately show ?thesis by blast
    qed
    finally show "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) < 1" .
  qed
  \<comment> \<open>New coefficients a'_k = a_k / c^{n-k}.\<close>
  let ?a' = "\<lambda>k. a k / complex_of_real (c ^ (n - k))"
  have h_cmod_eq: "\<forall>k<n. cmod (?a' k) = cmod (a k) / c ^ (n - k)"
    using hc by (simp add: norm_divide norm_power)
  have hbound': "(\<Sum>k<n. cmod (?a' k)) < 1"
    using h_cmod_eq hsum_small by simp
  obtain y where hy: "cmod y \<le> 1" and hroot': "y^n + (\<Sum>k<n. ?a' k * y^k) = 0"
    using Theorem_56_1_step_3[OF assms hbound'] by blast
  let ?x = "complex_of_real c * y"
  let ?cc = "complex_of_real c"
  have hcc_nz: "?cc \<noteq> 0" using hc by simp
  \<comment> \<open>Term-wise identity: c^n * (a k / c^(n-k) * y^k) = a k * (c*y)^k when k<n.\<close>
  have h_term: "\<And>k. k < n \<Longrightarrow> ?cc^n * (?a' k * y^k) = a k * ?x^k"
  proof -
    fix k :: nat assume hk: "k < n"
    have hpow_split: "?cc^n = ?cc^(n-k) * ?cc^k"
      using hk by (simp add: power_add[symmetric])
    have hpow_eq: "?cc^(n-k) = complex_of_real (c^(n-k))" by simp
    have "?cc^n * (?a' k * y^k) = ?cc^(n-k) * ?cc^k * (a k / complex_of_real (c^(n-k)) * y^k)"
      using hpow_split by simp
    also have "\<dots> = ?cc^k * (a k * y^k)"
      using hpow_eq hcc_nz by (simp add: field_simps power_not_zero)
    also have "\<dots> = a k * ?x^k"
      by (simp add: power_mult_distrib mult.commute mult.left_commute)
    finally show "?cc^n * (?a' k * y^k) = a k * ?x^k" .
  qed
  have h_cn_sum: "?cc^n * (\<Sum>k<n. ?a' k * y^k) = (\<Sum>k<n. a k * ?x^k)"
  proof -
    have "?cc^n * (\<Sum>k<n. ?a' k * y^k) = (\<Sum>k<n. ?cc^n * (?a' k * y^k))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k<n. a k * ?x^k)"
      by (rule sum.cong, simp, rule h_term, simp)
    finally show ?thesis .
  qed
  have hxn_eq: "?x^n = ?cc^n * y^n" by (simp add: power_mult_distrib)
  \<comment> \<open>Multiply root equation by c^n to get x-root equation.\<close>
  have "?cc^n * (y^n + (\<Sum>k<n. ?a' k * y^k)) = 0" using hroot' by simp
  hence "?cc^n * y^n + ?cc^n * (\<Sum>k<n. ?a' k * y^k) = 0"
    by (simp add: distrib_left)
  hence "?x^n + (\<Sum>k<n. a k * ?x^k) = 0"
    using hxn_eq h_cn_sum by simp
  thus ?thesis by blast
qed

text \<open>Original form (FTA for arbitrary polynomials with nonzero leading coefficient).\<close>
corollary Theorem_56_1_FTA_leading:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes "n > 0" and "a n \<noteq> 0"
  shows "\<exists>z. (\<Sum>k\<le>n. a k * z^k) = 0"
proof -
  \<comment> \<open>Divide by a n to get monic form.\<close>
  let ?b = "\<lambda>k. a k / a n"
  have hbn: "?b n = 1" using assms(2) by simp
  have "\<exists>z. z^n + (\<Sum>k<n. ?b k * z^k) = 0"
    by (rule Theorem_56_1_FTA[OF assms(1)])
  then obtain z where hroot_monic: "z^n + (\<Sum>k<n. ?b k * z^k) = 0"
    by blast
  \<comment> \<open>This z is a root of the original polynomial too.\<close>
  have h_split: "(\<Sum>k\<le>n. a k * z^k) = (\<Sum>k<n. a k * z^k) + a n * z^n"
    by (simp add: lessThan_Suc_atMost[symmetric] sum.lessThan_Suc)
  have h_factor: "(\<Sum>k<n. a k * z^k) = a n * (\<Sum>k<n. ?b k * z^k)"
    by (simp add: sum_distrib_left assms(2) field_simps)
  have "(\<Sum>k\<le>n. a k * z^k) = a n * (z^n + (\<Sum>k<n. ?b k * z^k))"
    using h_split h_factor by (simp add: distrib_left mult.commute)
  thus ?thesis using hroot_monic assms(2) by fastforce
qed


subsection \<open>General homotopy tools (needed for \<S>57 and \<S>58)\<close>


text \<open>Key: homotopy from h to k + loop l at x₀ implies h\<circ>l loop-equiv to basepoint-change of k\<circ>l.\<close>
lemma homotopy_induced_basepoint_change:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = h x" and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hl: "top1_is_loop_on X TX x0 l" and hx0: "x0 \<in> X"
  shows "top1_loop_equiv_on Y TY (h x0) (h \<circ> l)
    (top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse (\<lambda>t. H (x0, t))) (k \<circ> l))"
proof -
  let ?\<alpha> = "\<lambda>t. H (x0, t)"
  \<comment> \<open>G(s,t) = H(l(s), t) gives: G(s,0) = h(l(s)), G(s,1) = k(l(s)),
     G(0,t) = G(1,t) = \<alpha>(t). So G is a homotopy (h\<circ>l) \<simeq> (k\<circ>l) relative to \<alpha>.\<close>
  \<comment> \<open>From this, derive: (h\<circ>l) * \<alpha> \<simeq> \<alpha> * (k\<circ>l), hence h\<circ>l \<simeq> \<alpha>⁻¹ * (k\<circ>l) * \<alpha>.\<close>
  \<comment> \<open>The full proof requires the broken-line homotopy in I×I (convexity)
     and composition with G. This is Munkres Lemma 58.4.\<close>
  \<comment> \<open>Step 1: G(s,t) = H(l(s),t) is continuous I×I → Y.\<close>
  let ?G = "\<lambda>(s::real, t::real). H (l s, t)"
  have hG_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?G"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hl_cont: "top1_continuous_map_on I_set I_top X TX l"
      using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hpi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
      unfolding II_topology_def by (rule top1_continuous_pi2[OF hTI hTI])
    have hlfst: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (l \<circ> pi1)"
      by (rule top1_continuous_map_on_comp[OF hpi1 hl_cont])
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have heq: "(\<lambda>p. (l (pi1 p), pi2 p)) = (\<lambda>(s, t). (l s, t))"
      unfolding pi1_def pi2_def by (rule ext) (simp add: case_prod_beta)
    have hlid: "top1_continuous_map_on (I_set \<times> I_set) II_topology (X \<times> I_set)
        (product_topology_on TX I_top) (\<lambda>(s, t). (l s, t))"
    proof -
      have hT18: "\<And>f. (\<forall>c\<in>(I_set \<times> I_set). f c \<in> X \<times> I_set) \<and>
          top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (pi1 \<circ> f) \<and>
          top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top (pi2 \<circ> f)
          \<longrightarrow> top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
              (X \<times> I_set) (product_topology_on TX I_top) f"
        using Theorem_18_4[OF hTII[unfolded II_topology_def] hTX hTI] by (by100 blast)
      have hcomp1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX
          (pi1 \<circ> (\<lambda>(s, t). (l s, t)))"
      proof -
        have "pi1 \<circ> (\<lambda>(s, t). (l s, t)) = l \<circ> pi1"
          unfolding pi1_def comp_def by (rule ext) (simp add: case_prod_beta)
        show ?thesis using hlfst unfolding \<open>pi1 \<circ> (\<lambda>(s, t). (l s, t)) = l \<circ> pi1\<close> II_topology_def .
      qed
      have hcomp2: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top
          (pi2 \<circ> (\<lambda>(s, t). (l s, t)))"
      proof -
        have "pi2 \<circ> (\<lambda>(s, t). (l s, t)) = pi2"
          unfolding pi2_def comp_def by (rule ext) (simp add: case_prod_beta)
        show ?thesis using hpi2 unfolding \<open>pi2 \<circ> (\<lambda>(s, t). (l s, t)) = pi2\<close> II_topology_def .
      qed
      have hrange: "\<forall>c\<in>(I_set \<times> I_set). (\<lambda>(s, t). (l s, t)) c \<in> X \<times> I_set"
        using hl_cont unfolding top1_continuous_map_on_def by (by100 auto)
      have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
          (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>(s, t). (l s, t))"
        using hT18 hcomp1 hcomp2 hrange by (by100 blast)
      thus ?thesis unfolding II_topology_def .
    qed
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (H \<circ> (\<lambda>(s, t). (l s, t)))"
      by (rule top1_continuous_map_on_comp[OF hlid hHcont])
    moreover have "(H \<circ> (\<lambda>(s, t). (l s, t))) = ?G"
      by (rule ext) (simp add: comp_def case_prod_beta)
    ultimately show ?thesis by simp
  qed
  have hl0: "l 0 = x0" using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hl1: "l 1 = x0" using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hG_bot: "\<forall>s\<in>I_set. ?G (s, 0) = (h \<circ> l) s"
  proof (intro ballI)
    fix s assume "s \<in> I_set"
    have "l s \<in> X" using hl \<open>s \<in> I_set\<close>
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    thus "?G (s, 0) = (h \<circ> l) s" using hH0 by (by100 simp)
  qed
  have hG_top: "\<forall>s\<in>I_set. ?G (s, 1) = (k \<circ> l) s"
  proof (intro ballI)
    fix s assume "s \<in> I_set"
    have "l s \<in> X" using hl \<open>s \<in> I_set\<close>
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    thus "?G (s, 1) = (k \<circ> l) s" using hH1 by (by100 simp)
  qed
  have hG_left: "\<forall>t\<in>I_set. ?G (0, t) = ?\<alpha> t"
    using hl0 by (by100 simp)
  have hG_right: "\<forall>t\<in>I_set. ?G (1, t) = ?\<alpha> t"
    using hl1 by (by100 simp)
  \<comment> \<open>Step 2: (h\<circ>l)*\<alpha> \<simeq> \<alpha>*(k\<circ>l) via broken-line homotopy in I×I.
     The convexity of I×I gives a homotopy between the two broken-line paths.\<close>
  have hprod_hom: "top1_path_homotopic_on Y TY (h x0) (k x0)
      (top1_path_product (h \<circ> l) ?\<alpha>)
      (top1_path_product ?\<alpha> (k \<circ> l))"
  proof -
    \<comment> \<open>Broken-line paths in I×I: β₁ = bottom*right, β₂ = left*top.
       G∘β₁ = (h∘l)*α, G∘β₂ = α*(k∘l).
       β₁ ≃ β₂ in I×I (convexity). Apply G.\<close>
    \<comment> \<open>Define β₁, β₂ as path products in I×I.\<close>
    let ?bottom = "\<lambda>s::real. (s, 0::real)"
    let ?right = "\<lambda>t::real. (1::real, t)"
    let ?left' = "\<lambda>t::real. (0::real, t)"
    let ?top' = "\<lambda>s::real. (s, 1::real)"
    \<comment> \<open>β₁ = bottom * right, β₂ = left * top.\<close>
    let ?\<beta>1 = "top1_path_product ?bottom ?right"
    let ?\<beta>2 = "top1_path_product ?left' ?top'"
    \<comment> \<open>β₁ and β₂ both go from (0,0) to (1,1) in I×I.
       They're path-homotopic in I×I because I×I is convex (simply connected).\<close>
    have hII_sc: "top1_simply_connected_on (I_set \<times> I_set) II_topology"
      unfolding top1_simply_connected_on_def
    proof (intro conjI)
      show "top1_path_connected_on (I_set \<times> I_set) II_topology"
        unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def
          by (rule product_topology_on_is_topology_on[OF
                top1_unit_interval_topology_is_topology_on
                top1_unit_interval_topology_is_topology_on])
      next
        fix x y :: "real \<times> real"
        assume hx: "x \<in> I_set \<times> I_set" and hy: "y \<in> I_set \<times> I_set"
        let ?\<gamma> = "\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y)"
        have hg_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?\<gamma>"
        proof -
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          have hc1_cont: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst x + t * fst y)"
            by (intro continuous_intros)
          have hc2_cont: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd x + t * snd y)"
            by (intro continuous_intros)
          have hc1_range: "\<And>t. t \<in> I_set \<Longrightarrow> (1-t) * fst x + t * fst y \<in> I_set"
          proof -
            fix t assume ht: "t \<in> I_set"
            have ht': "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
            have ha: "0 \<le> fst x" "fst x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 auto)+
            have hb: "0 \<le> fst y" "fst y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - t" using ht' by (by100 linarith)
            have h1: "0 \<le> (1-t) * fst x + t * fst y"
              using mult_nonneg_nonneg[OF h0t ha(1)] mult_nonneg_nonneg[OF ht'(1) hb(1)]
              by (by100 linarith)
            have h2: "(1-t) * fst x + t * fst y \<le> 1"
              by (rule convex_bound_le[OF ha(2) hb(2) h0t ht'(1)]) (by100 simp)
            show "(1-t) * fst x + t * fst y \<in> I_set"
              unfolding top1_unit_interval_def using h1 h2 by (by100 auto)
          qed
          have hc2_range: "\<And>t. t \<in> I_set \<Longrightarrow> (1-t) * snd x + t * snd y \<in> I_set"
          proof -
            fix t assume ht: "t \<in> I_set"
            have ht': "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
            have ha: "0 \<le> snd x" "snd x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 auto)+
            have hb: "0 \<le> snd y" "snd y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - t" using ht' by (by100 linarith)
            have h1: "0 \<le> (1-t) * snd x + t * snd y"
              using mult_nonneg_nonneg[OF h0t ha(1)] mult_nonneg_nonneg[OF ht'(1) hb(1)]
              by (by100 linarith)
            have h2: "(1-t) * snd x + t * snd y \<le> 1"
              by (rule convex_bound_le[OF ha(2) hb(2) h0t ht'(1)]) (by100 simp)
            show "(1-t) * snd x + t * snd y \<in> I_set"
              unfolding top1_unit_interval_def using h1 h2 by (by100 auto)
          qed
          have hc1: "top1_continuous_map_on I_set I_top I_set I_top
              (\<lambda>t. (1-t) * fst x + t * fst y)"
            unfolding top1_unit_interval_topology_def
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hc1_range hc1_cont])
          have hc2: "top1_continuous_map_on I_set I_top I_set I_top
              (\<lambda>t. (1-t) * snd x + t * snd y)"
            unfolding top1_unit_interval_topology_def
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hc2_range hc2_cont])
          have hpi1_eq: "pi1 \<circ> ?\<gamma> = (\<lambda>t. (1-t) * fst x + t * fst y)"
            unfolding pi1_def comp_def by (rule ext) simp
          have hpi2_eq: "pi2 \<circ> ?\<gamma> = (\<lambda>t. (1-t) * snd x + t * snd y)"
            unfolding pi2_def comp_def by (rule ext) simp
          show ?thesis unfolding II_topology_def
            using iffD2[OF Theorem_18_4[OF hTI hTI hTI]]
                  hc1[unfolded hpi1_eq[symmetric]] hc2[unfolded hpi2_eq[symmetric]]
            by (by100 blast)
        qed
        have hg0: "?\<gamma> 0 = x" by (simp add: prod_eq_iff)
        have hg1: "?\<gamma> 1 = y" by (simp add: prod_eq_iff)
        show "\<exists>f. top1_is_path_on (I_set \<times> I_set) II_topology x y f"
          unfolding top1_is_path_on_def using hg_cont hg0 hg1 by (by100 blast)
      qed
    next
      show "\<forall>x0\<in>I_set \<times> I_set. \<forall>f. top1_is_loop_on (I_set \<times> I_set) II_topology x0 f \<longrightarrow>
          top1_path_homotopic_on (I_set \<times> I_set) II_topology x0 x0 f (top1_constant_path x0)"
      proof (intro ballI allI impI)
        fix x0 :: "real \<times> real" and f :: "real \<Rightarrow> real \<times> real"
        assume hx0: "x0 \<in> I_set \<times> I_set" and hf: "top1_is_loop_on (I_set \<times> I_set) II_topology x0 f"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hTII': "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
        \<comment> \<open>Straight-line homotopy: F(s,t) = (1-t)*f(s) + t*x0.\<close>
        let ?F = "\<lambda>(s::real, t::real). ((1-t) * fst (f s) + t * fst x0,
                                        (1-t) * snd (f s) + t * snd x0)"
        have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
            (I_set \<times> I_set) II_topology ?F"
        proof -
          \<comment> \<open>Bridge: extract continuous_on from f's custom continuity.\<close>
          have hfc: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology f"
            using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hfr: "\<forall>s\<in>I_set. f s \<in> I_set \<times> I_set"
            using hfc unfolding top1_continuous_map_on_def by (by100 blast)
          have hf_cont_on: "continuous_on I_set f"
          proof (unfold continuous_on_open_invariant, intro allI impI)
            fix U :: "(real \<times> real) set" assume hUo: "open U"
            have hU_top: "(I_set \<times> I_set) \<inter> U \<in> II_topology"
            proof -
              have "U \<in> (top1_open_sets :: (real\<times>real) set set)"
                using hUo unfolding top1_open_sets_def by (by100 blast)
              hence "U \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              thus ?thesis unfolding II_topology_def II_topology_eq_subspace
                subspace_topology_def by (by100 blast)
            qed
            have hpre_II: "{x \<in> I_set. f x \<in> (I_set \<times> I_set) \<inter> U} \<in> I_top"
              using hfc hU_top unfolding top1_continuous_map_on_def by (by100 blast)
            have hpre_eq: "{x \<in> I_set. f x \<in> U} = {x \<in> I_set. f x \<in> (I_set \<times> I_set) \<inter> U}"
              using hfr by (by100 auto)
            have hmem: "{x \<in> I_set. f x \<in> U} \<in> I_top" using hpre_II hpre_eq by (by100 simp)
            then obtain W where hWo: "open W" and hWeq: "{x \<in> I_set. f x \<in> U} = I_set \<inter> W"
              unfolding top1_unit_interval_topology_def subspace_topology_def
                        top1_open_sets_def by (by100 auto)
            have "W \<inter> I_set = f -` U \<inter> I_set" using hWeq by (by100 blast)
            hence "open W \<and> W \<inter> I_set = f -` U \<inter> I_set" using hWo by (by100 blast)
            thus "\<exists>A. open A \<and> A \<inter> I_set = f -` U \<inter> I_set" by (by100 blast)
          qed
          \<comment> \<open>continuous_on components.\<close>
          have hfst_cont: "continuous_on I_set (\<lambda>s. fst (f s))"
            using continuous_on_fst[OF hf_cont_on] unfolding comp_def .
          have hsnd_cont: "continuous_on I_set (\<lambda>s. snd (f s))"
            using continuous_on_snd[OF hf_cont_on] unfolding comp_def .
          \<comment> \<open>F is continuous_on (work with explicit fst/snd form, then match case_prod).\<close>
          let ?F' = "\<lambda>p::real\<times>real. ((1 - snd p) * fst (f (fst p)) + snd p * fst x0,
                                      (1 - snd p) * snd (f (fst p)) + snd p * snd x0)"
          have hf_fst_co: "continuous_on (I_set \<times> I_set) (\<lambda>p. f (fst p))"
            by (rule continuous_on_compose2[OF hf_cont_on continuous_on_fst]) (by100 auto)
          have hF'_co: "continuous_on (I_set \<times> I_set) ?F'"
            by (intro continuous_on_Pair continuous_on_add continuous_on_mult
                   continuous_on_diff continuous_on_const continuous_on_fst continuous_on_snd
                   continuous_on_id hf_fst_co)
          have hF_eq: "?F' = ?F" by (rule ext) (simp add: case_prod_beta)
          have hF_co: "continuous_on (I_set \<times> I_set) ?F" using hF'_co unfolding hF_eq .
          \<comment> \<open>Range in I_set \<times> I_set (convexity).\<close>
          have hF_range: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?F p \<in> I_set \<times> I_set"
          proof -
            fix p :: "real \<times> real" assume hp: "p \<in> I_set \<times> I_set"
            have ht': "0 \<le> snd p" "snd p \<le> 1" using hp unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - snd p" using ht' by (by100 linarith)
            have hfs: "f (fst p) \<in> I_set \<times> I_set" using hfr hp by (by100 auto)
            have hfa: "0 \<le> fst (f (fst p))" "fst (f (fst p)) \<le> 1" using hfs unfolding top1_unit_interval_def by (by100 auto)+
            have hfb: "0 \<le> snd (f (fst p))" "snd (f (fst p)) \<le> 1" using hfs unfolding top1_unit_interval_def by (by100 auto)+
            have hxa: "0 \<le> fst x0" "fst x0 \<le> 1" using hx0 unfolding top1_unit_interval_def by (by100 auto)+
            have hxb: "0 \<le> snd x0" "snd x0 \<le> 1" using hx0 unfolding top1_unit_interval_def by (by100 auto)+
            have "0 \<le> (1 - snd p) * fst (f (fst p)) + snd p * fst x0"
              using mult_nonneg_nonneg[OF h0t hfa(1)] mult_nonneg_nonneg[OF ht'(1) hxa(1)]
              by (by100 linarith)
            moreover have "(1 - snd p) * fst (f (fst p)) + snd p * fst x0 \<le> 1"
              by (rule convex_bound_le[OF hfa(2) hxa(2) h0t ht'(1)]) (by100 simp)
            moreover have "0 \<le> (1 - snd p) * snd (f (fst p)) + snd p * snd x0"
              using mult_nonneg_nonneg[OF h0t hfb(1)] mult_nonneg_nonneg[OF ht'(1) hxb(1)]
              by (by100 linarith)
            moreover have "(1 - snd p) * snd (f (fst p)) + snd p * snd x0 \<le> 1"
              by (rule convex_bound_le[OF hfb(2) hxb(2) h0t ht'(1)]) (by100 simp)
            ultimately show "?F p \<in> I_set \<times> I_set"
              unfolding top1_unit_interval_def by (simp add: case_prod_beta)
          qed
          \<comment> \<open>Transfer via subspace topology bridge.\<close>
          have "top1_continuous_map_on (I_set \<times> I_set)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
            (I_set \<times> I_set)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)) ?F"
            by (rule top1_continuous_map_on_real2_subspace_general[OF hF_range hF_co])
          thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
        qed
        have hF0: "\<forall>s\<in>I_set. ?F (s, 0) = f s"
          by (auto simp: prod_eq_iff)
        have hF1: "\<forall>s\<in>I_set. ?F (s, 1) = x0"
          by (auto simp: prod_eq_iff)
        have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hFl: "\<forall>t\<in>I_set. ?F (0, t) = x0"
          using hf0 by (auto simp: prod_eq_iff algebra_simps)
        have hFr: "\<forall>t\<in>I_set. ?F (1, t) = x0"
          using hf1 by (auto simp: prod_eq_iff algebra_simps)
        have hf_path: "top1_is_path_on (I_set \<times> I_set) II_topology x0 x0 f"
          using hf unfolding top1_is_loop_on_def by (by100 blast)
        have hconst_path: "top1_is_path_on (I_set \<times> I_set) II_topology x0 x0 (top1_constant_path x0)"
          by (rule top1_constant_path_is_path[OF hTII' hx0])
        have hF1': "\<forall>s\<in>I_set. ?F (s, 1) = top1_constant_path x0 s"
          using hF1 by (simp add: top1_constant_path_value)
        show "top1_path_homotopic_on (I_set \<times> I_set) II_topology x0 x0 f (top1_constant_path x0)"
          unfolding top1_path_homotopic_on_def
          using hf_path hconst_path hF_cont hF0 hF1' hFl hFr by (by100 blast)
      qed
    qed
    have h00: "(0::real, 0::real) \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    have h0I: "(0::real) \<in> I_set" and h1I: "(1::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)+
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def
      by (rule product_topology_on_is_topology_on[OF
            top1_unit_interval_topology_is_topology_on top1_unit_interval_topology_is_topology_on])
    have hbot_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?bottom"
      by (rule pair_s_const_continuous[OF h0I])
    have hright_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?right"
      by (rule pair_const_t_continuous[OF h1I])
    have hleft_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?left'"
      by (rule pair_const_t_continuous[OF h0I])
    have htop_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?top'"
      by (rule pair_s_const_continuous[OF h1I])
    have hbot_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 0) ?bottom"
      unfolding top1_is_path_on_def using hbot_cont by (by100 simp)
    have hright_path: "top1_is_path_on (I_set \<times> I_set) II_topology (1, 0) (1, 1) ?right"
      unfolding top1_is_path_on_def using hright_cont by (by100 simp)
    have hleft_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (0, 1) ?left'"
      unfolding top1_is_path_on_def using hleft_cont by (by100 simp)
    have htop_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 1) (1, 1) ?top'"
      unfolding top1_is_path_on_def using htop_cont by (by100 simp)
    have h\<beta>1_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>1"
      by (rule top1_path_product_is_path[OF hTII hbot_path hright_path])
    have h\<beta>2_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>2"
      by (rule top1_path_product_is_path[OF hTII hleft_path htop_path])
    have h\<beta>_hom: "top1_path_homotopic_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>1 ?\<beta>2"
      by (rule simply_connected_paths_homotopic[OF hII_sc h\<beta>1_path h\<beta>2_path h00])
    \<comment> \<open>G∘β₁ = (h∘l)*α and G∘β₂ = α*(k∘l).\<close>
    have hG\<beta>1: "\<forall>s\<in>I_set. (?G \<circ> ?\<beta>1) s = top1_path_product (h \<circ> l) ?\<alpha> s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      show "(?G \<circ> ?\<beta>1) s = top1_path_product (h \<circ> l) ?\<alpha> s"
        unfolding comp_def top1_path_product_def case_prod_beta
        using hG_bot hG_right hs hl1
        unfolding top1_unit_interval_def by (by100 auto)
    qed
    have hG\<beta>2: "\<forall>s\<in>I_set. (?G \<circ> ?\<beta>2) s = top1_path_product ?\<alpha> (k \<circ> l) s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      show "(?G \<circ> ?\<beta>2) s = top1_path_product ?\<alpha> (k \<circ> l) s"
        unfolding comp_def top1_path_product_def case_prod_beta
        using hG_left hG_top hs hl0
        unfolding top1_unit_interval_def by (by100 auto)
    qed
    \<comment> \<open>G preserves homotopy: G∘β₁ ≃ G∘β₂.\<close>
    have "top1_path_homotopic_on Y TY (?G (0, 0)) (?G (1, 1))
        (?G \<circ> ?\<beta>1) (?G \<circ> ?\<beta>2)"
      by (rule continuous_preserves_path_homotopic[OF
            product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on,
              unfolded II_topology_def[symmetric]]
            hTY hG_cont h\<beta>_hom])
    \<comment> \<open>?G(0,0) = H(x₀,0) = h(x₀), ?G(1,1) = H(x₀,1) = k(x₀).\<close>
    hence hGhom: "top1_path_homotopic_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>1) (?G \<circ> ?\<beta>2)"
      using hH0 hH1 hx0 hl0 hl1 by (by100 simp)
    \<comment> \<open>Transfer via agreement on I: G∘β₁ agrees with (h∘l)*α, etc.\<close>
    show ?thesis unfolding top1_path_homotopic_on_def
    proof -
      from hGhom obtain F where
          hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F"
          and hF0: "\<forall>s\<in>I_set. F (s, 0) = (?G \<circ> ?\<beta>1) s"
          and hF1: "\<forall>s\<in>I_set. F (s, 1) = (?G \<circ> ?\<beta>2) s"
          and hFl: "\<forall>t\<in>I_set. F (0, t) = h x0"
          and hFr: "\<forall>t\<in>I_set. F (1, t) = k x0"
        using hGhom unfolding top1_path_homotopic_on_def by (by100 auto)
      have hF0': "\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s"
        using hF0 hG\<beta>1 by (by100 simp)
      have hF1': "\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s"
        using hF1 hG\<beta>2 by (by100 simp)
      show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product (h \<circ> l) ?\<alpha>)
          \<and> top1_is_path_on Y TY (h x0) (k x0) (top1_path_product ?\<alpha> (k \<circ> l))
          \<and> (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F
              \<and> (\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s)
              \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s)
              \<and> (\<forall>t\<in>I_set. F (0, t) = h x0)
              \<and> (\<forall>t\<in>I_set. F (1, t) = k x0))"
      proof (intro conjI)
        \<comment> \<open>is_path_on for path products: follows from G∘β being paths + pointwise agreement.\<close>
        have hGb1_path: "top1_is_path_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>1)"
          using hGhom unfolding top1_path_homotopic_on_def by (by100 blast)
        have hGb2_path: "top1_is_path_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>2)"
          using hGhom unfolding top1_path_homotopic_on_def by (by100 blast)
        have hGb1_cont: "top1_continuous_map_on I_set I_top Y TY (?G \<circ> ?\<beta>1)"
          using hGb1_path unfolding top1_is_path_on_def by (by100 blast)
        have hGb2_cont: "top1_continuous_map_on I_set I_top Y TY (?G \<circ> ?\<beta>2)"
          using hGb2_path unfolding top1_is_path_on_def by (by100 blast)
        have hprod1_cont: "top1_continuous_map_on I_set I_top Y TY (top1_path_product (h \<circ> l) ?\<alpha>)"
          by (rule top1_continuous_map_on_agree'[OF hGb1_cont hG\<beta>1])
        have hprod2_cont: "top1_continuous_map_on I_set I_top Y TY (top1_path_product ?\<alpha> (k \<circ> l))"
          by (rule top1_continuous_map_on_agree'[OF hGb2_cont hG\<beta>2])
        show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product (h \<circ> l) ?\<alpha>)"
          using hGb1_path hG\<beta>1 hprod1_cont unfolding top1_is_path_on_def
          by (simp add: hl0 hl1 top1_path_product_at_end top1_path_product_at_start)
        show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product ?\<alpha> (k \<circ> l))"
          using hGb2_path hG\<beta>2 hprod2_cont unfolding top1_is_path_on_def
          by (simp add: hH0 hl1 hx0 top1_path_product_at_end top1_path_product_at_start)
        show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F
            \<and> (\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s)
            \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s)
            \<and> (\<forall>t\<in>I_set. F (0, t) = h x0)
            \<and> (\<forall>t\<in>I_set. F (1, t) = k x0)"
          using hF hF0' hF1' hFl hFr by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: From (h\<circ>l)*\<alpha> \<simeq> \<alpha>*(k\<circ>l), derive h\<circ>l \<simeq> \<alpha>⁻¹*(k\<circ>l)*\<alpha>.\<close>
  have h0I': "(0::real) \<in> I_set" and h1I': "(1::real) \<in> I_set"
    unfolding top1_unit_interval_def by (by100 simp)+
  \<comment> \<open>First establish \<alpha> is a path h(x0) \<rightarrow> k(x0), using G restricted to s=0.\<close>
  have h\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY ?\<alpha>"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>t. (0::real, t)))"
      by (rule top1_continuous_map_on_comp[OF pair_const_t_continuous[OF h0I'] hG_cont])
    moreover have "\<forall>t\<in>I_set. (?G \<circ> (\<lambda>t. (0, t))) t = ?\<alpha> t"
      using hG_left by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have h\<alpha>_path: "top1_is_path_on Y TY (h x0) (k x0) ?\<alpha>"
    unfolding top1_is_path_on_def using h\<alpha>_cont hH0 hH1 hx0 by (by100 auto)
  have hrev\<alpha>_path: "top1_is_path_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
  \<comment> \<open>h\<circ>l is a loop at h(x0): via G restricted to t=0.\<close>
  have hhl_cont: "top1_continuous_map_on I_set I_top Y TY (h \<circ> l)"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>s. (s, 0::real)))"
      by (rule top1_continuous_map_on_comp[OF pair_s_const_continuous[OF h0I'] hG_cont])
    moreover have "\<forall>s\<in>I_set. (?G \<circ> (\<lambda>s. (s, 0))) s = (h \<circ> l) s"
      using hG_bot by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have hhl_loop: "top1_is_loop_on Y TY (h x0) (h \<circ> l)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hhl_cont hl0 hl1 by (by100 auto)
  have hhl_path: "top1_is_path_on Y TY (h x0) (h x0) (h \<circ> l)"
    using hhl_loop unfolding top1_is_loop_on_def by blast
  \<comment> \<open>k\<circ>l is a loop at k(x0): via G restricted to t=1.\<close>
  have hkl_cont: "top1_continuous_map_on I_set I_top Y TY (k \<circ> l)"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>s. (s, 1::real)))"
      by (rule top1_continuous_map_on_comp[OF pair_s_const_continuous[OF h1I'] hG_cont])
    moreover have "\<forall>s\<in>I_set. (?G \<circ> (\<lambda>s. (s, 1))) s = (k \<circ> l) s"
      using hG_top by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have hkl_loop: "top1_is_loop_on Y TY (k x0) (k \<circ> l)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hkl_cont hl0 hl1 by (by100 auto)
  have hkl_path: "top1_is_path_on Y TY (k x0) (k x0) (k \<circ> l)"
    using hkl_loop unfolding top1_is_loop_on_def by blast
  \<comment> \<open>Path algebra chain: h\<circ>l \<simeq> \<alpha>*((k\<circ>l)*(rev \<alpha>)).\<close>
  \<comment> \<open>(1) Right-compose hprod_hom with rev \<alpha>.\<close>
  have pa1: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule path_homotopic_product_left[OF hTY hprod_hom hrev\<alpha>_path])
  \<comment> \<open>(2) Associativity: (h\<circ>l)*(\<alpha>*(rev\<alpha>)) \<simeq> ((h\<circ>l)*\<alpha>)*(rev\<alpha>).\<close>
  have pa2: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))"
    by (rule Theorem_51_2_associativity[OF hTY hhl_path h\<alpha>_path hrev\<alpha>_path])
  \<comment> \<open>(3) \<alpha>*(rev\<alpha>) \<simeq> const_{h(x0)}.\<close>
  have pa3: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)) (top1_constant_path (h x0))"
    by (rule Theorem_51_2_invgerse_left[OF hTY h\<alpha>_path])
  \<comment> \<open>(4) (h\<circ>l)*(\<alpha>*(rev\<alpha>)) \<simeq> (h\<circ>l)*const (right product).\<close>
  have pa4: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0)))"
    by (rule path_homotopic_product_right[OF hTY pa3 hhl_path])
  \<comment> \<open>(5) (h\<circ>l)*const \<simeq> h\<circ>l (right identity).\<close>
  have pa5: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0))) (h \<circ> l)"
    by (rule Theorem_51_2_right_identity[OF hTY hhl_path])
  \<comment> \<open>(6) Associativity on right: \<alpha>*((k\<circ>l)*(rev\<alpha>)) \<simeq> (\<alpha>*(k\<circ>l))*(rev\<alpha>).\<close>
  have pa6: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule Theorem_51_2_associativity[OF hTY h\<alpha>_path hkl_path hrev\<alpha>_path])
  \<comment> \<open>Chain by transitivity: h\<circ>l \<simeq> (h\<circ>l)*const (pa5 sym)
     \<simeq> (h\<circ>l)*(\<alpha>*(rev\<alpha>)) (pa4 sym) \<simeq> ((h\<circ>l)*\<alpha>)*(rev\<alpha>) (pa2)
     \<simeq> (\<alpha>*(k\<circ>l))*(rev\<alpha>) (pa1) \<simeq> \<alpha>*((k\<circ>l)*(rev\<alpha>)) (pa6 sym).\<close>
  have c1: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF pa5])
  have c2: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c1
          Lemma_51_1_path_homotopic_sym[OF pa4]])
  have c3: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c2 pa2])
  have c4: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c3 pa1])
  have c5: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c4
          Lemma_51_1_path_homotopic_sym[OF pa6]])
  \<comment> \<open>rev(rev \<alpha>) = \<alpha>, so target = \<alpha>*((k\<circ>l)*(rev \<alpha>)).\<close>
  have htarget_eq: "top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>) (k \<circ> l)
    = top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>))"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
  \<comment> \<open>The target is a loop (path from h(x0) to h(x0)).\<close>
  have hkl_rev\<alpha>_path: "top1_is_path_on Y TY (k x0) (h x0)
    (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>))"
    by (rule top1_path_product_is_path[OF hTY hkl_path hrev\<alpha>_path])
  have htarget_path: "top1_is_path_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))"
    by (rule top1_path_product_is_path[OF hTY h\<alpha>_path hkl_rev\<alpha>_path])
  have htarget_loop: "top1_is_loop_on Y TY (h x0)
    (top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>) (k \<circ> l))"
    unfolding top1_is_loop_on_def htarget_eq using htarget_path by blast
  show ?thesis unfolding top1_loop_equiv_on_def
    using hhl_loop htarget_loop c5[unfolded htarget_eq[symmetric]] by blast
qed


text \<open>Double basepoint change = single basepoint change along composed path.\<close>
lemma double_basepoint_change_equiv:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x1 x2 alpha"
      and hbeta: "top1_is_path_on X TX x0 x1 beta"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_loop_equiv_on X TX x2
    (top1_basepoint_change_on X TX x1 x2 alpha
      (top1_basepoint_change_on X TX x0 x1 beta f))
    (top1_basepoint_change_on X TX x0 x2
      (top1_path_product beta alpha) f)"
proof -
  let ?ra = "top1_path_reverse alpha" and ?rb = "top1_path_reverse beta"
  let ?ba = "top1_path_product beta alpha"
  let ?fp = "top1_is_path_on X TX"
  have hfp: "?fp x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hra: "?fp x2 x1 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
  have hrb: "?fp x1 x0 ?rb" by (rule top1_path_reverse_is_path[OF hbeta])
  have hba: "?fp x0 x2 ?ba" by (rule top1_path_product_is_path[OF hTX hbeta halpha])
  \<comment> \<open>rev(\<beta>*\<alpha>) = rev(\<alpha>) * rev(\<beta>) (definitional equality).\<close>
  have ha0: "alpha 0 = x1" and ha1: "alpha 1 = x2"
    using halpha unfolding top1_is_path_on_def by (by100 blast)+
  have hb0: "beta 0 = x0" and hb1: "beta 1 = x1"
    using hbeta unfolding top1_is_path_on_def by (by100 blast)+
  have hrev_prod: "top1_path_reverse ?ba = top1_path_product ?ra ?rb"
  proof (rule ext)
    fix s :: real
    show "top1_path_reverse ?ba s = top1_path_product ?ra ?rb s"
      unfolding top1_path_reverse_def top1_path_product_def
      using ha0 hb1 by (simp add: field_simps)
  qed
  \<comment> \<open>Unfold basepoint_change_on_def.\<close>
  have hlhs_eq: "top1_basepoint_change_on X TX x1 x2 alpha
      (top1_basepoint_change_on X TX x0 x1 beta f)
    = top1_path_product ?ra (top1_path_product
        (top1_path_product ?rb (top1_path_product f beta)) alpha)"
    unfolding top1_basepoint_change_on_def by (rule refl)
  have hrhs_eq: "top1_basepoint_change_on X TX x0 x2 ?ba f
    = top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba)"
    unfolding top1_basepoint_change_on_def hrev_prod by (rule refl)
  \<comment> \<open>Both sides are path-homotopic via repeated associativity:
     ra * ((rb * (f * \<beta>)) * \<alpha>) \<simeq> (ra * rb) * (f * (\<beta> * \<alpha>)).\<close>
  \<comment> \<open>Path facts for associativity.\<close>
  have hfb: "?fp x0 x1 (top1_path_product f beta)"
    by (rule top1_path_product_is_path[OF hTX hfp hbeta])
  have hfba: "?fp x0 x2 (top1_path_product f ?ba)"
    by (rule top1_path_product_is_path[OF hTX hfp hba])
  have hrb_fba: "?fp x1 x2 (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule top1_path_product_is_path[OF hTX hrb hfba])
  \<comment> \<open>Step 1: (rb*(f*\<beta>))*\<alpha> \<simeq> rb*((f*\<beta>)*\<alpha>) [sym of assoc].\<close>
  have s1: "top1_path_homotopic_on X TX x1 x2
    (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha)
    (top1_path_product ?rb (top1_path_product (top1_path_product f beta) alpha))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTX hrb hfb halpha]])
  \<comment> \<open>Step 2: (f*\<beta>)*\<alpha> \<simeq> f*(\<beta>*\<alpha>) [sym of assoc].\<close>
  have s2: "top1_path_homotopic_on X TX x0 x2
    (top1_path_product (top1_path_product f beta) alpha)
    (top1_path_product f ?ba)"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTX hfp hbeta halpha]])
  \<comment> \<open>Lift step 2 through rb: rb*((f*\<beta>)*\<alpha>) \<simeq> rb*(f*(\<beta>*\<alpha>)).\<close>
  have s2': "top1_path_homotopic_on X TX x1 x2
    (top1_path_product ?rb (top1_path_product (top1_path_product f beta) alpha))
    (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule path_homotopic_product_right[OF hTX s2 hrb])
  \<comment> \<open>Combine steps 1+2: (rb*(f*\<beta>))*\<alpha> \<simeq> rb*(f*ba).\<close>
  have s12: "top1_path_homotopic_on X TX x1 x2
    (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha)
    (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2'])
  \<comment> \<open>Lift s12 through ra: ra*((rb*(f*\<beta>))*\<alpha>) \<simeq> ra*(rb*(f*ba)).\<close>
  have s12': "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha))
    (top1_path_product ?ra (top1_path_product ?rb (top1_path_product f ?ba)))"
    by (rule path_homotopic_product_right[OF hTX s12 hra])
  \<comment> \<open>Step 3: ra*(rb*(f*ba)) \<simeq> (ra*rb)*(f*ba) [assoc].\<close>
  have s3: "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product ?rb (top1_path_product f ?ba)))
    (top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba))"
    by (rule Theorem_51_2_associativity[OF hTX hra hrb hfba])
  \<comment> \<open>Full chain: LHS \<simeq> RHS.\<close>
  have hchain: "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha))
    (top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s12' s3])
  have hbc_bf: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 beta f)"
    by (rule top1_basepoint_change_is_loop[OF hTX hbeta hf])
  have hlhs_loop: "top1_is_loop_on X TX x2
    (top1_basepoint_change_on X TX x1 x2 alpha (top1_basepoint_change_on X TX x0 x1 beta f))"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hbc_bf])
  have hrhs_loop: "top1_is_loop_on X TX x2
    (top1_basepoint_change_on X TX x0 x2 ?ba f)"
    by (rule top1_basepoint_change_is_loop[OF hTX hba hf])
  have hchain': "top1_path_homotopic_on X TX x2 x2
    (top1_basepoint_change_on X TX x1 x2 alpha (top1_basepoint_change_on X TX x0 x1 beta f))
    (top1_basepoint_change_on X TX x0 x2 ?ba f)"
    using hchain unfolding hlhs_eq hrhs_eq .
  show ?thesis unfolding top1_loop_equiv_on_def
    using hlhs_loop hrhs_loop hchain' by (by100 blast)
qed

section \<open>\<S>57 The Borsuk-Ulam Theorem\<close>

text \<open>Antipode-preserving map on the plane: h(-x) = -h(x) pointwise.\<close>
definition top1_antipode_preserving_S1 :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> bool" where
  "top1_antipode_preserving_S1 h \<longleftrightarrow>
     (\<forall>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y))))"

text \<open>General lemma: if g: S^1 \<rightarrow> S^1 is continuous, nulhomotopic, and g(1,0) = (1,0),
  then g \<circ> f \<simeq> const for every loop f at (1,0).\<close>
lemma nulhomotopic_trivializes_loops:
  assumes hg: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hgnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hg10: "g (1, 0) = (1::real, 0::real)"
      and hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
  shows "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      (g \<circ> f) (top1_constant_path (1, 0))"
proof -
  \<comment> \<open>From nulhomotopy, extract c and homotopy H. Apply homotopy_induced_basepoint_change
     to get g\<circ>f ≃ bc(rev(\<alpha>), const_c) at g(1,0) = (1,0), where \<alpha>(t) = H((1,0),t).
     Then show bc(rev(\<alpha>), const_c) ≃ const by path algebra.\<close>
  obtain c where hcS1: "c \<in> top1_S1"
      and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g (\<lambda>_. c)"
    using hgnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
      and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = g x"
      and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
            simplified]]) simp
  have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  have hH1': "\<forall>x\<in>top1_S1. H (x, 1) = (\<lambda>_. c) x" using hH1 by (by100 simp)
  note hbc = homotopy_induced_basepoint_change[OF hTS1 hTS1 hHcont hH0 hH1' hf h10S1]
  have hbc': "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0)) (g \<circ> f)
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))"
  proof -
    have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
      by (rule ext) (simp add: top1_constant_path_def comp_def)
    thus ?thesis using hbc by simp
  qed
  \<comment> \<open>From hbc', g \<circ> f ≃ bc(rev(\<alpha>), const_c) at g(1,0).
     Path algebra gives bc(rev(\<alpha>), const_c) ≃ const_{g(1,0)}:
       bc = \<alpha> * (const_c * rev(\<alpha>)), const_c * rev(\<alpha>) ≃ rev(\<alpha>) (left id),
       \<alpha> * rev(\<alpha>) ≃ const_{g(1,0)} (inverse).
     Same as the proof in hh_trivial_at_h10 (lines 9734-9790 of the True case).\<close>
  \<comment> \<open>Path algebra: show bc(rev(\<alpha>), const_c) ≃ const_{g(1,0)}, then chain with hbc'.\<close>
  let ?\<alpha> = "\<lambda>t. H ((1::real, 0::real), t)"
  have h\<alpha>_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?\<alpha>"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hp1: "pi1 \<circ> (\<lambda>t. ((1::real,0::real),t)) = (\<lambda>_. (1::real,0::real))"
      unfolding pi1_def by (rule ext) simp
    have hp2: "pi2 \<circ> (\<lambda>t. ((1::real,0::real),t)) = id"
      unfolding pi2_def by (rule ext) simp
    have hpair: "top1_continuous_map_on I_set I_top (top1_S1 \<times> I_set)
                   (product_topology_on top1_S1_topology I_top) (\<lambda>t. ((1::real, 0::real), t))"
      using iffD2[OF Theorem_18_4[OF hTI hTS1 hTI]]
            top1_continuous_map_on_const[OF hTI hTS1 h10S1, folded hp1]
            top1_continuous_map_on_id[OF hTI, folded hp2]
      by (by100 blast)
    show ?thesis using top1_continuous_map_on_comp[OF hpair hHcont] by (simp add: comp_def)
  qed
  have h\<alpha>_path: "top1_is_path_on top1_S1 top1_S1_topology (g (1, 0)) c ?\<alpha>"
    unfolding top1_is_path_on_def using h\<alpha>_cont
    by (auto simp: hH0[rule_format, OF h10S1] hH1[rule_format, OF h10S1])
  have hra: "top1_is_path_on top1_S1 top1_S1_topology c (g (1, 0)) (top1_path_reverse ?\<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
  have hconst_c: "top1_is_loop_on top1_S1 top1_S1_topology c (top1_constant_path c)"
    by (rule top1_constant_path_is_loop[OF hTS1 hcS1])
  have hbc_def: "top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
      (top1_path_reverse ?\<alpha>) (top1_constant_path c)
    = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
  have hchain: "top1_path_homotopic_on top1_S1 top1_S1_topology (g (1, 0)) (g (1, 0))
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g (1, 0)))"
    using Lemma_51_1_path_homotopic_trans[OF hTS1
        path_homotopic_product_right[OF hTS1 Theorem_51_2_left_identity[OF hTS1 hra] h\<alpha>_path,
          unfolded hbc_def[symmetric]]
        Theorem_51_2_invgerse_left[OF hTS1 h\<alpha>_path]] .
  have hbc_is_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0))
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g (1, 0)))"
  proof -
    have hg10_S1: "g (1, 0) \<in> top1_S1"
      using hg h10S1 unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_loop_equiv_on_def
      using top1_basepoint_change_is_loop[OF hTS1 hra hconst_c]
            top1_constant_path_is_loop[OF hTS1 hg10_S1]
            hchain by (by100 blast)
  qed
  have hresult: "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0)) (g \<circ> f)
      (top1_constant_path (g (1, 0)))"
    by (rule top1_loop_equiv_on_trans[OF hTS1 hbc' hbc_is_const])
  have "top1_path_homotopic_on top1_S1 top1_S1_topology (g (1, 0)) (g (1, 0))
      (g \<circ> f) (top1_constant_path (g (1, 0)))"
    using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  thus ?thesis using hg10 by simp
qed

(** from *\<S>57 Theorem 57.1: antipode-preserving S^1 \<rightarrow> S^1 is NOT nulhomotopic.

    Munkres' proof:
    Step 1: WLOG h(b_0) = b_0 (rotate). Let q: S^1 \<rightarrow> S^1 be q(z) = z^2 (quotient
            map). q is a covering map and its fibers are antipodal pairs {z, -z}.
            Since h(-z) = -h(z), we have q(h(-z)) = q(h(z)), so q\<circ>h factors as
            k\<circ>q for some continuous k: S^1 \<rightarrow> S^1.
    Step 2: k_* is nontrivial. If \<tilde>f is any path in S^1 from b_0 to -b_0, the
            loop f = q\<circ>\<tilde>f represents a nontrivial element of \<pi>_1(S^1). For \<tilde>f is
            a lifting of f, starting at b_0 but not ending at b_0.
            Hence k_*[f] = [k\<circ>(q\<circ>\<tilde>f)] = [q\<circ>(h\<circ>\<tilde>f)] is also nontrivial.
    Step 3: k_* injective; q_* injective (multiplication by 2 in Z). So k_*\<circ>q_*
            is injective. Since q_*\<circ>h_* = k_*\<circ>q_*, h_* is injective, hence
            nontrivial, hence h is not nulhomotopic. **)
theorem Theorem_57_1:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and "top1_antipode_preserving_S1 h"
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
  \<comment> \<open>Step 1: q(z)=z^2 is a covering map. h(-z)=-h(z) \<Rightarrow> q\<circ>h = k\<circ>q for some k.\<close>
  let ?q = "\<lambda>(x, y). (x^2 - y^2, 2*x*y)"
  have hq_cover: "top1_covering_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology ?q" sorry
  obtain k where hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology k"
      and hk_eq: "\<forall>z\<in>top1_S1. k (?q z) = ?q (h z)"
    sorry
  \<comment> \<open>Step 2: k_* is nontrivial. A path from b0 to -b0 in S^1 lifts to a nontrivial loop under q,
     and k maps this to another nontrivial element.\<close>
  have hk_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (k \<circ> f) (top1_constant_path (1, 0)))" sorry
  \<comment> \<open>Step 3: q_* is multiplication by 2, hence injective. k_*\<circ>q_* injective.
     q_*\<circ>h_* = k_*\<circ>q_* \<Rightarrow> h_* injective \<Rightarrow> nontrivial \<Rightarrow> h not nulhomotopic.\<close>
  have hq_star_inj: "\<forall>f g. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<and> top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g
      \<and> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
           (?q \<circ> f) (?q \<circ> g)
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g" sorry
  \<comment> \<open>WLOG: reduce to h(1,0) = (1,0) by rotation. Munkres: let \<rho> rotate h(b0) to b0.\<close>
  \<comment> \<open>Case 1: h(1,0) = (1,0). Then h_* at (1,0) is nontrivial (from covering theory),
     but nulhomotopic \<Rightarrow> h_* trivial. Contradiction.\<close>
  \<comment> \<open>Case 2: h(1,0) \<noteq> (1,0). Rotate to reduce to Case 1.\<close>
  \<comment> \<open>Derive contradiction via case split on h(1,0) = (1,0).\<close>
  have hh_star_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (h \<circ> f) (top1_constant_path (1, 0)))" sorry
  \<comment> \<open>Helper: for any loop f at (1,0), h\<circ>f \<simeq> const_{h(1,0)} at h(1,0).
     This is proved via homotopy_induced_basepoint_change + path algebra.\<close>
  have hh_trivial_at_h10: "\<And>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f \<Longrightarrow>
      top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (h \<circ> f) (top1_constant_path (h (1, 0)))"
  proof -
    fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
    obtain c where hcS1: "c \<in> top1_S1"
        and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
      using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
    obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
        and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
        and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
      using hhom unfolding top1_homotopic_on_def by (by100 blast)
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
              simplified]]) simp
    have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hH1': "\<forall>x\<in>top1_S1. H (x, 1) = (\<lambda>_. c) x" using hH1 by (by100 simp)
    note hbc = homotopy_induced_basepoint_change[OF hTS1 hTS1 hHcont hH0 hH1' hf h10S1]
    have hbc': "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))"
    proof -
      have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
        by (rule ext) (simp add: top1_constant_path_def comp_def)
      thus ?thesis using hbc by simp
    qed
    have hbc_is_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0))
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))
        (top1_constant_path (h (1, 0)))"
    proof -
      let ?\<alpha> = "\<lambda>t. H ((1::real, 0::real), t)"
      have h\<alpha>_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?\<alpha>"
      proof -
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hp1: "pi1 \<circ> (\<lambda>t. ((1::real,0::real),t)) = (\<lambda>_. (1::real,0::real))"
          unfolding pi1_def by (rule ext) simp
        have hp2: "pi2 \<circ> (\<lambda>t. ((1::real,0::real),t)) = id"
          unfolding pi2_def by (rule ext) simp
        have hpair: "top1_continuous_map_on I_set I_top (top1_S1 \<times> I_set)
                       (product_topology_on top1_S1_topology I_top) (\<lambda>t. ((1::real, 0::real), t))"
          using iffD2[OF Theorem_18_4[OF hTI hTS1 hTI]]
                top1_continuous_map_on_const[OF hTI hTS1 h10S1, folded hp1]
                top1_continuous_map_on_id[OF hTI, folded hp2]
          by (by100 blast)
        show ?thesis using top1_continuous_map_on_comp[OF hpair hHcont] by (simp add: comp_def)
      qed
      have h\<alpha>_path: "top1_is_path_on top1_S1 top1_S1_topology (h (1, 0)) c ?\<alpha>"
        unfolding top1_is_path_on_def using h\<alpha>_cont
        by (auto simp: hH0[rule_format, OF h10S1] hH1[rule_format, OF h10S1])
      have hra: "top1_is_path_on top1_S1 top1_S1_topology c (h (1, 0)) (top1_path_reverse ?\<alpha>)"
        by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
      have hconst_c: "top1_is_loop_on top1_S1 top1_S1_topology c (top1_constant_path c)"
        by (rule top1_constant_path_is_loop[OF hTS1 hcS1])
      have hbc_def: "top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
          (top1_path_reverse ?\<alpha>) (top1_constant_path c)
        = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
        unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
      have hchain: "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
             (top1_path_reverse ?\<alpha>) (top1_constant_path c))
          (top1_constant_path (h (1, 0)))"
        using Lemma_51_1_path_homotopic_trans[OF hTS1
            path_homotopic_product_right[OF hTS1 Theorem_51_2_left_identity[OF hTS1 hra] h\<alpha>_path,
              unfolded hbc_def[symmetric]]
            Theorem_51_2_invgerse_left[OF hTS1 h\<alpha>_path]] .
      have hh10S1: "h (1, 0) \<in> top1_S1"
        using assms(1) h10S1 unfolding top1_continuous_map_on_def by (by100 blast)
      show ?thesis unfolding top1_loop_equiv_on_def
        using top1_basepoint_change_is_loop[OF hTS1 hra hconst_c]
              top1_constant_path_is_loop[OF hTS1 hh10S1]
              hchain by (by100 blast)
    qed
    have hresult: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_constant_path (h (1, 0)))"
      by (rule top1_loop_equiv_on_trans[OF hTS1 hbc' hbc_is_const])
    show "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
        (h \<circ> f) (top1_constant_path (h (1, 0)))"
      using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  qed
  \<comment> \<open>Case split: h(1,0) = (1,0) gives direct contradiction;
     h(1,0) \<noteq> (1,0) needs WLOG rotation.\<close>
  show False
  proof (cases "h (1, 0) = (1::real, 0::real)")
    case True
    have "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0))"
      using hh_trivial_at_h10 True by simp
    thus False using hh_star_nontrivial by blast
  next
    case False
    \<comment> \<open>h(1,0) \<noteq> (1,0): WLOG rotation. Let \<rho> rotate h(1,0) to (1,0).\<close>
    \<comment> \<open>h(1,0) \<in> S^1, so h(1,0) = (cos \<theta>, sin \<theta>) for some \<theta>.
       Rotation by -\<theta>: \<rho>(x,y) = (x cos\<theta> + y sin\<theta>, -x sin\<theta> + y cos\<theta>).
       Then \<rho>(h(1,0)) = (cos^2\<theta> + sin^2\<theta>, 0) = (1,0).\<close>
    have h10_S1: "(1::real,0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hh10: "h (1,0) \<in> top1_S1"
      using assms(1) h10_S1 unfolding top1_continuous_map_on_def by (by100 blast)
    let ?a = "fst (h (1, 0))" and ?b = "snd (h (1, 0))"
    have hab_S1: "?a^2 + ?b^2 = 1" using hh10 unfolding top1_S1_def by (by100 auto)
    \<comment> \<open>Define rotation \<rho>(x,y) = (ax+by, -bx+ay).\<close>
    let ?\<rho> = "\<lambda>(x::real,y::real). (?a*x + ?b*y, -?b*x + ?a*y)"
    have hrho_10: "?\<rho> (h (1,0)) = (1, 0)"
      using hab_S1 by (simp add: prod_eq_iff case_prod_beta power2_eq_square algebra_simps)
    \<comment> \<open>\<rho> commutes with negation: \<rho>(-x,-y) = -\<rho>(x,y).\<close>
    have hrho_neg: "\<And>x y. ?\<rho> (-x,-y) = (- fst (?\<rho> (x,y)), - snd (?\<rho> (x,y)))"
      by (by100 simp)
    \<comment> \<open>\<rho>\<circ>h is continuous, antipode-preserving, nulhomotopic.\<close>
    have "?\<rho> \<circ> h = (\<lambda>z. ?\<rho> (h z))" by (rule ext) (by100 simp)
    \<comment> \<open>\<rho> maps S^1 to S^1 and is continuous.\<close>
    have hrho_S1: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?\<rho> p \<in> top1_S1"
    proof -
      fix p assume hp: "p \<in> top1_S1"
      have hxy: "(fst p)^2 + (snd p)^2 = 1" using hp unfolding top1_S1_def by (by100 auto)
      have "(?a * fst p + ?b * snd p)^2 + (-?b * fst p + ?a * snd p)^2
          = (?a^2 + ?b^2) * ((fst p)^2 + (snd p)^2)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = 1" using hab_S1 hxy by (by100 simp)
      finally show "?\<rho> p \<in> top1_S1" unfolding top1_S1_def by (simp add: case_prod_beta)
    qed
    have hrho_cont_univ: "continuous_on UNIV ?\<rho>"
    proof -
      have "continuous_on UNIV (\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_minus continuous_on_const continuous_on_fst continuous_on_snd continuous_on_id)
      moreover have "(\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p)) = ?\<rho>"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by (by100 metis)
    qed
    have hrho_top1: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?\<rho>"
    proof -
      have "top1_continuous_map_on top1_S1
          (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1)
          top1_S1 (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1) ?\<rho>"
        using top1_continuous_map_on_subspace_open_sets[OF hrho_S1 hrho_cont_univ]
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
      thus ?thesis unfolding top1_S1_topology_def
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
    qed
    have hrh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF assms(1) hrho_top1])
    have hrh_anti: "top1_antipode_preserving_S1 (?\<rho> \<circ> h)"
      unfolding top1_antipode_preserving_S1_def
    proof (intro allI)
      fix x y
      have "h (-x, -y) = (- fst (h (x,y)), - snd (h (x,y)))"
        using assms(2) unfolding top1_antipode_preserving_S1_def by (by100 blast)
      thus "(?\<rho> \<circ> h) (-x, -y) = (- fst ((?\<rho> \<circ> h) (x, y)), - snd ((?\<rho> \<circ> h) (x, y)))"
        by (simp add: comp_def case_prod_beta algebra_simps)
    qed
    have hrh_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
    proof -
      obtain c where hc: "c \<in> top1_S1"
          and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
        using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
      have hrhc_S1: "?\<rho> c \<in> top1_S1"
        using hrho_S1[OF hc] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      \<comment> \<open>Extract homotopy H from hhom, compose with \<rho>.\<close>
      obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
          and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
          and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
        using hhom unfolding top1_homotopic_on_def by (by100 blast)
      have hrH_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology (?\<rho> \<circ> H)"
        by (rule top1_continuous_map_on_comp[OF hHcont hrho_top1])
      have hconst_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>_. ?\<rho> c)"
        by (rule top1_continuous_map_on_const[OF hTS1 hTS1 hrhc_S1])
      have hrhH0: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 0) = (?\<rho> \<circ> h) x"
        using hH0 by (by100 simp)
      have hrhH1: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 1) = ?\<rho> c"
        using hH1 by (by100 simp)
      have "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
          (?\<rho> \<circ> h) (\<lambda>_. ?\<rho> c)"
        unfolding top1_homotopic_on_def
        apply (intro conjI exI[of _ "?\<rho> \<circ> H"])
        apply (rule hrh_cont)
        apply (rule hconst_cont)
        apply (rule hrH_cont)
        using hrhH0 apply (by100 simp)
        using hrhH1 apply (by100 simp)
        done
      thus ?thesis unfolding top1_nulhomotopic_on_def using hrhc_S1 by (by100 blast)
    qed
    have hrh_10: "(?\<rho> \<circ> h) (1, 0) = (1, 0)"
      using hrho_10 by (by100 simp)
    \<comment> \<open>Apply the same argument as the True case to \<rho>\<circ>h.\<close>
    \<comment> \<open>Step 1: (\<rho>\<circ>h)\<circ>f \<simeq> const for all loops f at (1,0) — from nulhomotopy + basepoint change.\<close>
    have hrh_trivial: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
    proof (intro allI impI)
      fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
      show "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
        by (rule nulhomotopic_trivializes_loops[OF hrh_cont hrh_nul hrh_10 hf])
    qed
    \<comment> \<open>Step 2: (\<rho>\<circ>h)_* is nontrivial (covering theory: antipode-preserving \<Rightarrow> induced map \<times>2).\<close>
    have hrh_star_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0)))"
      using hrh_cont hrh_anti hrh_10 sorry
    show False using hrh_trivial hrh_star_nontrivial by (by100 blast)
  qed
qed

(** from *\<S>57 Theorem 57.2: no continuous antipode-preserving S^2 \<rightarrow> S^1.
    Munkres' proof: if g: S^2 \<rightarrow> S^1 is antipode-preserving, then h = g|S^1
    (equator) is antipode-preserving S^1 \<rightarrow> S^1, not nulhomotopic by 57.1.
    But g extends h over the upper hemisphere \<cong> B^2, so h IS nulhomotopic.
    Contradiction.

    (Stated as part of Theorem 57.3 below using an inline S^2 set, since
     top1_S2 is defined later in the file.) **)

(** from *\<S>57 Theorem 57.3: Borsuk-Ulam theorem for S^2.
    Munkres' proof: by contradiction. If f(x) \<ne> f(-x) for all x \<in> S^2, then
    g(x) = (f(x) - f(-x))/||f(x) - f(-x)|| is continuous antipode-preserving
    S^2 \<rightarrow> S^1, contradicting Theorem 57.2. **)
theorem Theorem_57_3_BorsukUlam:
  fixes f :: "real \<times> real \<times> real \<Rightarrow> real \<times> real"
  assumes hf: "top1_continuous_map_on {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}
    (subspace_topology UNIV
      (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets))
      {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1})
    UNIV (product_topology_on top1_open_sets top1_open_sets) f"
  shows "\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x))"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x)))"
  \<comment> \<open>By assumption, f(x) \<noteq> f(-x) for all x \<in> S^2.\<close>
  let ?S2 = "{p::real\<times>real\<times>real. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"
  let ?neg = "\<lambda>x::real\<times>real\<times>real. (- fst x, - fst (snd x), - snd (snd x))"
  have hfne: "\<forall>x\<in>?S2. f x \<noteq> f (?neg x)" using hno by blast
  \<comment> \<open>Define g: S^2 \<rightarrow> S^1 by g(x) = (f(x) - f(-x)) / ||f(x) - f(-x)||.\<close>
  let ?diff = "\<lambda>x. (fst (f x) - fst (f (?neg x)), snd (f x) - snd (f (?neg x)))"
  let ?norm = "\<lambda>x. sqrt ((fst (?diff x))^2 + (snd (?diff x))^2)"
  let ?g = "\<lambda>x. (fst (?diff x) / ?norm x, snd (?diff x) / ?norm x)"
  \<comment> \<open>g is continuous (rational functions with nonzero denominator).\<close>
  have hg_cont: "top1_continuous_map_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  \<comment> \<open>g is antipode-preserving: g(-x) = -g(x).\<close>
  have hg_anti: "\<forall>x\<in>?S2. ?g (?neg x) = (- fst (?g x), - snd (?g x))"
  proof (intro ballI)
    fix x :: "real \<times> real \<times> real" assume hx: "x \<in> ?S2"
    have hnegneg: "?neg (?neg x) = x" by (simp add: prod_eq_iff)
    have h1: "fst (?diff (?neg x)) = - fst (?diff x)" by (simp add: hnegneg)
    have h2: "snd (?diff (?neg x)) = - snd (?diff x)" by (simp add: hnegneg)
    have hpc1: "(fst (f (?neg x)) - fst (f x))\<^sup>2 = (fst (f x) - fst (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have hpc2: "(snd (f (?neg x)) - snd (f x))\<^sup>2 = (snd (f x) - snd (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have h3: "?norm (?neg x) = ?norm x" by (simp add: hnegneg hpc1 hpc2)
    have hd1: "fst (f (?neg x)) - fst (f x) = - (fst (f x) - fst (f (?neg x)))"
      by (by100 linarith)
    have hd2: "snd (f (?neg x)) - snd (f x) = - (snd (f x) - snd (f (?neg x)))"
      by (by100 linarith)
    show "?g (?neg x) = (- fst (?g x), - snd (?g x))"
      by (simp del: minus_diff_eq add: prod_eq_iff hnegneg h3 hd1 hd2)
  qed
  \<comment> \<open>Restrict g to the equator S^1: h = g|_{S^1}. h is antipode-preserving S^1 \<rightarrow> S^1.\<close>
  \<comment> \<open>By Theorem 57.1, h is not nulhomotopic. But g extends h over the upper hemisphere
     which is homeomorphic to B^2, so h is nulhomotopic. Contradiction.\<close>
  have hg_not_nulhomo: "\<not> top1_nulhomotopic_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  have hg_nulhomo: "top1_nulhomotopic_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g" sorry
  show False using hg_not_nulhomo hg_nulhomo by contradiction
qed


section \<open>\<S>58 Deformation Retracts and Homotopy Type\<close>

text \<open>A is a deformation retract of X: the identity map of X is homotopic
  to a map that carries all of X into A, with A fixed during the homotopy.\<close>
definition top1_deformation_retract_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_deformation_retract_of_on X TX A \<longleftrightarrow>
     A \<subseteq> X \<and>
     (\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
          \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A)
          \<and> (\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a))"

text \<open>Homotopy equivalence: f: X\<rightarrow>Y and g: Y\<rightarrow>X with g\<circ>f \<simeq> id_X and f\<circ>g \<simeq> id_Y.\<close>
definition top1_homotopy_equivalence_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_homotopy_equivalence_on X TX Y TY f g \<longleftrightarrow>
     top1_continuous_map_on X TX Y TY f \<and>
     top1_continuous_map_on Y TY X TX g \<and>
     top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x) \<and>
     top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"

text \<open>Spaces have the same homotopy type if there is a homotopy equivalence between them.\<close>
definition top1_same_homotopy_type_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "top1_same_homotopy_type_on X TX Y TY \<longleftrightarrow>
     (\<exists>f g. top1_homotopy_equivalence_on X TX Y TY f g)"

text \<open>Homotopy equivalence is symmetric (swap f and g).\<close>
lemma top1_homotopy_equivalence_on_sym:
  assumes "top1_homotopy_equivalence_on X TX Y TY f g"
  shows "top1_homotopy_equivalence_on Y TY X TX g f"
  using assms unfolding top1_homotopy_equivalence_on_def by blast

text \<open>Same homotopy type is symmetric.\<close>
lemma top1_same_homotopy_type_on_sym:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  using assms top1_homotopy_equivalence_on_sym
  unfolding top1_same_homotopy_type_on_def by blast

(** from \<S>58 Lemma 58.1: if h, k: (X, x_0) \<rightarrow> (Y, y_0) are homotopic with basepoint
    fixed during the homotopy, then h_* = k_* on fundamental groups. **)
lemma Lemma_58_1_basepoint_fixed:
  assumes hTX: "is_topology_on X TX"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hk: "top1_continuous_map_on X TX Y TY k"
      and hhx0: "h x0 = y0" and hkx0: "k x0 = y0"
      and hH: "\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H
              \<and> (\<forall>x\<in>X. H (x, 0) = h x) \<and> (\<forall>x\<in>X. H (x, 1) = k x)
              \<and> (\<forall>t\<in>I_set. H (x0, t) = y0)"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0
           (top1_induced_homomorphism_on X TX Y TY h f)
           (top1_induced_homomorphism_on X TX Y TY k f)"
proof -
  obtain H where hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = h x" and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHbase: "\<forall>t\<in>I_set. H (x0, t) = y0"
    using hH by blast
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hf_vals: "\<forall>s\<in>I_set. f s \<in> X"
    using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" and hf1: "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  \<comment> \<open>Continuity of (s,t) \<mapsto> (f s, t) : I \<times> I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hid_II': "top1_continuous_map_on (I_set \<times> I_set) II_topology
                  (I_set \<times> I_set) (product_topology_on I_top I_top) id"
    using top1_continuous_map_on_id[OF hTII] unfolding II_topology_def .
  have hpi1_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hpi2_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi2 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hfpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1_II hfcont])
  \<comment> \<open>Build (\<lambda>(s,t). (f s, t)) via Theorem_18_4.\<close>
  have hpi1_pair: "(pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = f \<circ> pi1"
    unfolding pi1_def by (rule ext) simp
  have hpi2_pair: "(pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = pi2"
    unfolding pi2_def by (rule ext) simp
  have hpi1_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
                         (pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hfpi1 unfolding hpi1_pair .
  have hpi2_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top
                         (pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hpi2_II unfolding hpi2_pair .
  have hpair: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                 (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>p::real\<times>real. (f (fst p), snd p))"
    using iffD2[OF Theorem_18_4[OF hTII hTX hTI]] hpi1_pair_cont hpi2_pair_cont
    unfolding II_topology_def by blast
  \<comment> \<open>Composition: F(s,t) = H(f s, t).\<close>
  let ?F = "\<lambda>p::real\<times>real. H (f (fst p), snd p)"
  have hFcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY
                 (H \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?F"
    using hFcomp by (simp add: comp_def)
  \<comment> \<open>Boundary values.\<close>
  have h_hf_path: "top1_is_path_on Y TY y0 y0 (h \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hh])
  next
    show "(h \<circ> f) 0 = y0" using hf0 hhx0 by (simp add: comp_def)
  next
    show "(h \<circ> f) 1 = y0" using hf1 hhx0 by (simp add: comp_def)
  qed
  have h_kf_path: "top1_is_path_on Y TY y0 y0 (k \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (k \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hk])
  next
    show "(k \<circ> f) 0 = y0" using hf0 hkx0 by (simp add: comp_def)
  next
    show "(k \<circ> f) 1 = y0" using hf1 hkx0 by (simp add: comp_def)
  qed
  have hFs0: "\<forall>s\<in>I_set. ?F (s, 0) = (h \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 0) = h (f s)" using hH0 by blast
    thus "?F (s, 0) = (h \<circ> f) s" by (simp add: comp_def)
  qed
  have hFs1: "\<forall>s\<in>I_set. ?F (s, 1) = (k \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 1) = k (f s)" using hH1 by blast
    thus "?F (s, 1) = (k \<circ> f) s" by (simp add: comp_def)
  qed
  have hF0t: "\<forall>t\<in>I_set. ?F (0, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 0 = x0" by (rule hf0)
    hence "?F (0, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (0, t) = y0" .
  qed
  have hF1t: "\<forall>t\<in>I_set. ?F (1, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 1 = x0" by (rule hf1)
    hence "?F (1, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (1, t) = y0" .
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def top1_induced_homomorphism_on_def
    using h_hf_path h_kf_path hFcont hFs0 hFs1 hF0t hF1t by blast
qed

(** from \<S>58 Lemma 58.5: if A \<subseteq> X, H : X\<times>I \<rightarrow> X is a homotopy from id_X
    to some map k : X \<rightarrow> X with H(a, t) \<in> A for all a \<in> A and t \<in> I,
    and \<alpha>(t) = H(x_0, t) is the "base-tracking" path from x_0 to k(x_0),
    then the basepoint-change \<alpha>\<^sup>\<hat> commutes with the induced map on \<pi>_1. **)
lemma Lemma_58_5_basepoint_change:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and H :: "'a \<times> real \<Rightarrow> 'a" and k :: "'a \<Rightarrow> 'a" and x0 :: 'a
  assumes hTX: "is_topology_on_strict X TX"
      and hAsub: "A \<subseteq> X"
      and hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x"
      and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) \<in> A"
      and hx0A: "x0 \<in> A"
  shows "top1_is_path_on X TX x0 (k x0) (\<lambda>t. H (x0, t))"
proof -
  have hx0X: "x0 \<in> X" using hx0A hAsub by blast
  have hTX': "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF hTX])
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX' hTI])
  \<comment> \<open>Continuity of t \<mapsto> (x_0, t) : I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hconst_x0: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
    by (rule top1_continuous_map_on_const[OF hTI hTX' hx0X])
  have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top X TX (pi1 \<circ> (\<lambda>t. (x0, t)))"
    using hconst_x0 unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>t. (x0, t)))"
    using hid_I unfolding hpi2_eq .
  have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>t. (x0, t))"
    using iffD2[OF Theorem_18_4[OF hTI hTX' hTI]] hpi1_cont hpi2_cont by blast
  \<comment> \<open>Composition H \<circ> (\<lambda>t. (x_0, t)) : I \<rightarrow> X is continuous.\<close>
  have hcomp: "top1_continuous_map_on I_set I_top X TX (H \<circ> (\<lambda>t. (x0, t)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hcont: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H (x0, t))"
    using hcomp by (simp add: comp_def)
  \<comment> \<open>Endpoints: H(x_0, 0) = x_0 and H(x_0, 1) = k x_0.\<close>
  have hstart: "H (x0, 0) = x0" using hH0 hx0X by blast
  have hend: "H (x0, 1) = k x0" using hH1 hx0X by blast
  show ?thesis
    unfolding top1_is_path_on_def
    using hcont hstart hend by simp
qed

(** from \<S>58 Theorem 58.7: a homotopy equivalence induces an isomorphism of fundamental groups.
    The strict version is trivially related.

    Munkres' proof (sketch):
    Given f and g as homotopy invgerses, Lemma 58.1 gives that (g o f)_* equals id_*
    and (f o g)_* equals id_*, so f_* and g_* are mutual invgerses in a suitable sense.
    Hence f_* is a bijection onto pi_1(Y, f x_0). **)
text \<open>Helper: continuous f: X \<rightarrow> Y preserves path homotopy.\<close>
lemma top1_continuous_preserves_path_homotopy:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_path_homotopic_on X TX x0 x0 l l'"
  shows "top1_path_homotopic_on Y TY (f x0) (f x0) (f \<circ> l) (f \<circ> l')"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = l s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = l' s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x0" and hF1: "\<forall>t\<in>I_set. F (1, t) = x0"
    using hll' unfolding top1_path_homotopic_on_def by blast
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  let ?G = "f \<circ> F"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?G"
    by (rule top1_continuous_map_on_comp[OF hF hf])
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using hl unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hl'0: "l' 0 = x0" and hl'1: "l' 1 = x0"
    using hl' unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hfl_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l)"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl] hf]
    by (simp add: comp_def hl0 hl1)
  have hfl'_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l')"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl'] hf]
    by (simp add: comp_def hl'0 hl'1)
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hfl_path hfl'_path hGcont hFs0 hFs1 hF0 hF1
    by (auto simp: comp_def)
qed

text \<open>Helper: continuous f sends loops to loops.\<close>
lemma top1_continuous_map_loop:
  assumes "top1_continuous_map_on X TX Y TY f"
      and "top1_is_loop_on X TX x0 l"
  shows "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
proof -
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using assms(2) unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  show ?thesis
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF assms(2)] assms(1)]
    by (simp add: comp_def hl0 hl1)
qed

text \<open>Helper: f_* sends loops at x0 to loops at f(x0), preserving loop equiv.\<close>
lemma top1_induced_preserves_loop_equiv:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_loop_equiv_on X TX x0 l l'"
  shows "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
  unfolding top1_loop_equiv_on_def
  using top1_continuous_map_loop[OF hf hl] top1_continuous_map_loop[OF hf hl']
        top1_continuous_preserves_path_homotopy[OF hTX hf hl hl']
  using hll' unfolding top1_loop_equiv_on_def by blast

theorem Theorem_58_7:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and heq: "top1_homotopy_equivalence_on X TX Y TY f g" and hx0: "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
proof -
  have hf: "top1_continuous_map_on X TX Y TY f"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  have hg: "top1_continuous_map_on Y TY X TX g"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  \<comment> \<open>Define f_* on equivalence classes.\<close>
  let ?f_star = "\<lambda>c. {h. \<exists>l\<in>c. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  \<comment> \<open>f_* maps carrier to carrier (well-definedness).\<close>
  have hfstar_class: "\<And>l. top1_is_loop_on X TX x0 l \<Longrightarrow>
    ?f_star {h. top1_loop_equiv_on X TX x0 l h} =
    {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  proof (intro set_eqI iffI)
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
    then obtain l' where hl': "top1_loop_equiv_on X TX x0 l l'"
        and hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l') h" by blast
    have hl'_loop: "top1_is_loop_on X TX x0 l'" using hl' unfolding top1_loop_equiv_on_def by blast
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
      by (rule top1_induced_preserves_loop_equiv[OF hTX hf hl hl'_loop hl'])
    show "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      using top1_loop_equiv_on_trans[OF hTY hfl_equiv hh] by simp
  next
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    hence hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h" by simp
    have "l \<in> {h. top1_loop_equiv_on X TX x0 l h}"
      using top1_loop_equiv_on_refl[OF hl] by simp
    thus "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
      using hh by blast
  qed
  have hfstar_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain l where hl: "top1_is_loop_on X TX x0 l"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 l h}"
      unfolding top1_fundamental_group_carrier_def by blast
    have "?f_star c = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      unfolding hc by (rule hfstar_class[OF hl])
    moreover have "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
      by (rule top1_continuous_map_loop[OF hf hl])
    ultimately show "?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
      unfolding top1_fundamental_group_carrier_def by blast
  qed
  \<comment> \<open>Pointwise: f \<circ> (l1 * l2) = (f \<circ> l1) * (f \<circ> l2).\<close>
  have hf_comp_product: "\<And>l1 l2. f \<circ> top1_path_product l1 l2 = top1_path_product (f \<circ> l1) (f \<circ> l2)"
    unfolding top1_path_product_def comp_def by (rule ext) auto
  \<comment> \<open>f_* is a homomorphism.\<close>
  have hfstar_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {h. top1_loop_equiv_on X TX x0 l1 h}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on X TX x0 l2 h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hl12: "top1_is_loop_on X TX x0 (top1_path_product l1 l2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hl1 hl2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    \<comment> \<open>LHS: f_*(mul c1 c2) = f_*(class(l1*l2)) = class(f\<circ>(l1*l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product l1 l2) h}"
      unfolding hc1_eq hc2_eq by (rule top1_fundamental_group_mul_class[OF hTX hl1 hl2])
    have hLHS: "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_path_product l1 l2) h}"
      unfolding hmul_eq by (rule hfstar_class[OF hl12])
    have hLHS': "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hLHS hf_comp_product ..
    \<comment> \<open>RHS: mul(f_*(c1), f_*(c2)) = mul(class(f\<circ>l1), class(f\<circ>l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hfc1: "?f_star c1 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
      unfolding hc1_eq by (rule hfstar_class[OF hl1])
    have hfc2: "?f_star c2 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
      unfolding hc2_eq by (rule hfstar_class[OF hl2])
    have hfl1: "top1_is_loop_on Y TY (f x0) (f \<circ> l1)"
      by (rule top1_continuous_map_loop[OF hf hl1])
    have hfl2: "top1_is_loop_on Y TY (f x0) (f \<circ> l2)"
      by (rule top1_continuous_map_loop[OF hf hl2])
    have hRHS: "top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hfc1 hfc2 by (rule top1_fundamental_group_mul_class[OF hTY hfl1 hfl2])
    show "?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
      unfolding hLHS' hRHS ..
  qed
  \<comment> \<open>f_* is bijective.
     Injectivity: g_* \<circ> f_* is related to basepoint change (iso).
     Surjectivity: f_* \<circ> g_* is related to basepoint change (iso).\<close>
  have hgof: "top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  have hfog: "top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  \<comment> \<open>Injectivity of f_*: g_*\<circ>f_* = basepoint change (iso), so f_* injective.\<close>
  obtain H1 where hH1cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H1"
      and hH10: "\<forall>x\<in>X. H1 (x, 0) = (g \<circ> f) x" and hH11: "\<forall>x\<in>X. H1 (x, 1) = x"
    using hgof unfolding top1_homotopic_on_def id_def by blast
  let ?\<alpha>1 = "\<lambda>t. H1 (x0, t)"
  have hfstar_inj: "inj_on ?f_star (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq_fs: "?f_star c1 = ?f_star c2"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 l1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 l2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    \<comment> \<open>f_*(c1)=f_*(c2) \<Rightarrow> f\<circ>l1 \<simeq> f\<circ>l2 at f(x0).\<close>
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) (f \<circ> l2)"
    proof -
      have "{h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
        using heq_fs
        unfolding hc1_eq hc2_eq hfstar_class[OF hl1] hfstar_class[OF hl2] .
      moreover have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
        using top1_loop_equiv_on_refl[OF top1_continuous_map_loop[OF hf hl1]] by simp
      ultimately have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}" by simp
      hence "top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) (f \<circ> l1)" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply g: g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 at g(f(x0)).\<close>
    have hgfl_equiv: "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> f \<circ> l1) (g \<circ> f \<circ> l2)"
    proof -
      have "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> (f \<circ> l1)) (g \<circ> (f \<circ> l2))"
        by (rule top1_induced_preserves_loop_equiv[OF hTY hg
            top1_continuous_map_loop[OF hf hl1]
            top1_continuous_map_loop[OF hf hl2] hfl_equiv])
      thus ?thesis by (simp add: comp_assoc)
    qed
    \<comment> \<open>By homotopy_induced_basepoint_change: g\<circ>f\<circ>li \<simeq> bc(li) at g(f(x0)).\<close>
    let ?bc = "\<lambda>l. top1_basepoint_change_on X TX x0 ((g \<circ> f) x0)
                     (top1_path_reverse ?\<alpha>1) l"
    have hH11id: "\<forall>x\<in>X. H1 (x, 1) = id x" using hH11 by simp
    note hbc_raw1 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl1 hx0]
    have hbc1: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) (?bc l1)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l1))"
        by (rule hbc_raw1)
      thus ?thesis by simp
    qed
    note hbc_raw2 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl2 hx0]
    have hbc2: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2) (?bc l2)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l2))"
        by (rule hbc_raw2)
      thus ?thesis by simp
    qed
    \<comment> \<open>Chain: bc(l1) \<simeq> g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 \<simeq> bc(l2) at g(f(x0)).\<close>
    have hgfx0: "(g \<circ> f) x0 = g (f x0)" by simp
    have hbc_equiv: "top1_loop_equiv_on X TX ((g \<circ> f) x0) (?bc l1) (?bc l2)"
    proof -
      have hgfl1': "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) ((g \<circ> f) \<circ> l2)"
        using hgfl_equiv by (simp add: comp_def)
      show ?thesis by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX
            top1_loop_equiv_on_sym[OF hbc1] hgfl1'] hbc2])
    qed
    \<comment> \<open>bc is injective by basepoint_change_iso_via_path + roundtrip.\<close>
    have hra1: "top1_is_path_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by blast
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by auto
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by auto
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by auto
    qed
    have hrev_a1: "top1_is_path_on X TX x0 ((g \<circ> f) x0) (top1_path_reverse ?\<alpha>1)"
      by (rule top1_path_reverse_is_path[OF hra1])
    \<comment> \<open>Roundtrip: li \<simeq> inv_bc(bc(li)). So bc(l1)\<simeq>bc(l2) \<Rightarrow> l1\<simeq>l2.\<close>
    have hrt1: "top1_loop_equiv_on X TX x0 l1
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))"
      unfolding top1_loop_equiv_on_def
      using hl1 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl1,
              unfolded top1_path_reverse_twice] by blast
    have hrt2: "top1_loop_equiv_on X TX x0 l2
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      unfolding top1_loop_equiv_on_def
      using hl2 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl2,
              unfolded top1_path_reverse_twice] by blast
    have hbc_cong: "top1_loop_equiv_on X TX x0
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra1
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]
            hbc_equiv])
    have hl1l2: "top1_loop_equiv_on X TX x0 l1 l2"
      by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX hrt1 hbc_cong]
          top1_loop_equiv_on_sym[OF hrt2]])
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 l1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 l2 g"
        using hl1l2 top1_loop_equiv_on_trans[OF hTX]
              top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hl1l2]]
        by blast
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  \<comment> \<open>Surjectivity: similar argument using f\<circ>g \<simeq> id.\<close>
  have hfstar_surj: "?f_star ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier Y TY (f x0)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
    thus "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
      using hfstar_range by (by100 blast)
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
    \<comment> \<open>d = [m] for some loop m at f(x0) in Y.\<close>
    obtain m where hm: "top1_is_loop_on Y TY (f x0) m"
        and hd_eq: "d = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>g\<circ>m is a loop at g(f(x0)) in X.\<close>
    have hgm: "top1_is_loop_on X TX (g (f x0)) (g \<circ> m)"
      by (rule top1_continuous_map_loop[OF hg hm])
    \<comment> \<open>Basepoint-change to x0: bc(\<alpha>1, g\<circ>m) is a loop at x0.\<close>
    have hra1: "top1_is_path_on X TX (g (f x0)) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by (by100 auto)
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    let ?bc_gm = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m)"
    have hbc_loop: "top1_is_loop_on X TX x0 ?bc_gm"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm])
    \<comment> \<open>c = [bc(\<alpha>1, g\<circ>m)] \<in> carrier(X, x0).\<close>
    let ?c = "{h. top1_loop_equiv_on X TX x0 ?bc_gm h}"
    have hc_mem: "?c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hbc_loop by (by100 blast)
    \<comment> \<open>f_*(c) = d: use f\<circ>g \<simeq> id to relate f\<circ>bc(\<alpha>1, g\<circ>m) to a basepoint change of m.\<close>
    obtain H2 where hH2cont: "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY H2"
        and hH20: "\<forall>y\<in>Y. H2 (y, 0) = (f \<circ> g) y" and hH21: "\<forall>y\<in>Y. H2 (y, 1) = y"
      using hfog unfolding top1_homotopic_on_def id_def by (by100 blast)
    let ?\<alpha>2 = "\<lambda>t. H2 (f x0, t)"
    \<comment> \<open>By homotopy_induced_basepoint_change: (f\<circ>g)\<circ>m \<simeq> bc(rev \<alpha>2, m).\<close>
    have hfx0Y: "f x0 \<in> Y" using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hH21': "\<forall>y\<in>Y. H2 (y, 1) = id y" using hH21 by (by100 simp)
    note hbc2 = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm hfx0Y]
    \<comment> \<open>hbc2: loop_equiv ((f\<circ>g)(f x0)) ((f\<circ>g)\<circ>m) (bc(rev \<alpha>2, id\<circ>m)).\<close>
    have hbc2': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m)
        (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
           (top1_path_reverse ?\<alpha>2) m)"
    proof -
      have "(\<lambda>y. f (g y)) \<circ> m = f \<circ> g \<circ> m" by (simp add: comp_def)
      moreover have "(\<lambda>y. y) \<circ> m = m" by (simp add: comp_def)
      ultimately show ?thesis using hbc2 by simp
    qed
    \<comment> \<open>f preserves path products: f \<circ> (p * q) = (f\<circ>p) * (f\<circ>q).\<close>
    have hf_comp_product: "\<And>p q. f \<circ> top1_path_product p q = top1_path_product (f \<circ> p) (f \<circ> q)"
      unfolding top1_path_product_def comp_def by (rule ext) (by100 auto)
    have hf_comp_rev: "\<And>p. f \<circ> top1_path_reverse p = top1_path_reverse (f \<circ> p)"
      unfolding top1_path_reverse_def comp_def by (rule ext) (by100 auto)
    \<comment> \<open>f \<circ> bc(\<alpha>1, g\<circ>m) = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m) since f preserves products.\<close>
    have hfbc_eq: "f \<circ> ?bc_gm = top1_basepoint_change_on Y TY (f (g (f x0))) (f x0)
        (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m)"
      unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
      by (simp add: comp_assoc)
    \<comment> \<open>Define \<gamma> = rev(\<alpha>2) * (f\<circ>\<alpha>1), a loop at f(x0).\<close>
    have hfa1: "top1_is_path_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)"
    proof -
      have ha1_cont: "top1_continuous_map_on I_set I_top X TX ?\<alpha>1"
        using hra1 unfolding top1_is_path_on_def by (by100 blast)
      have "top1_continuous_map_on I_set I_top Y TY (f \<circ> ?\<alpha>1)"
        using top1_continuous_map_on_comp[OF ha1_cont hf] by (simp add: comp_assoc)
      moreover have "(f \<circ> ?\<alpha>1) 0 = f (g (f x0))" using hH10 hx0 by (by100 auto)
      moreover have "(f \<circ> ?\<alpha>1) 1 = f x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have ha2: "top1_is_path_on Y TY (f (g (f x0))) (f x0) ?\<alpha>2"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst_fx0: "top1_continuous_map_on I_set I_top Y TY (\<lambda>_. f x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTY hfx0Y])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (f x0, t))) = (\<lambda>_. f x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (f x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (Y \<times> I_set) (product_topology_on TY I_top)
                     (\<lambda>t. (f x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTY hTI]]
              hconst_fx0[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top Y TY (\<lambda>t. H2 (f x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH2cont] by (simp add: comp_def)
      have "?\<alpha>2 0 = f (g (f x0))" using hH20 hfx0Y by (by100 auto)
      moreover have "?\<alpha>2 1 = f x0" using hH21 hfx0Y by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    have hra2: "top1_is_path_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2)"
      by (rule top1_path_reverse_is_path[OF ha2])
    let ?\<gamma> = "top1_path_product (top1_path_reverse ?\<alpha>2) (f \<circ> ?\<alpha>1)"
    have h\<gamma>_path: "top1_is_path_on Y TY (f x0) (f x0) ?\<gamma>"
      by (rule top1_path_product_is_path[OF hTY hra2 hfa1])
    \<comment> \<open>For ANY loop m' at f(x0): f \<circ> bc(\<alpha>1, g\<circ>m') \<simeq> bc(\<gamma>, m').\<close>
    have hcomp_is_bc: "\<And>m'. top1_is_loop_on Y TY (f x0) m' \<Longrightarrow>
        top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
    proof -
      fix m' assume hm': "top1_is_loop_on Y TY (f x0) m'"
      \<comment> \<open>f\<circ>bc(\<alpha>1, g\<circ>m') = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') (f preserves products).\<close>
      have hfbc': "f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m') =
          top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m')"
        unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
        by (simp add: comp_assoc)
      \<comment> \<open>f\<circ>g\<circ>m' \<simeq> bc(rev \<alpha>2, m') by homotopy_induced_basepoint_change.\<close>
      have hbc2_m': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
             (top1_path_reverse ?\<alpha>2) m')"
      proof -
        note hbc2_raw = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm' hfx0Y]
        have "(\<lambda>y. f (g y)) \<circ> m' = f \<circ> g \<circ> m'" by (simp add: comp_def)
        moreover have "(\<lambda>y. y) \<circ> m' = m'" by (simp add: comp_def)
        ultimately show ?thesis using hbc2_raw by simp
      qed
      \<comment> \<open>bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) by bc_loop_equiv.\<close>
      have hfgm'_loop: "top1_is_loop_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')"
        using hbc2_m' unfolding top1_loop_equiv_on_def by (by100 blast)
      have hbc_ra2_m': "top1_is_loop_on Y TY (f (g (f x0)))
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m')"
        by (rule top1_basepoint_change_is_loop[OF hTY hra2 hm'])
      have hstep2: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))"
        by (rule top1_basepoint_change_loop_equiv[OF hTY hfa1 hfgm'_loop hbc_ra2_m' hbc2_m'])
      \<comment> \<open>bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m') by double_bc.\<close>
      have hstep3: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule double_basepoint_change_equiv[OF hTY hfa1 hra2 hm'])
      \<comment> \<open>Chain: f\<circ>bc = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m').\<close>
      have hchain: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule top1_loop_equiv_on_trans[OF hTY hstep2 hstep3])
      show "top1_loop_equiv_on Y TY (f x0)
          (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        using hchain unfolding hfbc' .
    qed
    \<comment> \<open>Take m' = bc(rev(\<gamma>), m). By roundtrip: m \<simeq> bc(\<gamma>, m').\<close>
    let ?r\<gamma> = "top1_path_reverse ?\<gamma>"
    have hr\<gamma>: "top1_is_path_on Y TY (f x0) (f x0) ?r\<gamma>"
      by (rule top1_path_reverse_is_path[OF h\<gamma>_path])
    let ?m' = "top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m"
    have hm'_loop: "top1_is_loop_on Y TY (f x0) ?m'"
      by (rule top1_basepoint_change_is_loop[OF hTY hr\<gamma> hm])
    have hroundtrip: "top1_loop_equiv_on Y TY (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
    proof -
      have "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) (top1_path_reverse ?r\<gamma>)
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m))"
        by (rule top1_basepoint_change_roundtrip[OF hTY hr\<gamma> hm])
      hence hrt: "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (simp add: top1_path_reverse_twice)
      have hbc_gm'_loop: "top1_is_loop_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
      show ?thesis
        unfolding top1_loop_equiv_on_def
        using hm hbc_gm'_loop hrt by (by100 blast)
    qed
    \<comment> \<open>Construct preimage: c' = [bc(\<alpha>1, g\<circ>m')].\<close>
    have hgm': "top1_is_loop_on X TX (g (f x0)) (g \<circ> ?m')"
      by (rule top1_continuous_map_loop[OF hg hm'_loop])
    let ?c_pre = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> ?m')"
    have hcpre_loop: "top1_is_loop_on X TX x0 ?c_pre"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm'])
    have hcpre_mem: "{h. top1_loop_equiv_on X TX x0 ?c_pre h}
        \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hcpre_loop by (by100 blast)
    \<comment> \<open>f_*([c']) = [f\<circ>c'] = [bc(\<gamma>, m')] by hcomp_is_bc.\<close>
    have hfcpre_equiv: "top1_loop_equiv_on Y TY (f x0)
        (f \<circ> ?c_pre) (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule hcomp_is_bc[OF hm'_loop])
    \<comment> \<open>bc(\<gamma>, m') \<simeq> m by roundtrip (sym).\<close>
    have hbc_gm'_loop_Y: "top1_is_loop_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
    have hrt_ph: "top1_path_homotopic_on Y TY (f x0) (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      using hroundtrip unfolding top1_loop_equiv_on_def by (by100 blast)
    have hbcgm_equiv_m: "top1_loop_equiv_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m') m"
      unfolding top1_loop_equiv_on_def
      using hbc_gm'_loop_Y hm Lemma_51_1_path_homotopic_sym[OF hrt_ph]
      by (by100 blast)
    \<comment> \<open>f\<circ>c' \<simeq> m.\<close>
    have hfcpre_m: "top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) m"
      by (rule top1_loop_equiv_on_trans[OF hTY hfcpre_equiv hbcgm_equiv_m])
    \<comment> \<open>f_*([c']) = [m] = d.\<close>
    have hfstar_cpre: "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h} = d"
    proof -
      have "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        by (rule hfstar_class[OF hcpre_loop])
      also have "\<dots> = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      proof (intro equalityI subsetI)
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
          using top1_loop_equiv_on_trans[OF hTY
                  top1_loop_equiv_on_sym[OF hfcpre_m]] by (by100 simp)
      next
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
          using top1_loop_equiv_on_trans[OF hTY hfcpre_m] by (by100 simp)
      qed
      also have "\<dots> = d" using hd_eq by simp
      finally show ?thesis .
    qed
    thus "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
      using hcpre_mem by (by100 blast)
  qed
  have hfstar_bij: "bij_betw ?f_star (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    unfolding bij_betw_def using hfstar_inj hfstar_surj by blast
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))
      (top1_fundamental_group_mul Y TY (f x0)) ?f_star"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hfstar_range hfstar_hom hfstar_bij unfolding bij_betw_def by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

(** from \<S>58 Theorem 58.3: deformation retract induces isomorphism of fundamental groups.

    Munkres' proof: if A is a deformation retract of X via H, then the
    inclusion j: A \<hookrightarrow> X and the retraction r: X \<rightarrow> A = H(\<cdot>, 1) are homotopy
    invgerses. By Theorem 58.7, any homotopy equivalence induces an iso on \<pi>_1. **)

text \<open>Helper: the inclusion-induced map takes A-equivalence classes to X-equivalence classes.\<close>
lemma inclusion_induced_class:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hf: "top1_is_loop_on A TA x0 f"
  shows "top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}
    = {k. top1_loop_equiv_on X TX x0 f k}"
proof (intro set_eqI iffI)
  fix k assume "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
  then obtain g where hfg: "top1_loop_equiv_on A TA x0 f g"
      and hgk: "top1_loop_equiv_on X TX x0 (id \<circ> g) k"
    unfolding top1_fundamental_group_induced_on_def by (by100 blast)
  have hg_loop: "top1_is_loop_on A TA x0 g"
    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
  have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    using top1_induced_preserves_loop_equiv[OF hTA hj hf hg_loop hfg]
    by (simp add: comp_def)
  have hgk': "top1_loop_equiv_on X TX x0 g k"
    using hgk by (simp add: comp_def)
  show "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
    using top1_loop_equiv_on_trans[OF hTX hfg_X hgk'] by simp
next
  fix k assume hk: "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
  hence hfk: "top1_loop_equiv_on X TX x0 f k" by simp
  have hff: "top1_loop_equiv_on A TA x0 f f"
    by (rule top1_loop_equiv_on_refl[OF hf])
  have hfk': "top1_loop_equiv_on X TX x0 (id \<circ> f) k"
    using hfk by (simp add: comp_def)
  show "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
    unfolding top1_fundamental_group_induced_on_def
    using hff hfk' by (by100 blast)
qed

text \<open>Helper for Theorem 58.3: the inclusion-induced map on \<pi>_1 classes is
  a group isomorphism when the inclusion has a retraction homotopic to id.\<close>
lemma inclusion_retraction_iso:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hr: "top1_continuous_map_on X TX A TA r"
      and hrj: "\<forall>a\<in>A. r a = a"
      and hjr: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
          top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>The inclusion j: A \<hookrightarrow> X induces j_*: \<pi>_1(A) \<rightarrow> \<pi>_1(X).
     Step 1 (Injectivity): If j_*[f] = [const] in \<pi>_1(X), then f \<simeq> const in X.
     Apply r: r\<circ>f \<simeq> r\<circ>const = const in A. But r\<circ>f = f (since f \<subseteq> A and r|A = id).
     So f \<simeq> const in A. Hence j_* is injective.
     Step 2 (Surjectivity): For any loop f in X, hjr gives f \<simeq> r\<circ>f in X.
     r\<circ>f is a loop in A, so [f] = j_*[r\<circ>f]. Hence j_* is surjective.
     Step 3 (Homomorphism): j_* preserves products by functoriality.\<close>
  let ?j_star = "top1_fundamental_group_induced_on A TA x0 X TX x0 id"
  have hj_inj: "inj_on ?j_star (top1_fundamental_group_carrier A TA x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier A TA x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier A TA x0"
       and heq: "?j_star c1 = ?j_star c2"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on A TA x0 g h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>j_*(c1) = [f]_X, j_*(c2) = [g]_X.\<close>
    have hjc1: "?j_star c1 = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc1_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjc2: "?j_star c2 = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hc2_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>[f]_X = [g]_X, so f \<simeq>_X g.\<close>
    have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    proof -
      have hf_X: "top1_is_loop_on X TX x0 f"
        using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
      have hclass_eq: "{k. top1_loop_equiv_on X TX x0 f k}
          = {k. top1_loop_equiv_on X TX x0 g k}"
        using heq hjc1 hjc2 by simp
      have "top1_loop_equiv_on X TX x0 f f"
        by (rule top1_loop_equiv_on_refl[OF hf_X])
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 f k}" by simp
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 g k}"
        using hclass_eq by simp
      hence "top1_loop_equiv_on X TX x0 g f" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply r: r\<circ>f \<simeq>_A r\<circ>g.\<close>
    have hfg_hom_X: "top1_path_homotopic_on X TX x0 x0 f g"
      using hfg_X unfolding top1_loop_equiv_on_def by (by100 blast)
    have hrf_rg_A: "top1_path_homotopic_on A TA (r x0) (r x0) (r \<circ> f) (r \<circ> g)"
      by (rule continuous_preserves_path_homotopic[OF hTX hTA hr hfg_hom_X])
    have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
    have hrf_rg_A': "top1_path_homotopic_on A TA x0 x0 (r \<circ> f) (r \<circ> g)"
      using hrf_rg_A unfolding hrx0 .
    \<comment> \<open>r\<circ>f = f and r\<circ>g = g (since f, g map into A and r|A = id).\<close>
    have hf_mem: "\<forall>s\<in>I_set. f s \<in> A"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hg_mem: "\<forall>s\<in>I_set. g s \<in> A"
      using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hrf_eq_f: "\<forall>s\<in>I_set. (r \<circ> f) s = f s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "f s \<in> A" using hf_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> f) s = f s" using hrj by (simp add: comp_def)
    qed
    have hrg_eq_g: "\<forall>s\<in>I_set. (r \<circ> g) s = g s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "g s \<in> A" using hg_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> g) s = g s" using hrj by (simp add: comp_def)
    qed
    \<comment> \<open>Transfer: f \<simeq>_A r\<circ>f and g \<simeq>_A r\<circ>g (by loop_agree_on_I).\<close>
    have hf_rf: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> f)"
      using conjunct2[OF loop_agree_on_I[OF hf hrf_eq_f]] .
    have hg_rg: "top1_path_homotopic_on A TA x0 x0 g (r \<circ> g)"
      using conjunct2[OF loop_agree_on_I[OF hg hrg_eq_g]] .
    \<comment> \<open>Chain: f \<simeq>_A r\<circ>f \<simeq>_A r\<circ>g \<simeq>_A g.\<close>
    have hf_rg: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> g)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rf hrf_rg_A'])
    have hrg_g: "top1_path_homotopic_on A TA x0 x0 (r \<circ> g) g"
      by (rule Lemma_51_1_path_homotopic_sym[OF hg_rg])
    have hfg_A: "top1_path_homotopic_on A TA x0 x0 f g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rg hrg_g])
    have hfg_equiv: "top1_loop_equiv_on A TA x0 f g"
      unfolding top1_loop_equiv_on_def using hf hg hfg_A by (by100 blast)
    show "c1 = c2"
    proof -
      have "\<And>h. top1_loop_equiv_on A TA x0 f h \<longleftrightarrow> top1_loop_equiv_on A TA x0 g h"
        using hfg_equiv top1_loop_equiv_on_trans[OF hTA]
              top1_loop_equiv_on_trans[OF hTA top1_loop_equiv_on_sym[OF hfg_equiv]]
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  have hj_surj: "?j_star ` (top1_fundamental_group_carrier A TA x0)
      = top1_fundamental_group_carrier X TX x0"
  proof (intro set_eqI iffI)
    fix c assume "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
    then obtain c_A where hcA: "c_A \<in> top1_fundamental_group_carrier A TA x0"
        and hc_eq: "c = ?j_star c_A" by (by100 blast)
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hcA_eq: "c_A = {g. top1_loop_equiv_on A TA x0 f g}"
      using hcA unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hjc: "c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq hcA_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    show "c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def hjc
      using hf_X by (by100 blast)
  next
    fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX x0"
    obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>r\<circ>f is a loop in A.\<close>
    have hrf_loop: "top1_is_loop_on A TA x0 (r \<circ> f)"
    proof -
      have hrf: "top1_is_loop_on A TA (r x0) (r \<circ> f)"
        by (rule top1_continuous_map_loop[OF hr hf])
      have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
      show ?thesis using hrf unfolding hrx0 .
    qed
    \<comment> \<open>j_*([r\<circ>f]_A) = [r\<circ>f]_X.\<close>
    let ?c_A = "{g. top1_loop_equiv_on A TA x0 (r \<circ> f) g}"
    have hcA_mem: "?c_A \<in> top1_fundamental_group_carrier A TA x0"
      unfolding top1_fundamental_group_carrier_def using hrf_loop by (by100 blast)
    have hjcA: "?j_star ?c_A = {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hrf_loop])
    \<comment> \<open>r\<circ>f \<simeq> f in X (by hjr), so [r\<circ>f]_X = [f]_X.\<close>
    have hrf_f: "top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      by (rule hjr[OF hf])
    have hrf_equiv_f: "top1_loop_equiv_on X TX x0 (r \<circ> f) f"
      unfolding top1_loop_equiv_on_def using hrf_f
      using top1_continuous_map_loop[OF hj hrf_loop] hf
      by (simp add: comp_def top1_is_loop_on_def)
    have hclass_eq: "{k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}
        = {k. top1_loop_equiv_on X TX x0 f k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      hence hk: "top1_loop_equiv_on X TX x0 (r \<circ> f) k" by simp
      have "top1_loop_equiv_on X TX x0 f (r \<circ> f)"
        by (rule top1_loop_equiv_on_sym[OF hrf_equiv_f])
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
        using top1_loop_equiv_on_trans[OF hTX _ hk] by simp
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
      hence hk: "top1_loop_equiv_on X TX x0 f k" by simp
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
        using top1_loop_equiv_on_trans[OF hTX hrf_equiv_f] by simp
    qed
    show "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
      using hcA_mem unfolding hc_eq hjcA[symmetric] hclass_eq[symmetric] by (by100 blast)
  qed
  have hj_hom: "\<forall>c\<in>top1_fundamental_group_carrier A TA x0.
      \<forall>d\<in>top1_fundamental_group_carrier A TA x0.
      ?j_star (top1_fundamental_group_mul A TA x0 c d)
      = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
  proof (intro ballI)
    fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
        and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hd_eq: "d = {h. top1_loop_equiv_on A TA x0 g h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>c \<cdot> d = [f*g]_A by mul_class.\<close>
    have hcd: "top1_fundamental_group_mul A TA x0 c d
        = {h. top1_loop_equiv_on A TA x0 (top1_path_product f g) h}"
      unfolding hc_eq hd_eq
      by (rule top1_fundamental_group_mul_class[OF hTA hf hg])
    \<comment> \<open>f*g is a loop in A.\<close>
    have hfg_loop: "top1_is_loop_on A TA x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTA hf hg])
    \<comment> \<open>j_*(c\<cdot>d) = j_*([f*g]_A) = [f*g]_X.\<close>
    have hjcd: "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hcd
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hfg_loop])
    \<comment> \<open>j_*(c) = [f]_X, j_*(d) = [g]_X.\<close>
    have hjc: "?j_star c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjd: "?j_star d = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hd_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>f, g are loops in X (since A \<subseteq> X and inclusion is continuous).\<close>
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    have hg_X: "top1_is_loop_on X TX x0 g"
      using top1_continuous_map_loop[OF hj hg] by (simp add: comp_def)
    \<comment> \<open>[f]_X \<cdot> [g]_X = [f*g]_X by mul_class.\<close>
    have hjcd': "top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hjc hjd
      by (rule top1_fundamental_group_mul_class[OF hTX hf_X hg_X])
    show "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
      unfolding hjcd hjcd' ..
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_mul A TA x0)
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0) ?j_star"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star c \<in> top1_fundamental_group_carrier X TX x0"
        using hj_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
          and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star (top1_fundamental_group_mul A TA x0 c d)
          = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
        using hj_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?j_star (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_carrier X TX x0)"
      unfolding bij_betw_def using hj_inj hj_surj by (by100 blast)
  qed
qed

theorem Theorem_58_3:
  assumes hdef: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
           (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  obtain H where hAsub: "A \<subseteq> X"
      and hH: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x" and hH1: "\<forall>x\<in>X. H (x, 1) \<in> A"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    using hdef unfolding top1_deformation_retract_of_on_def by blast
  let ?TA = "subspace_topology X TX A"
  have hTA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hAsub])
  \<comment> \<open>j = id (inclusion) and r = H(\<cdot>,1) (retraction) form a homotopy equivalence.
     By Theorem 58.7, this gives the isomorphism.\<close>
  let ?r = "\<lambda>x. H (x, 1::real)"
  \<comment> \<open>1. Inclusion id: A \<rightarrow> X is continuous.\<close>
  have hj_cont: "top1_continuous_map_on A ?TA X TX id"
    by (rule top1_continuous_map_on_subspace_restrict[OF top1_continuous_map_on_id[OF hTX] hAsub])
  \<comment> \<open>2. Retraction r: X \<rightarrow> A is continuous.\<close>
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hpair1: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top)
                  (\<lambda>x. (x, 1::real))"
  proof -
    have hc1: "top1_continuous_map_on X TX I_set I_top (\<lambda>_. 1::real)"
      by (rule top1_continuous_map_on_const[OF hTX hTI h1_I])
    have hp1_eq: "pi1 \<circ> (\<lambda>x. (x, 1::real)) = id" unfolding pi1_def by (rule ext) simp
    have hp1: "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp1_eq by (rule top1_continuous_map_on_id[OF hTX])
    have hp2_eq: "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)" unfolding pi2_def by (rule ext) simp
    have hp2: "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp2_eq by (rule hc1)
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTX hTX hTI, of "\<lambda>x. (x, 1::real)"]]
      hp1 hp2 by blast
  qed
  have hr_cont_X: "top1_continuous_map_on X TX X TX ?r"
    using top1_continuous_map_on_comp[OF hpair1 hH] by (simp add: comp_def)
  have hr_img: "?r ` X \<subseteq> A" using hH1 by auto
  have hr_cont: "top1_continuous_map_on X TX A ?TA ?r"
    by (rule top1_continuous_map_on_codomain_shrink[OF hr_cont_X hr_img hAsub])
  \<comment> \<open>3. r \<circ> id ≃ id_A: since H(a,1)=a for a\<in>A, r\<circ>id = id on A. Trivial homotopy.\<close>
  have hrj_eq: "\<forall>a\<in>A. ?r (id a) = id a"
    using hHA h1_I by auto
  have hrj_hom: "top1_homotopic_on A ?TA A ?TA (?r \<circ> id) id"
  proof -
    have hrj_fun_eq: "\<And>a. a \<in> A \<Longrightarrow> (?r \<circ> id) a = id a"
      using hrj_eq by simp
    \<comment> \<open>Constant homotopy: F(a,t) = a for all t.\<close>
    have hconst_hom: "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top)
                        A ?TA (\<lambda>p. fst p)"
    proof -
      have hTP: "is_topology_on (A \<times> I_set) (product_topology_on ?TA I_top)"
        by (rule product_topology_on_is_topology_on[OF hTA hTI])
      have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (pi1 \<circ> id)"
      proof -
        have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA pi1"
          by (rule top1_continuous_pi1[OF hTA hTI])
        thus ?thesis by simp
      qed
      thus ?thesis unfolding pi1_def comp_def by simp
    qed
    have hcont_rj: "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)"
      using top1_continuous_map_on_comp[OF hj_cont hr_cont] by simp
    show ?thesis
      unfolding top1_homotopic_on_def
    proof (intro conjI exI)
      show "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)" by (rule hcont_rj)
      show "top1_continuous_map_on A ?TA A ?TA id" by (rule top1_continuous_map_on_id[OF hTA])
      show "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (\<lambda>p. fst p)"
        by (rule hconst_hom)
      show "\<forall>x\<in>A. fst (x, 0::real) = (?r \<circ> id) x" using hrj_fun_eq by auto
      show "\<forall>x\<in>A. fst (x, 1::real) = id x" by simp
    qed
  qed
  \<comment> \<open>4. id \<circ> r ≃ id_X: via H(x, 1-t). H(x,0)=x=id(x), H(x,1)=(id\<circ>r)(x).\<close>
  have hjr_hom: "top1_homotopic_on X TX X TX (id \<circ> ?r) id"
  proof -
    \<comment> \<open>Homotopy F(x,t) = H(x, 1-t). F(x,0) = H(x,1) = r(x), F(x,1) = H(x,0) = x.\<close>
    let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
    \<comment> \<open>flip is continuous X\<times>I \<rightarrow> X\<times>I via Theorem 18.4.\<close>
    have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
      by (rule product_topology_on_is_topology_on[OF hTX hTI])
    have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (pi1 \<circ> ?flip)"
    proof -
      have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
      thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
    qed
    have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        I_set I_top (pi2 \<circ> ?flip)"
    proof -
      have hpi2_flip_eq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)"
        unfolding pi2_def by (rule ext) auto
      \<comment> \<open>(\<lambda>t. 1-t) is continuous I \<rightarrow> I.\<close>
      have hrev_map: "\<And>t. t \<in> I_set \<Longrightarrow> 1 - t \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hrev_cont: "continuous_on UNIV (\<lambda>t::real. 1 - t)" by (intro continuous_intros)
      have hrev_I: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      proof -
        have "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set) I_set
          (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
          by (rule top1_continuous_map_on_real_subspace_open_sets[OF hrev_map hrev_cont])
        thus ?thesis unfolding top1_unit_interval_topology_def .
      qed
      have hpi2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
        by (rule top1_continuous_pi2[OF hTX hTI])
      have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
          ((\<lambda>t. 1 - t) \<circ> pi2)"
        by (rule top1_continuous_map_on_comp[OF hpi2_cont hrev_I])
      have hcomp_eq: "((\<lambda>t. 1 - t) \<circ> pi2) = (\<lambda>p. 1 - pi2 p)" by (rule ext) (simp add: comp_def)
      show ?thesis unfolding hpi2_flip_eq hcomp_eq[symmetric] by (rule hcomp)
    qed
    have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        (X \<times> I_set) (product_topology_on TX I_top) ?flip"
      using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]]
      hflip_pi1 hflip_pi2 by blast
    have hF_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (\<lambda>p. H (?flip p))"
      using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def)
    have hF_eq: "\<And>p. ?flip p = (fst p, 1 - snd p)" by auto
    have hF0: "\<forall>x\<in>X. H (x, 1 - (0::real)) = (id \<circ> ?r) x" by simp
    have hF1: "\<forall>x\<in>X. H (x, 1 - (1::real)) = id x"
    proof
      fix x assume "x \<in> X"
      thus "H (x, 1 - 1) = id x" using hH0 by simp
    qed
    show ?thesis
      unfolding top1_homotopic_on_def id_def[symmetric]
    proof (intro conjI exI)
      show "top1_continuous_map_on X TX X TX (id \<circ> ?r)"
      proof -
        have "(id \<circ> ?r) = ?r" by (rule ext) (simp add: id_def)
        thus ?thesis using hr_cont_X by simp
      qed
      show "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
              (\<lambda>p. H (fst p, 1 - snd p))"
        using hF_cont by (simp add: case_prod_beta)
      show "\<forall>x\<in>X. H (fst (x, 0::real), 1 - snd (x, 0::real)) = (id \<circ> ?r) x"
        using hF0 by simp
      show "\<forall>x\<in>X. H (fst (x, 1::real), 1 - snd (x, 1::real)) = id x"
        using hF1 by simp
    qed
  qed
  \<comment> \<open>Following Munkres' textbook proof: use Lemma 58.1 (basepoint FIXED) directly.
     Key: H fixes x₀ ∈ A, so the basepoint-fixed version applies.\<close>
  have hx0X: "x0 \<in> X" using hx0 hAsub by blast
  \<comment> \<open>Lemma 58.1 applied: j\<circ>r \<simeq> id with x₀ fixed \<Rightarrow> (j\<circ>r)\<circ>f \<simeq> f for any loop f at x₀.\<close>
  have hjr_fixed: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> f) f"
  proof -
    fix fl assume hfl: "top1_is_loop_on X TX x0 fl"
    \<comment> \<open>Homotopy from j\<circ>r to id that fixes x₀: use H with H(x₀,t) = x₀.\<close>
    have hH_base_fixed: "\<forall>t\<in>I_set. H (x0, t) = x0"
      using hHA hx0 by blast
    have hH_for_58_1: "\<exists>G. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX G
        \<and> (\<forall>x\<in>X. G (x, 0) = (\<lambda>x. ?r x) x) \<and> (\<forall>x\<in>X. G (x, 1) = id x)
        \<and> (\<forall>t\<in>I_set. G (x0, t) = x0)"
    proof (intro exI conjI)
      let ?G = "\<lambda>p. H (fst p, 1 - snd p)"
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX ?G"
      proof -
        let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
        have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
          by (rule product_topology_on_is_topology_on[OF hTX hTI])
        have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?flip)"
        proof -
          have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
          thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
        qed
        have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?flip)"
        proof -
          have heq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)" unfolding pi2_def by (rule ext) auto
          have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
          proof -
            have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set) I_set
                (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
              by (rule top1_continuous_map_on_real_subspace_open_sets)
                 (auto simp: top1_unit_interval_def intro: continuous_intros)
            thus ?thesis unfolding top1_unit_interval_topology_def .
          qed
          have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top ((\<lambda>t. 1 - t) \<circ> pi2)"
            by (rule top1_continuous_map_on_comp[OF top1_continuous_pi2[OF hTX hTI] hrev])
          show ?thesis unfolding heq using hcomp by (simp add: comp_def)
        qed
        have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
            (X \<times> I_set) (product_topology_on TX I_top) ?flip"
          using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]] hflip_pi1 hflip_pi2 by blast
        show ?thesis
          using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def case_prod_beta)
      qed
      show "\<forall>x\<in>X. ?G (x, 0) = ?r x" by simp
      show "\<forall>x\<in>X. ?G (x, 1) = id x" using hH0 by simp
      show "\<forall>t\<in>I_set. ?G (x0, t) = x0"
      proof
        fix t assume "t \<in> I_set"
        hence "1 - t \<in> I_set" unfolding top1_unit_interval_def by auto
        thus "?G (x0, t) = x0" using hH_base_fixed by simp
      qed
    qed
    have hhx0: "(\<lambda>x. ?r x) x0 = x0"
      using hHA hx0 h1_I by auto
    have "top1_path_homotopic_on X TX x0 x0
        (top1_induced_homomorphism_on X TX X TX (\<lambda>x. ?r x) fl)
        (top1_induced_homomorphism_on X TX X TX id fl)"
      by (rule Lemma_58_1_basepoint_fixed[OF hTX
            hr_cont_X top1_continuous_map_on_id[OF hTX]
            hhx0 _ hH_for_58_1 hfl]) simp
    hence "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) ((\<lambda>x. x) \<circ> fl)"
      unfolding top1_induced_homomorphism_on_def id_def by simp
    thus "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) fl"
      by (simp add: comp_def)
  qed
  \<comment> \<open>Now: r_*\<circ>j_* = id on \<pi>_1(A) because r\<circ>j = id_A pointwise.
     And j_*\<circ>r_* = id on \<pi>_1(X) because j\<circ>r \<simeq> id with basepoint fixed (Lemma 58.1).
     So j_* is bijective (with inverse r_*), hence a group isomorphism.\<close>
  \<comment> \<open>Apply the inclusion-retraction lemma with j=id, r=H(\<cdot>,1).\<close>
  have hrj_pointwise: "\<forall>a\<in>A. ?r a = a" using hHA h1_I by auto
  show ?thesis
    by (rule inclusion_retraction_iso[OF hTX hTA hAsub refl hj_cont hr_cont hrj_pointwise hjr_fixed hx0])
qed

(** from \<S>58 Theorem 58.2: inclusion S^1 \<rightarrow> R^2-0 induces isomorphism of fundamental groups.

    Munkres' proof: S^1 is a deformation retract of R^2 - 0 via
    H(x, t) = (1-t)x + t(x/||x||). By Theorem 58.3, the inclusion induces
    an isomorphism of fundamental groups. **)
theorem Theorem_58_2_inclusion_iso:
  fixes TR2_0 :: "(real \<times> real) set set"
  defines "TR2_0 \<equiv> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_mul top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_carrier (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_mul (UNIV - {(0, 0)}) TR2_0 (1, 0))"
proof -
  \<comment> \<open>S^1 is a deformation retract of R^2 - {0} via H(x,t) = (1-t)x + t(x/|x|).\<close>
  have hdef: "top1_deformation_retract_of_on
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
       (UNIV - {(0::real, 0::real)}))
    top1_S1"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?H = "\<lambda>(x::real\<times>real, t::real). ((1-t)*fst x + t*fst x/?norm x, (1-t)*snd x + t*snd x/?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by auto
    have hH0: "\<forall>x\<in>?R2_0. ?H (x, 0) = x" by simp
    have hH1: "\<forall>x\<in>?R2_0. ?H (x, 1) \<in> top1_S1"
    proof
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0"
      hence hne: "x \<noteq> (0, 0)" by simp
      hence hnorm_pos: "?norm x > 0"
      proof -
        have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
        hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
        thus ?thesis by simp
      qed
      have "?H (x, 1) = (fst x / ?norm x, snd x / ?norm x)" by simp
      moreover have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 = 1"
      proof -
        have hns: "?norm x ^ 2 = fst x ^ 2 + snd x ^ 2"
          using hnorm_pos by (simp add: real_sqrt_pow2)
        have h1: "(fst x / ?norm x) ^ 2 = fst x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have h2: "(snd x / ?norm x) ^ 2 = snd x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have hdn: "fst x ^ 2 + snd x ^ 2 \<noteq> 0"
        proof -
          have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
          hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
          thus ?thesis by linarith
        qed
        let ?d = "fst x ^ 2 + snd x ^ 2"
        have "fst x ^ 2 / ?d + snd x ^ 2 / ?d = ?d / ?d"
          by (metis add_divide_distrib)
        also have "?d / ?d = 1" using hdn by simp
        finally show ?thesis unfolding h1 h2 .
      qed
      ultimately show "?H (x, 1) \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    have hHA: "\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. ?H (a, t) = a"
    proof (intro ballI)
      fix a :: "real \<times> real" and t :: real
      assume ha: "a \<in> top1_S1" and ht: "t \<in> I_set"
      have heq: "fst a ^ 2 + snd a ^ 2 = 1" using ha unfolding top1_S1_def by simp
      hence hnorm: "?norm a = 1" by (simp add: real_sqrt_eq_1_iff)
      show "?H (a, t) = a" using hnorm by (simp add: prod_eq_iff algebra_simps)
    qed
    have hHcont: "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) ?R2_0 ?TR ?H"
    proof -
      \<comment> \<open>Step 1: continuous_on (R²-{0})×I H.\<close>
      have hH_std: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))"
      proof -
        \<comment> \<open>Norm and division continuous on R²-{0}.\<close>
        have hnorm_cont: "continuous_on ?R2_0 ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power continuous_intros) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0"
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          thus "?norm x \<noteq> 0" by (metis less_imp_neq not_sym real_sqrt_gt_zero)
        qed
        have hfst_div: "continuous_on ?R2_0 (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        have hsnd_div: "continuous_on ?R2_0 (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        \<comment> \<open>Lift to (R²-{0})×I via composition with fst.\<close>
        have hfst_R2: "continuous_on (?R2_0 \<times> I_set) (fst::(real\<times>real)\<times>real \<Rightarrow> real\<times>real)"
          by (intro continuous_intros)
        have hfst_img: "fst ` (?R2_0 \<times> I_set) \<subseteq> ?R2_0" by (by100 auto)
        have hfdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. fst (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hfst_div hfst_img]]
          by (simp add: comp_def)
        have hsdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. snd (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hsnd_div hfst_img]]
          by (simp add: comp_def)
        have hid: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. p)"
          by (rule continuous_on_id)
        have h1mt: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. 1 - snd p)"
          by (intro continuous_on_diff continuous_on_const continuous_on_snd[OF hid])
        have hff: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. fst (fst p))"
          by (intro continuous_on_fst[OF continuous_on_fst[OF hid]])
        have hsf: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd (fst p))"
          by (intro continuous_on_snd[OF continuous_on_fst[OF hid]])
        have ht: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd p)"
          by (intro continuous_on_snd[OF hid])
        have htfd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (fst (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hfdiv'])
        have htsd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (snd (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hsdiv'])
        have hcomp1: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * fst (fst p) + snd p * (fst (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hff ht hfdiv')
        have hcomp2: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * snd (fst p) + snd p * (snd (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hsf ht hsdiv')
        show ?thesis
          using continuous_on_Pair[OF hcomp1 hcomp2] by simp
      qed
      have hH_eq: "(\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))
        = (\<lambda>p. ?H (fst p, snd p))"
        by (rule ext) (simp add: case_prod_beta)
      have hH_std': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. ?H (fst p, snd p))"
        using hH_std unfolding hH_eq .
      \<comment> \<open>Step 2: H maps into R²-{0}.\<close>
      have hH_range: "\<And>p. p \<in> ?R2_0 \<times> I_set \<Longrightarrow> (\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
      proof -
        fix p :: "(real \<times> real) \<times> real"
        assume hp: "p \<in> ?R2_0 \<times> I_set"
        have hxR2: "fst p \<in> ?R2_0" using hp by (simp add: mem_Times_iff)
        hence hxnz: "fst p \<noteq> (0, 0)" by (by100 simp)
        have htI: "snd p \<in> I_set" using hp by (simp add: mem_Times_iff)
        have hnp: "?norm (fst p) > 0"
          using hxnz by (cases "fst p") (auto simp: sum_power2_gt_zero_iff real_sqrt_gt_zero)
        \<comment> \<open>H(x,t) \<noteq> 0: if it were, both components = 0 ⟹ x = 0, contradiction.\<close>
        have "?H (fst p, snd p) \<noteq> (0, 0)"
        proof
          assume habs: "?H (fst p, snd p) = (0, 0)"
          \<comment> \<open>Component 1: (1-t)*a + t*a/|x| = 0 means a*((1-t) + t/|x|) = 0.\<close>
          have h1: "(1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          have h2: "(1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          \<comment> \<open>Multiply by |x| > 0: (1-t)*a*|x| + t*a = 0 and similarly for b.\<close>
          have h1': "(1 - snd p) * fst (fst p) * ?norm (fst p) + snd p * fst (fst p) = 0"
          proof -
            from h1 have "((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * fst (fst p) * ?norm (fst p) +
                snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * fst (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have h2': "(1 - snd p) * snd (fst p) * ?norm (fst p) + snd p * snd (fst p) = 0"
          proof -
            from h2 have "((1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * snd (fst p) * ?norm (fst p) +
                snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * snd (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          \<comment> \<open>Factor: a * ((1-t)*|x| + t) = 0 and b * ((1-t)*|x| + t) = 0.\<close>
          have hfact1: "fst (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h1' by (simp add: algebra_simps)
          have hfact2: "snd (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h2' by (simp add: algebra_simps)
          \<comment> \<open>(1-t)*|x| + t > 0 since |x| > 0 and t \<ge> 0, 1-t \<ge> 0.\<close>
          have hc_pos: "(1 - snd p) * ?norm (fst p) + snd p > 0"
          proof (cases "snd p = 0")
            case True thus ?thesis using hnp by (by100 simp)
          next
            case False
            have "snd p > 0" using False htI unfolding top1_unit_interval_def by (by100 simp)
            moreover have "(1 - snd p) * ?norm (fst p) \<ge> 0"
              using htI hnp unfolding top1_unit_interval_def by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have "fst (fst p) = 0" using hfact1 hc_pos by (by100 simp)
          moreover have "snd (fst p) = 0" using hfact2 hc_pos by (by100 simp)
          ultimately show False using hxnz by (simp add: prod_eq_iff)
        qed
        thus "(\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
          by (simp add: case_prod_beta)
      qed
      \<comment> \<open>Step 3: Transfer.\<close>
      have "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top)
          ?R2_0 ?TR (\<lambda>p. ?H (fst p, snd p))"
        by (rule R2_subspace_I_continuous_on_transfer[OF hH_std' hH_range])
      moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?H (fst p, snd p)) = ?H"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    show ?thesis unfolding top1_deformation_retract_of_on_def
      using hS1sub hHcont hH0 hH1 hHA by blast
  qed
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTR2_0: "is_topology_on (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hS1_eq: "top1_S1_topology = subspace_topology
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
    top1_S1"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_trans[of top1_S1 "UNIV - {(0, 0)}", symmetric])
       (auto simp: top1_S1_def)
  have hdef': "top1_deformation_retract_of_on (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1"
    unfolding TR2_0_def by (rule hdef)
  have hTR2_0': "is_topology_on (UNIV - {(0::real, 0::real)}) TR2_0"
    unfolding TR2_0_def by (rule hTR2_0)
  show ?thesis
    unfolding TR2_0_def[symmetric]
    by (rule Theorem_58_3[OF hdef' hTR2_0' h10])
qed

corollary Theorem_58_7_strict:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
    and "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
  using Theorem_58_7[OF is_topology_on_strict_imp[OF assms(1)] is_topology_on_strict_imp[OF assms(2)] assms(3) assms(4)] by blast

text \<open>Strict version: if X and Y have the same homotopy type and X is strict,
  Y is also strict.\<close>
corollary top1_same_homotopy_type_strict:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  by (rule top1_same_homotopy_type_on_sym[OF assms])

section \<open>\<S>59 The Fundamental Group of S^n\<close>

text \<open>The n-sphere S^n embedded in R^{n+1}.\<close>
definition top1_Sn :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "top1_Sn n = {x. (\<forall>i \<ge> Suc n. x i = 0) \<and> (\<Sum>i\<le>n. (x i)^2) = 1}"

(** from \<S>59 Theorem 59.1: the images of i_*: \<pi>_1(U, x_0) \<rightarrow> \<pi>_1(X, x_0) and
    j_*: \<pi>_1(V, x_0) \<rightarrow> \<pi>_1(X, x_0) generate \<pi>_1(X, x_0). Equivalently, every loop in
    X at x_0 is path-homotopic to a finite concatenation of loops, each of which
    lies entirely in U or entirely in V. **)
theorem Theorem_59_1:
  assumes hT: "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and hUV: "U \<union> V = X" and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hx0: "x0 \<in> U \<inter> V"
  shows "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
    (\<exists>n \<ge> 1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
            \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V))
       \<and> top1_path_homotopic_on X TX x0 x0 f
           (foldr (top1_path_product) gs (top1_constant_path x0)))"
  \<comment> \<open>Munkres 59.1: Step 1: Lebesgue number gives subdivision a0<...<an with f([ai,ai+1])
     in U or V and f(ai) in U\<inter>V. Step 2: Choose paths \<alpha>i in U\<inter>V from x0 to f(ai).
     Set gi = (\<alpha>_{i-1} * fi) * \<alpha>i_bar. Each gi is a loop in U or V at x0, and
     [g1]*...*[gn] = [f1]*...*[fn] = [f].\<close>
proof (intro allI impI)
  fix f assume hf: "top1_is_loop_on X TX x0 f"
  \<comment> \<open>Step 1: Lebesgue subdivision. Find a0<...<an with f([ai,ai+1]) in U or V.\<close>
  obtain m :: nat and subdivision :: "nat \<Rightarrow> real" where
    hm: "m \<ge> 1" and hsub0: "subdivision 0 = 0" and hsubm: "subdivision m = 1"
    and hsub_mono: "\<forall>i<m. subdivision i < subdivision (Suc i)"
    and hsub_UV: "\<forall>i<m. f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> U
                       \<or> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> V"
    and hsub_int: "\<forall>i\<le>m. f (subdivision i) \<in> U \<inter> V"
    sorry
  \<comment> \<open>Step 2: For each subinterval, define fi = f restricted + reparametrized.
     Choose paths \<alpha>i in U\<inter>V from x0 to f(ai). Set gi = (\<alpha>_{i-1} * fi) * rev \<alpha>i.\<close>
  obtain gs :: "(real \<Rightarrow> 'a) list" where
    hgs_len: "length gs = m" and
    hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs!i)
        \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)" and
    hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    sorry
  show "\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs ! i) \<and>
              (gs ! i ` I_set \<subseteq> U \<or> gs ! i ` I_set \<subseteq> V)) \<and>
       top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    using hm hgs_len hgs_loops hgs_product by (by100 auto)
qed

text \<open>Helper: path homotopy in a subspace implies path homotopy in the ambient space.\<close>
lemma path_homotopic_subspace_to_ambient:
  assumes hTX: "is_topology_on X TX" and hUsub: "U \<subseteq> X"
      and hTU: "TU = subspace_topology X TX U"
      and hhom: "top1_path_homotopic_on U TU x0 x1 f g"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  \<comment> \<open>A path homotopy F: I\<times>I \<rightarrow> U in the subspace is also a path homotopy F: I\<times>I \<rightarrow> X
     in the ambient space, since U \<subseteq> X and the subspace topology makes F continuous in X.\<close>
  have hf_path: "top1_is_path_on U TU x0 x1 f"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have hg_path: "top1_is_path_on U TU x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F
      \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s)
      \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x1)"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  then obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = x0" and hFr: "\<forall>t\<in>I_set. F (1, t) = x1"
    by (by100 auto)
  \<comment> \<open>F is continuous in X (subspace continuous \<Rightarrow> ambient continuous).\<close>
  have hF_cont_X: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "F p \<in> U" using hF_cont hp unfolding top1_continuous_map_on_def by (by100 blast)
    thus "F p \<in> X" using hUsub by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
    have "{p \<in> I_set \<times> I_set. F p \<in> V} = {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V}"
    proof (rule set_eqI)
      fix p show "(p \<in> {p \<in> I_set \<times> I_set. F p \<in> V}) = (p \<in> {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V})"
        using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    also have "\<dots> \<in> II_topology"
      using hF_cont hVU unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology" .
  qed
  have hf_path_X: "top1_is_path_on X TX x0 x1 f"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hf_cont_U: "top1_continuous_map_on I_set I_top U TU f"
      using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "f s \<in> X" using hf_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. f s \<in> V} = {s \<in> I_set. f s \<in> U \<inter> V}"
        using hf_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hf_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. f s \<in> V} \<in> I_top" .
    qed
    show "f 0 = x0" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "f 1 = x1" using hf_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  have hg_path_X: "top1_is_path_on X TX x0 x1 g"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hg_cont_U: "top1_continuous_map_on I_set I_top U TU g"
      using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "g s \<in> X" using hg_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> U \<inter> V}"
        using hg_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hg_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
    qed
    show "g 0 = x0" using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "g 1 = x1" using hg_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  show ?thesis unfolding top1_path_homotopic_on_def
    using hf_path_X hg_path_X hF_cont_X hF0 hF1 hFl hFr by (by100 blast)
qed

text \<open>Helper: a path in a subspace is a path in the ambient space.\<close>
lemma path_in_subspace_is_path_in_ambient:
  assumes hTX: "is_topology_on X TX" and hWX: "W \<subseteq> X"
      and hg: "top1_is_path_on W (subspace_topology X TX W) a b g"
  shows "top1_is_path_on X TX a b g"
  unfolding top1_is_path_on_def
proof (intro conjI)
  have hg_cont: "top1_continuous_map_on I_set I_top W (subspace_topology X TX W) g"
    using hg unfolding top1_is_path_on_def by (by100 blast)
  show "top1_continuous_map_on I_set I_top X TX g"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix s assume "s \<in> I_set"
    thus "g s \<in> X" using hg_cont hWX unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVW: "W \<inter> V \<in> subspace_topology X TX W"
      unfolding subspace_topology_def using hV by (by100 blast)
    have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> W \<inter> V}"
      using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
    also have "\<dots> \<in> I_top" using hg_cont hVW unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
  qed
  show "g 0 = a" using hg unfolding top1_is_path_on_def by (by100 blast)
  show "g 1 = b" using hg unfolding top1_is_path_on_def by (by100 blast)
qed

text \<open>Helper: union of path-connected open sets with nonempty path-connected intersection
  is path-connected.\<close>
lemma path_connected_union:
  assumes hTX: "is_topology_on X TX"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hUV: "U \<union> V = X" and hUsub: "U \<subseteq> X" and hVsub: "V \<subseteq> X"
      and hUV_ne: "U \<inter> V \<noteq> {}"
  shows "top1_path_connected_on X TX"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on X TX" by (rule hTX)
next
  fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
  \<comment> \<open>Case analysis: both in U, both in V, or one in each (join via U\<inter>V).\<close>
  show "\<exists>f. top1_is_path_on X TX x y f"
  proof (cases "x \<in> U \<and> y \<in> U")
    case True
    \<comment> \<open>Path in U, transfer to X via subspace inclusion.\<close>
    obtain f where hf: "top1_is_path_on U (subspace_topology X TX U) x y f"
      using hU_pc True unfolding top1_path_connected_on_def by (by100 auto)
    have "top1_is_path_on X TX x y f"
      by (rule path_in_subspace_is_path_in_ambient[OF hTX hUsub hf])
    thus ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>x \<notin> U \<or> y \<notin> U. Since x,y \<in> U\<union>V, the missing one is in V.
       Pick z \<in> U\<inter>V, path in U to/from z, path in V to/from z, concatenate.\<close>
    have hx_mem: "x \<in> U \<or> x \<in> V" and hy_mem: "y \<in> U \<or> y \<in> V"
      using hx hy hUV by (by100 blast)+
    \<comment> \<open>Get z \<in> U \<inter> V for joining paths.\<close>
    obtain z where hz: "z \<in> U \<inter> V" using hUV_ne by (by100 blast)
    \<comment> \<open>For any a \<in> U and b \<in> V, there's a path a\<rightarrow>z in U and z\<rightarrow>b in V in X.\<close>
    \<comment> \<open>Full proof requires path extraction from each subspace + transfer + concatenation.
       Follows the same pattern as the True case above.\<close>
    \<comment> \<open>Helper: get path in X between points in a path-connected subspace W.\<close>
    have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by (by100 blast)+
    \<comment> \<open>x is in U or V; get path x\<rightarrow>z in X.\<close>
    obtain g1 where hg1: "top1_is_path_on X TX x z g1"
    proof -
      have "\<exists>g. top1_is_path_on X TX x z g"
      proof (cases "x \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) x z g"
          using hU_pc True hzU unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "x \<in> V" using hx_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) x z g"
          using hV_pc \<open>x \<in> V\<close> hzV unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>y is in U or V; get path z\<rightarrow>y in X.\<close>
    obtain g2 where hg2: "top1_is_path_on X TX z y g2"
    proof -
      have "\<exists>g. top1_is_path_on X TX z y g"
      proof (cases "y \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) z y g"
          using hU_pc hzU True unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "y \<in> V" using hy_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) z y g"
          using hV_pc hzV \<open>y \<in> V\<close> unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Concatenate: x \<rightarrow> z \<rightarrow> y.\<close>
    have "top1_is_path_on X TX x y (top1_path_product g1 g2)"
      by (rule top1_path_product_is_path[OF hTX hg1 hg2])
    thus ?thesis by (by100 blast)
  qed
qed

text \<open>Helper: R with top1\_open\_sets is Hausdorff.\<close>
lemma top1_R_is_hausdorff:
  "is_hausdorff_on (UNIV :: real set) top1_open_sets"
proof -
  have hT: "is_topology_on (UNIV :: real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hH: "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). x \<noteq> y \<longrightarrow>
      (\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
             neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {})"
  proof (intro ballI impI)
    fix x y :: real assume "x \<in> UNIV" "y \<in> UNIV" "x \<noteq> y"
    show "\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
                neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {}"
    proof (cases "x < y")
      case True
      let ?m = "(x + y) / 2"
      have "{..<(?m::real)} \<in> {U. open U} \<and> x \<in> {..<(?m::real)}"
        using True by simp
      moreover have "{?m<..} \<in> {U. open U} \<and> y \<in> {?m<..}"
        using True by simp
      moreover have "{..<(?m::real)} \<inter> {?m<..} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    next
      case False
      hence "x > y" using \<open>x \<noteq> y\<close> by simp
      let ?m = "(x + y) / 2"
      have "{?m<..} \<in> {U. open U} \<and> x \<in> {?m<..}"
        using \<open>x > y\<close> by simp
      moreover have "{..<(?m::real)} \<in> {U. open U} \<and> y \<in> {..<(?m::real)}"
        using \<open>x > y\<close> by simp
      moreover have "{?m<..} \<inter> {..<(?m::real)} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    qed
  qed
  show ?thesis unfolding is_hausdorff_on_def using hT hH by (by100 blast)
qed

text \<open>Helper: R^2 with product topology is Hausdorff.\<close>
lemma top1_R2_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR by (by100 blast)
  thus ?thesis by simp
qed

text \<open>Helper: S^1 subspace is Hausdorff.\<close>
lemma top1_S1_is_hausdorff:
  "is_hausdorff_on top1_S1 top1_S1_topology"
proof -
  have "top1_S1 \<subseteq> (UNIV :: (real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S1_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R2_is_hausdorff by (by100 blast)
qed

text \<open>Helper: R^3 = R \<times> (R \<times> R) is Hausdorff.\<close>
lemma top1_R3_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real \<times> real) set)
     (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    by (rule top1_R2_is_hausdorff)
  have "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> (real \<times> real)) set)
      (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR hR2 by (by100 blast)
  thus ?thesis by simp
qed

text \<open>S^1 has strict topology.\<close>
lemma top1_S1_is_topology_on_strict:
  "is_topology_on_strict top1_S1 top1_S1_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
  show "top1_S1_topology \<subseteq> Pow top1_S1"
    unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>R^2 - {0} has strict topology.\<close>
lemma top1_R2_minus_0_is_topology_on_strict:
  "is_topology_on_strict (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on (UNIV - {(0::real, 0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  proof -
    have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using top1_R2_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) simp
  qed
  show "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})
      \<subseteq> Pow (UNIV - {(0::real, 0::real)})"
    unfolding subspace_topology_def by (by100 blast)
qed

text \<open>Helper: closed set has open complement.\<close>
lemma closedin_complement_openin:
  assumes "closedin_on X TX A"
  shows "openin_on X TX (X - A)"
  using assms unfolding closedin_on_def openin_on_def by (by100 blast)

text \<open>Helper: open set has closed complement.\<close>
lemma openin_complement_closedin:
  assumes "openin_on X TX A"
  shows "closedin_on X TX (X - A)"
proof -
  have hA: "A \<in> TX" and hAsub: "A \<subseteq> X"
    using assms unfolding openin_on_def by (by100 blast)+
  have "X - (X - A) = A" using hAsub by (by100 blast)
  thus ?thesis unfolding closedin_on_def using hA by (by100 simp)
qed


text \<open>Helper: if each loop in a list is nulhomotopic, their foldr product is nulhomotopic.\<close>
lemma foldr_path_product_nulhomotopic:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hnul: "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
  using hnul
proof (induction gs)
  case Nil
  have "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  thus ?case by (simp, rule Lemma_51_1_path_homotopic_refl)
next
  case (Cons g gs')
  have hg_nul: "top1_path_homotopic_on X TX x0 x0 g (top1_constant_path x0)"
    using Cons.prems by force
  have hgs'_nul: "\<forall>i < length gs'. top1_path_homotopic_on X TX x0 x0 (gs'!i) (top1_constant_path x0)"
    using Cons.prems by force
  have hrest_nul: "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs' (top1_constant_path x0)) (top1_constant_path x0)"
    by (rule Cons.IH[OF hgs'_nul])
  have hrest_path: "top1_is_path_on X TX x0 x0 (foldr top1_path_product gs' (top1_constant_path x0))"
    using hrest_nul unfolding top1_path_homotopic_on_def by (by100 blast)
  have step1: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))"
    by (rule path_homotopic_product_left[OF hTX hg_nul hrest_path])
  have step2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Theorem_51_2_left_identity[OF hTX hrest_path])
  have step12: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX step1 step2])
  show ?case
    by (simp, rule Lemma_51_1_path_homotopic_trans[OF hTX step12 hrest_nul])
qed

(** from \<S>59 Corollary 59.2: U, V open, simply connected, U \<inter> V path-connected
    and nonempty \<Longrightarrow> X = U \<union> V is simply connected. **)
corollary Corollary_59_2:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V \<noteq> {}"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_simply_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
  shows "top1_simply_connected_on X TX"
proof -
  \<comment> \<open>Munkres 59.2: By Thm 59.1, every loop decomposes into loops in U or V.
     U, V simply connected \<Rightarrow> each piece nulhomotopic \<Rightarrow> whole loop nulhomotopic.\<close>
  obtain x0 where hx0: "x0 \<in> U \<inter> V" using assms(5) by (by100 blast)
  \<comment> \<open>Step 1: X is path-connected (U, V path-connected via simply connected, joined via U\<inter>V).\<close>
  have hpc: "top1_path_connected_on X TX"
  proof -
    have hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      using assms(7) top1_simply_connected_on_path_connected by (by100 blast)
    have hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      using assms(8) top1_simply_connected_on_path_connected by (by100 blast)
    show ?thesis
      by (rule path_connected_union[OF is_topology_on_strict_imp[OF assms(1)]
            hU_pc hV_pc assms(6) assms(4) openin_on_sub[OF assms(2)] openin_on_sub[OF assms(3)] assms(5)])
  qed
  \<comment> \<open>Step 2: Every loop at x0 is nulhomotopic.\<close>
  have hnul: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
      top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX x0 f"
    \<comment> \<open>By Theorem 59.1, f decomposes into loops in U or V.\<close>
    obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
        and hgs: "\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
                      \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)"
        and hprod: "top1_path_homotopic_on X TX x0 x0 f
            (foldr top1_path_product gs (top1_constant_path x0))"
      using Theorem_59_1[OF assms(1,2,3,4,6) hx0] hf by blast
    \<comment> \<open>Each gi lies in U or V, hence is nulhomotopic there (simply connected).\<close>
    have hgi_nul: "\<forall>i<n. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
    proof (intro allI impI)
      fix i assume hi: "i < n"
      have hgi_loop: "top1_is_loop_on X TX x0 (gs!i)" using hgs hi by (by100 blast)
      have "gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V" using hgs hi by (by100 blast)
      \<comment> \<open>If in U: simply connected U \<Rightarrow> nulhomotopic in U \<Rightarrow> nulhomotopic in X.
         If in V: simply connected V \<Rightarrow> nulhomotopic in V \<Rightarrow> nulhomotopic in X.\<close>
      thus "top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
      proof
        assume hU_case: "gs!i ` I_set \<subseteq> U"
        \<comment> \<open>gs!i is a loop in U. U simply connected \<Rightarrow> nulhomotopic in U.\<close>
        have hgi_loop_U: "top1_is_loop_on U (subspace_topology X TX U) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> U" using hU_case .
          have hUsub: "U \<subseteq> X" using openin_on_sub[OF assms(2)] .
          have hcont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hUsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_U hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_U: "top1_path_homotopic_on U (subspace_topology X TX U) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0U: "x0 \<in> U" using hx0 by (by100 blast)
          show ?thesis using assms(7) hgi_loop_U hx0U
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_U])
             (rule openin_on_sub[OF assms(2)])
      next
        assume hV_case: "gs!i ` I_set \<subseteq> V"
        have hgi_loop_V: "top1_is_loop_on V (subspace_topology X TX V) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> V" using hV_case .
          have hVsub: "V \<subseteq> X" using openin_on_sub[OF assms(3)] .
          have hcont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hVsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_V hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_V: "top1_path_homotopic_on V (subspace_topology X TX V) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0V: "x0 \<in> V" using hx0 by (by100 blast)
          show ?thesis using assms(8) hgi_loop_V hx0V
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_V])
             (rule openin_on_sub[OF assms(3)])
      qed
    qed
    \<comment> \<open>Product of nulhomotopic loops is nulhomotopic.\<close>
    have hx0X: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
    have hTX_weak: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
    have "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
    proof -
      have "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
        using hgi_nul hlen by (by100 simp)
      thus ?thesis by (rule foldr_path_product_nulhomotopic[OF hTX_weak hx0X])
    qed
    \<comment> \<open>Transitivity: f \<simeq> product \<simeq> const.\<close>
    thus "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_trans[OF is_topology_on_strict_imp[OF assms(1)] hprod])
  qed
  \<comment> \<open>Assemble: path-connected + all loops at x0 nulhomotopic \<Rightarrow> simply connected.\<close>
  have hx0X_outer: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF
          is_topology_on_strict_imp[OF assms(1)] hpc hx0X_outer hnul])
qed

(** from \<S>59 Theorem 59.3: for n \<ge> 2, S^n is simply connected.

    Munkres' proof (2 steps):
    Step 1: S^n - p is homeomorphic to R^n via stereographic projection.
    Step 2: Apply Corollary 59.2 with U = S^n - p, V = S^n - q. **)
theorem Theorem_59_3:
  assumes "n \<ge> 2"
  shows "top1_simply_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
proof -
  let ?Sn = "top1_Sn n"
  let ?TSn = "subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?Sn"
  \<comment> \<open>Munkres 59.3: north pole p, south pole q.\<close>
  let ?p = "\<lambda>i::nat. if i = 0 then (1::real) else 0"
  let ?q = "\<lambda>i::nat. if i = 0 then (-1::real) else 0"
  let ?U = "?Sn - {?p}" and ?V = "?Sn - {?q}"
  \<comment> \<open>Step 1: U = S^n - {p} \<cong> R^n via stereographic projection, hence simply connected.\<close>
  have hU_sc: "top1_simply_connected_on ?U (subspace_topology ?Sn ?TSn ?U)" sorry
  have hV_sc: "top1_simply_connected_on ?V (subspace_topology ?Sn ?TSn ?V)" sorry
  \<comment> \<open>Step 2: U, V are open in S^n.\<close>
  \<comment> \<open>U = S^n - {p} and V = S^n - {q} are open because {p}, {q} are closed in S^n
     (Hausdorff + singleton closed).\<close>
  \<comment> \<open>S^n is Hausdorff (subspace of Hausdorff product). Singletons are closed, so complements are open.\<close>
  have hProd_haus: "is_hausdorff_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    by (rule Theorem_19_4_product) (simp add: top1_R_is_hausdorff)
  have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
  have hProd_haus_UNIV: "is_hausdorff_on (UNIV :: (nat \<Rightarrow> real) set)
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    using hProd_haus unfolding hPiE_eq .
  have hSn_sub_UNIV: "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by simp
  have hSn_haus: "is_hausdorff_on ?Sn ?TSn"
    using conjunct2[OF conjunct2[OF Theorem_17_11]] hProd_haus_UNIV hSn_sub_UNIV by (by100 blast)
  have hp_in_Sn: "?p \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?p i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?p i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) simp_all
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?p i)\<^sup>2) = 1" .
  qed
  have hq_in_Sn: "?q \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?q i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?q i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) (simp_all add: power2_eq_square)
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?q i)\<^sup>2) = 1" .
  qed
  have hp_closed: "closedin_on ?Sn ?TSn {?p}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hp_in_Sn])
  have hq_closed: "closedin_on ?Sn ?TSn {?q}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hq_in_Sn])
  have hU_open: "openin_on ?Sn ?TSn ?U"
    by (rule closedin_complement_openin[OF hp_closed])
  have hV_open: "openin_on ?Sn ?TSn ?V"
    by (rule closedin_complement_openin[OF hq_closed])
  \<comment> \<open>U \<union> V = S^n (every point of S^n differs from p or q).\<close>
  have hpq_ne: "?p \<noteq> ?q"
  proof -
    have "?p 0 = (1::real)" by simp
    moreover have "?q 0 = (-1::real)" by simp
    ultimately show ?thesis by (metis one_neq_neg_one)
  qed
  have hUV: "?U \<union> ?V = ?Sn" using hpq_ne by (by100 blast)
  \<comment> \<open>U \<inter> V = S^n - {p, q} is path-connected for n \<ge> 2.\<close>
  have hUV_ne: "?U \<inter> ?V \<noteq> {}"
  proof -
    \<comment> \<open>The point with x(1)=1 and x(i)=0 otherwise is in S^n (for n\<ge>2) and differs from p,q.\<close>
    let ?r = "\<lambda>i::nat. if i = 1 then (1::real) else 0"
    have hr_Sn: "?r \<in> ?Sn" unfolding top1_Sn_def
    proof (intro CollectI conjI allI impI)
      fix i :: nat assume "i \<ge> Suc n"
      hence "i \<noteq> 1" using assms by linarith
      thus "?r i = 0" by simp
    next
      have h1n: "(1::nat) \<le> n" using assms by linarith
      have "(\<Sum>i\<le>n. (?r i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 1 then 1 else (0::real)))"
      proof (rule sum.cong)
        fix i assume "i \<in> {..n}"
        show "(?r i)\<^sup>2 = (if i = 1 then 1 else 0)" by simp
      qed simp
      also have "\<dots> = 1"
      proof -
        have hfin: "finite ({..n}::nat set)" by simp
        have "(\<Sum>i\<le>n. (if i = (1::nat) then (1::real) else 0))
            = (if (1::nat) \<in> {..n} then 1 else 0)"
          using sum.delta'[OF hfin, of 1 "\<lambda>_. 1::real"] by simp
        also have "\<dots> = 1" using h1n by simp
        finally show ?thesis .
      qed
      finally show "(\<Sum>i\<le>n. (?r i)\<^sup>2) = 1" .
    qed
    have hr_ne_p: "?r \<noteq> ?p"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?p 0 = (1::real)" by simp
      ultimately show ?thesis by (metis zero_neq_one)
    qed
    have hr_ne_q: "?r \<noteq> ?q"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?q 0 = (-1::real)" by simp
      ultimately show ?thesis by (metis neg_0_equal_iff_equal zero_neq_one)
    qed
    have "?r \<in> ?U \<inter> ?V" using hr_Sn hr_ne_p hr_ne_q by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?Sn ?TSn (?U \<inter> ?V))" sorry
  have hT_strict: "is_topology_on_strict ?Sn ?TSn"
    unfolding is_topology_on_strict_def
  proof (intro conjI)
    have hTop_each: "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      using top1_open_sets_is_topology_on_UNIV by simp
    have hTop_prod: "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
      by (rule top1_product_topology_on_is_topology_on[OF hTop_each])
    have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
    have hTop_UNIV: "is_topology_on (UNIV :: (nat \<Rightarrow> real) set)
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
      using hTop_prod unfolding hPiE_eq .
    show "is_topology_on ?Sn ?TSn"
      by (rule subspace_topology_is_topology_on[OF hTop_UNIV]) simp
    show "?TSn \<subseteq> Pow ?Sn"
      unfolding subspace_topology_def by (by100 blast)
  qed
  \<comment> \<open>Apply Corollary 59.2.\<close>
  show ?thesis
    using Corollary_59_2[OF hT_strict hU_open hV_open hUV hUV_ne hUV_pc hU_sc hV_sc] by (by100 blast)
qed

corollary Theorem_59_3_path_connected:
  assumes "n \<ge> 2"
  shows "top1_path_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
  using Theorem_59_3[OF assms] top1_simply_connected_on_path_connected by blast

section \<open>\<S>60 Fundamental Groups of Some Surfaces\<close>

(** from \<S>60 Theorem 60.1: \<pi>_1(X \<times> Y, (x_0, y_0)) \<cong> \<pi>_1(X, x_0) \<times> \<pi>_1(Y, y_0).
    The iso is given by the product map induced by the two projections. **)
theorem Theorem_60_1_product:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
      and "x0 \<in> X" and "y0 \<in> Y"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           (top1_fundamental_group_mul (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           ((top1_fundamental_group_carrier X TX x0) \<times>
            (top1_fundamental_group_carrier Y TY y0))
           (\<lambda>(c1, c2) (d1, d2).
              (top1_fundamental_group_mul X TX x0 c1 d1,
               top1_fundamental_group_mul Y TY y0 c2 d2))"
  \<comment> \<open>Munkres 60.1: \<Phi>([f]) = (p_*([f]), q_*([f])) = ([p\<circ>f], [q\<circ>f]) where p,q are projections.\<close>
proof -
  let ?TXY = "product_topology_on TX TY"
  let ?\<Phi> = "\<lambda>c. (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c,
                  top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c)"
  \<comment> \<open>Step 1: \<Phi> is well-defined and a homomorphism.\<close>
  have hTX: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
  have hTY: "is_topology_on Y TY" by (rule is_topology_on_strict_imp[OF assms(2)])
  have hpi1_eq: "(pi1 :: ('a \<times> 'b) \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 :: ('a \<times> 'b) \<Rightarrow> 'b) = snd" unfolding pi2_def by (rule ext) simp
  have hfst_cont: "top1_continuous_map_on (X \<times> Y) ?TXY X TX fst"
    using top1_continuous_pi1[OF hTX hTY] unfolding hpi1_eq .
  have hsnd_cont: "top1_continuous_map_on (X \<times> Y) ?TXY Y TY snd"
    using top1_continuous_pi2[OF hTX hTY] unfolding hpi2_eq .
  have h\<Phi>_hom: "\<forall>c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      \<forall>d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      ?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
           top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)" sorry
  \<comment> \<open>Step 2: Injectivity. If p\<circ>f \<simeq> const and q\<circ>f \<simeq> const, combine homotopies componentwise.\<close>
  have h\<Phi>_inj: "inj_on ?\<Phi> (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))" sorry
  \<comment> \<open>Step 3: Surjectivity. Given [g] \<in> \<pi>_1(X) and [h] \<in> \<pi>_1(Y), define f(s) = (g(s), h(s)).\<close>
  have h\<Phi>_surj: "?\<Phi> ` (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
      = (top1_fundamental_group_carrier X TX x0) \<times>
        (top1_fundamental_group_carrier Y TY y0)" sorry
  \<comment> \<open>Assemble: \<Phi> is a group isomorphism.\<close>
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)
        (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2))
        ?\<Phi>"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> c \<in> top1_fundamental_group_carrier X TX x0 \<times>
            top1_fundamental_group_carrier Y TY y0"
        using h\<Phi>_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
          and hd: "d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d) =
          (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)"
        using h\<Phi>_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?\<Phi>
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)"
      unfolding bij_betw_def using h\<Phi>_inj h\<Phi>_surj by (by100 blast)
  qed
qed

section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>

text \<open>The 2-sphere S^2 as a subspace of R^3.\<close>
definition top1_S2 :: "(real \<times> real \<times> real) set" where
  "top1_S2 = {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"

definition top1_S2_topology :: "(real \<times> real \<times> real) set set" where
  "top1_S2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets
       (product_topology_on top1_open_sets top1_open_sets)) top1_S2"

text \<open>S^2 is Hausdorff (subspace of Hausdorff R^3).\<close>
lemma top1_S2_is_hausdorff:
  "is_hausdorff_on top1_S2 top1_S2_topology"
proof -
  have "top1_S2 \<subseteq> (UNIV :: (real \<times> real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S2_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R3_is_hausdorff by (by100 blast)
qed

text \<open>S^2 has strict topology.\<close>
lemma top1_S2_is_topology_on_strict:
  "is_topology_on_strict top1_S2 top1_S2_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S2 top1_S2_topology"
  proof -
    have hR3: "is_topology_on (UNIV :: (real \<times> real \<times> real) set)
        (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
      using top1_R3_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    show ?thesis unfolding top1_S2_topology_def
      by (rule subspace_topology_is_topology_on[OF hR3]) simp
  qed
  show "top1_S2_topology \<subseteq> Pow top1_S2"
    unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>A set C separates a space X if X - C has more than one component.\<close>
definition top1_separates_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_separates_on X TX C \<longleftrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"

lemma top1_separates_on_def_expand:
  "top1_separates_on X TX C \<Longrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"
  unfolding top1_separates_on_def by blast

lemma top1_separates_onI:
  "\<not> top1_connected_on (X - C) (subspace_topology X TX (X - C)) \<Longrightarrow>
    top1_separates_on X TX C"
  unfolding top1_separates_on_def by (by100 blast)

(** from \<S>61 Lemma 61.1: unbounded/bounded components of R^2-h(C) correspond to
    S^2-b components under a homeomorphism h: S^2-b \<rightarrow> R^2.
    If U is a component of S^2 - C not containing b, then h(U) is a BOUNDED
    component of R^2 - h(C). If U contains b, then h(U - {b}) is the UNBOUNDED
    component of R^2 - h(C). **)
lemma Lemma_61_1_components_correspond:
  fixes h :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real)" and C :: "(real \<times> real \<times> real) set"
    and b :: "real \<times> real \<times> real" and U :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "C \<subseteq> top1_S2"
      and "top1_compact_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and "b \<in> top1_S2 - C"
      and "top1_homeomorphism_on (top1_S2 - {b})
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) h"
      and "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      and "U \<subseteq> top1_S2 - C"
  shows "(b \<notin> U \<longrightarrow> (\<exists>M. \<forall>x\<in>U. fst (h x) ^ 2 + snd (h x) ^ 2 \<le> M))
       \<and> (b \<in> U \<longrightarrow> (\<forall>M. \<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M))"
proof -
  \<comment> \<open>Munkres 61.1: h maps components of S^2-C to components of R^2-h(C).
     Step 1: h(C) is compact (continuous image of compact), hence bounded in R^2.
     Step 2: Components of S^2-C not containing b map to bounded components of R^2-h(C)
     (since h|_{S^2-b} is a homeomorphism, connected components correspond).
     Step 3: The component containing b maps to the complement of a bounded set,
     which is unbounded.\<close>
  have hC_compact: "top1_compact_on (h ` (C - {b}))
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` (C - {b})))" sorry
  have hC_bounded: "\<exists>M. \<forall>p \<in> h ` (C - {b}). fst p ^ 2 + snd p ^ 2 \<le> M" sorry
  show ?thesis sorry
qed

(** from \<S>61 Lemma 61.2 (Nulhomotopy lemma): any continuous map from a compact
    space A into S^2 - b whose image factors through an arc is nulhomotopic. **)
lemma Lemma_61_2_nulhomotopy:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and b :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_compact_on A TA"
      and "b \<in> top1_S2"
      and "top1_continuous_map_on A TA
             (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
      and "\<exists>D. D \<subseteq> top1_S2 - {b} \<and> f ` A \<subseteq> D
            \<and> (\<exists>\<gamma>. top1_continuous_map_on I_set I_top D
                     (subspace_topology top1_S2 top1_S2_topology D) \<gamma>
                  \<and> inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D)"
             \<comment> \<open>f factors through an arc D\<close>
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
proof -
  \<comment> \<open>Munkres 61.2: f factors through an arc D \<subseteq> S^2-{b}.
     Step 1: An arc D is homeomorphic to [0,1], which is convex.
     Step 2: Any map into a convex set is nulhomotopic (straight-line homotopy).
     Step 3: S^2-{b} \<cong> R^2 (stereographic projection), so the nulhomotopy transfers.\<close>
  obtain D where hD: "D \<subseteq> top1_S2 - {b}" and hfD: "f ` A \<subseteq> D"
      and "\<exists>\<gamma>. inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D"
    using assms(5) by (by100 auto)
  \<comment> \<open>D is contractible (homeomorphic to [0,1]).\<close>
  have hD_contractible: "top1_simply_connected_on D
      (subspace_topology top1_S2 top1_S2_topology D)" sorry
  \<comment> \<open>f is nulhomotopic in D, hence in S^2-{b}.\<close>
  show ?thesis sorry
qed

(** from \<S>61 Theorem 61.3: Jordan separation theorem for S^2.

    Munkres' proof sketch:
    Suppose for contradiction S^2 - C is path connected.
    Write C = A_1 \<union> A_2 (arcs meeting at {a, b}).
    Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.
    Then X = U \<union> V and U \<inter> V = S^2 - C (path connected by assumption).
    By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.
    Using Lemma 61.2 (nulhomotopy), both i_* and j_* are trivial.
    So \<pi>_1(X, x_0) is trivial. But X \<cong> R^2 - {0} has nontrivial \<pi>_1. \<bottom> **)
theorem Theorem_61_3_JordanSeparation_S2:
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_separates_on top1_S2 top1_S2_topology C"
proof (rule ccontr)
  assume hnot: "\<not> top1_separates_on top1_S2 top1_S2_topology C"
  \<comment> \<open>Negation: S^2 - C is connected.\<close>
  have hS2_C_connected: "top1_connected_on (top1_S2 - C)
                           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
    using hnot unfolding top1_separates_on_def by blast
  \<comment> \<open>Decompose C = A_1 \<union> A_2 (two arcs) with common endpoints a, b.\<close>
  obtain A1 A2 a b where hC_decomp: "C = A1 \<union> A2"
      and hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
      and hA1_arc: "top1_is_arc_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
      and hA2_arc: "top1_is_arc_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
    using hC sorry
  \<comment> \<open>Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.\<close>
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - C (path-connected by hypothesis).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hC_decomp hab by blast
  have hUV_eq: "?U \<inter> ?V = top1_S2 - C" using hC_decomp hab by blast
  \<comment> \<open>U, V are open in X.\<close>
  have hU_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?U" sorry
  have hV_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?V" sorry
  \<comment> \<open>U \<inter> V = S^2 - C is path-connected (connected + locally path-connected).\<close>
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V))" sorry
  obtain x0 where hx0: "x0 \<in> ?U \<inter> ?V" sorry
  \<comment> \<open>By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.\<close>
  \<comment> \<open>By Lemma 61.2 (nulhomotopy), every loop in U factors through A2 (an arc),
     hence is nulhomotopic. Similarly for V. So i_*, j_* are trivial.\<close>
  have h_pi1_X_trivial: "top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)" sorry
  \<comment> \<open>But X = S^2 - {a, b} \<cong> R^2 - {0} which has nontrivial \<pi>_1.\<close>
  have h_pi1_X_nontrivial: "\<not> top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)" sorry
  show False using h_pi1_X_trivial h_pi1_X_nontrivial by contradiction
qed

(** from \<S>61 Theorem 61.4: general separation theorem for S^2 **)
theorem Theorem_61_4_general_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "A1 \<subseteq> top1_S2" and "A2 \<subseteq> top1_S2"
  and "closedin_on top1_S2 top1_S2_topology A1"
  and "closedin_on top1_S2 top1_S2_topology A2"
  and "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
  and "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
  and "card (A1 \<inter> A2) = 2"
  shows "top1_separates_on top1_S2 top1_S2_topology (A1 \<union> A2)"
proof -
  \<comment> \<open>Munkres 61.4: Write C=A1\<union>A2 with A1\<inter>A2={a,b}.
     X = S^2-{a,b} \<cong> R^2-{0}, U = S^2-A1, V = S^2-A2. X=U\<union>V.\<close>
  obtain a b where hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
    using assms(8) card_2_iff by (by100 metis)
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - (A1 \<union> A2).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hab by (by100 blast)
  have hUV_eq: "?U \<inter> ?V = top1_S2 - (A1 \<union> A2)" by (by100 blast)
  \<comment> \<open>If S^2 - (A1\<union>A2) were connected, then U\<inter>V would be path-connected.\<close>
  \<comment> \<open>By Lemma 61.2, loops in U and V are nulhomotopic (they factor through arcs).\<close>
  \<comment> \<open>So \<pi>_1(X) would be trivial. But X \<cong> R^2-{0} has nontrivial \<pi>_1. Contradiction.\<close>
  \<comment> \<open>Hence S^2 - (A1 \<union> A2) is NOT connected.\<close>
  show ?thesis unfolding top1_separates_on_def sorry
qed

section \<open>*\<S>62 Invariance of Domain\<close>

text \<open>Invariance of domain in R^2: an open injective continuous map R^2 \<rightarrow> R^2
  has open image, and its invgerse is continuous.\<close>

(** from *\<S>62 Theorem 62.3: Invariance of Domain in R^2. **)
theorem Theorem_62_3_invgariance_of_domain:
  fixes U :: "(real \<times> real) set" and f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes "U \<in> product_topology_on top1_open_sets top1_open_sets"
      and "top1_continuous_map_on U
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
             UNIV (product_topology_on top1_open_sets top1_open_sets) f"
      and "inj_on f U"
  shows "f ` U \<in> product_topology_on top1_open_sets top1_open_sets"
proof -
  \<comment> \<open>Munkres 62.3: For x\<in>U, show f(x)\<in>Int(f(U)).
     Step 1: Take a closed ball B centered at x with B \<subseteq> U.
     Step 2: f|B is injective continuous on compact B; f(Bd B) is a simple closed
     curve in R^2 (since Bd B \<cong> S^1 and f is injective on it).
     Step 3: By the Jordan Separation Theorem (61.3), f(Bd B) separates R^2.
     Step 4: f(x) is in the bounded component W of R^2 - f(Bd B).
     Step 5: W \<subseteq> f(Int B) \<subseteq> f(U), so f(x) \<in> Int(f(U)).\<close>
  have "\<forall>x\<in>U. \<exists>W. x \<in> W \<and> W \<in> product_topology_on top1_open_sets top1_open_sets \<and> W \<subseteq> f ` U"
  proof
    fix x assume hx: "x \<in> U"
    \<comment> \<open>Step 1: Take closed ball B with x \<in> Int(B) \<subseteq> B \<subseteq> U.\<close>
    obtain B where hBsub: "B \<subseteq> U"
        and hB_compact: "top1_compact_on B (subspace_topology UNIV
            (product_topology_on top1_open_sets top1_open_sets) B)"
        and hx_int: "x \<in> B - frontier B"
        and hBd_S1: "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
            (frontier B) (subspace_topology UNIV
              (product_topology_on top1_open_sets top1_open_sets) (frontier B)) h"
      sorry
    \<comment> \<open>Step 2: f(Bd B) is a simple closed curve (f injective on compact Bd B \<cong> S^1).\<close>
    have hfBd_curve: "top1_simple_closed_curve_on UNIV
        (product_topology_on top1_open_sets top1_open_sets) (f ` frontier B)" sorry
    \<comment> \<open>Step 3: By Jordan Curve Theorem, f(Bd B) separates R^2 into two components.\<close>
    obtain W1 W2 where hW_disj: "W1 \<inter> W2 = {}" and hW_union: "W1 \<union> W2 = UNIV - f ` frontier B"
        and hW1_ne: "W1 \<noteq> {}" and hW2_ne: "W2 \<noteq> {}"
        and hW1_open: "W1 \<in> product_topology_on top1_open_sets top1_open_sets"
      sorry \<comment> \<open>By Jordan Curve Theorem (Theorem 63.4).\<close>
    \<comment> \<open>Step 4: f(x) is in the bounded component.\<close>
    have hfx_in_W: "f x \<in> W1" sorry
    \<comment> \<open>Step 5: W1 \<subseteq> f(Int B) \<subseteq> f(U).\<close>
    have hW1_sub: "W1 \<subseteq> f ` U" sorry
    show "\<exists>W. x \<in> W \<and> W \<in> product_topology_on top1_open_sets top1_open_sets \<and> W \<subseteq> f ` U"
      sorry
  qed
  show ?thesis sorry
qed

section \<open>\<S>63 The Jordan Curve Theorem\<close>

text \<open>A simple closed curve in X: image of a continuous injective map S^1 \<rightarrow> X.\<close>
definition top1_simple_closed_curve_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_simple_closed_curve_on X TX C \<longleftrightarrow>
     (\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<and> inj_on f top1_S1
          \<and> f ` top1_S1 = C)"

(** from \<S>63 Theorem 63.1: if X = U \<union> V with U \<inter> V = A \<union> B (disjoint open),
    and alpha: a to b in U, beta: b to a in V, then the loop f = alpha * beta is
    nontrivial in pi_1(X, a) (plus further properties: homotopy lifts, f^m and f^k
    are nonconjugate when the components are different). Used in Munkres' proof of
    the Jordan Curve Theorem. **)
theorem Theorem_63_1_loop_nontrivial:
  assumes "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
  shows "\<not> top1_path_homotopic_on X TX a a
           (top1_path_product alpha beta) (top1_constant_path a)"
proof
  assume hnul: "top1_path_homotopic_on X TX a a
      (top1_path_product alpha beta) (top1_constant_path a)"
  \<comment> \<open>Munkres 63.1: Construct covering space p: E \<rightarrow> X as infinite helix.
     E = ... \<sqcup> U_0 \<sqcup> V_0 \<sqcup> U_1 \<sqcup> V_1 \<sqcup> ... with A-sheets and B-sheets glued alternately.
     Concretely: E = Z \<times> (U \<sqcup> V), identifying (n, A-point in V_n) with (n, A-point in U_n)
     and (n, B-point in U_n) with (n+1, B-point in V_n).\<close>
  \<comment> \<open>Step 1: Build the covering space E and covering map p: E \<rightarrow> X.\<close>
  have "\<exists>(E::'a set) TE (p0::'a \<Rightarrow> 'a).
      top1_covering_map_on E TE X TX p0
    \<and> (\<exists>e0\<in>E. p0 e0 = a)" sorry
  \<comment> \<open>Step 2: Lift f = \<alpha>*\<beta> starting at e0 in the covering. The lift of \<alpha> goes from
     sheet n to the same sheet; the lift of \<beta> shifts from sheet n to sheet n+1.
     So the lifted path ends at a point in a DIFFERENT sheet than it started.\<close>
  have "\<exists>(E::'a set) TE (p0::'a \<Rightarrow> 'a) e0 e1.
      top1_covering_map_on E TE X TX p0
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> e1 \<in> E \<and> p0 e1 = a
    \<and> e0 \<noteq> e1
    \<and> (\<exists>ftilde. top1_is_path_on E TE e0 e1 ftilde
        \<and> (\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s))" sorry
  \<comment> \<open>Step 3: If f were nulhomotopic, the lift would be a loop (same start and end).
     But we showed the lift has different endpoints. Contradiction.\<close>
  show False sorry
qed

(** from \<S>63 Theorem 63.2: an arc D in S^2 does not separate S^2.
    Munkres' proof: by contradiction + Theorem 63.1; use that \<pi>_1(S^2) is trivial. **)
theorem Theorem_63_2_arc_no_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "D \<subseteq> top1_S2"
  and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology D"
proof (rule ccontr)
  assume hnot: "\<not> \<not> top1_separates_on top1_S2 top1_S2_topology D"
  hence hsep: "top1_separates_on top1_S2 top1_S2_topology D" by blast
  \<comment> \<open>Munkres 63.2: Split D=D1\<union>D2 at midpoint d.\<close>
  obtain d D1 D2 where hd: "d \<in> D" and hD: "D = D1 \<union> D2" and "D1 \<inter> D2 = {d}"
      and "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
      and "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
    sorry
  \<comment> \<open>Since D separates S^2, take a\<in>A, b\<in>B in different components of S^2-D.\<close>
  obtain a b where hab: "a \<in> top1_S2 - D" "b \<in> top1_S2 - D"
      and hab_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f)"
    using hsep sorry
  \<comment> \<open>X=S^2-{d}, U=S^2-D1, V=S^2-D2. Apply Theorem 63.1.\<close>
  \<comment> \<open>Get nontrivial element of \<pi>_1(X). But X\<cong>R^2 has trivial \<pi>_1. Contradiction.\<close>
  have h_pi1_trivial: "top1_simply_connected_on (top1_S2 - {d})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))" sorry
  have h_pi1_nontrivial: "\<not> top1_simply_connected_on (top1_S2 - {d})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))" sorry
  show False using h_pi1_trivial h_pi1_nontrivial by contradiction
qed

(** from \<S>63 Theorem 63.3: general non-separation theorem. **)
theorem Theorem_63_3_general_nonseparation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology D1"
  and "closedin_on top1_S2 top1_S2_topology D2"
  and "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D2"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
proof (rule ccontr)
  assume hnot: "\<not> \<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
  hence hsep: "top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)" by blast
  \<comment> \<open>Munkres 63.3: Take a\<in>A, b\<in>B in different components of S^2-(D1\<union>D2).\<close>
  obtain a b where "a \<in> top1_S2 - (D1 \<union> D2)" "b \<in> top1_S2 - (D1 \<union> D2)"
      and hab_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f)"
    using hsep sorry
  \<comment> \<open>Since D1 doesn't separate, join a to b in S^2-D1: path \<alpha>.\<close>
  obtain \<alpha> where "top1_is_path_on (top1_S2 - D1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>"
    using assms(5) sorry
  \<comment> \<open>Since D2 doesn't separate, join b to a in S^2-D2: path \<beta>.\<close>
  obtain \<beta> where "top1_is_path_on (top1_S2 - D2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>"
    using assms(6) sorry
  \<comment> \<open>The loop f = \<alpha>*\<beta> lies in X=S^2-(D1\<inter>D2). By Theorem 63.1, [f] is nontrivial.\<close>
  have hf_nontrivial: "\<exists>f. top1_is_loop_on (top1_S2 - (D1 \<inter> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a f
      \<and> \<not> top1_path_homotopic_on (top1_S2 - (D1 \<inter> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a a f
          (top1_constant_path a)" sorry
  \<comment> \<open>But S^2-(D1\<inter>D2) is simply connected by assumption. Contradiction.\<close>
  have ha_mem: "a \<in> top1_S2 - (D1 \<inter> D2)"
    using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  show False using hf_nontrivial assms(4) ha_mem
    unfolding top1_simply_connected_on_def by (by100 blast)
qed

(** from \<S>63 Theorem 63.4: Jordan Curve Theorem.

    Munkres' proof: use Theorem 61.3 (separation) + locally connected property +
    Theorem 63.1 argument to show at most 2 components. Each component has C as
    boundary by an auxiliary argument.

    NB: Currently stated for C \<subseteq> R^2 (as in the original formalization). **)
theorem Theorem_63_4_JordanCurve:
  fixes C :: "(real \<times> real) set"
  assumes "top1_simple_closed_curve_on
    UNIV (product_topology_on top1_open_sets top1_open_sets) C"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {}
    \<and> U \<inter> V = {} \<and> U \<union> V = UNIV - C
    \<and> top1_path_connected_on U
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
    \<and> top1_path_connected_on V
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) V)
    \<comment> \<open>One component is bounded (interior), the other unbounded (exterior).\<close>
    \<and> (\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M)
    \<and> (\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M)
    \<comment> \<open>Both components have C as boundary.\<close>
    \<and> closure U = U \<union> C
    \<and> closure V = V \<union> C"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets"
  \<comment> \<open>Step 1 (Separation): Transfer to S^2 via stereographic projection. C corresponds
     to a simple closed curve on S^2. By Theorem 61.3, S^2 - C' has \<ge> 2 components.\<close>
  have hC_sep: "\<not> top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))" sorry
  \<comment> \<open>Step 2 (Exactly two components): Decompose C = C_1 \<union> C_2 (two arcs with endpoints a, b).
     By Theorem 63.5 (applied via 63.2 + 63.3), exactly two components.\<close>
  obtain U V where hUV_ne: "U \<noteq> {}" "V \<noteq> {}" and hUV_disj: "U \<inter> V = {}"
      and hUV_cover: "U \<union> V = UNIV - C"
      and hU_conn: "top1_connected_on U (subspace_topology UNIV ?TR2 U)"
      and hV_conn: "top1_connected_on V (subspace_topology UNIV ?TR2 V)"
    sorry
  \<comment> \<open>Step 3 (Path-connected): R^2 is locally path-connected, so components are path-connected.\<close>
  have hU_pc: "top1_path_connected_on U (subspace_topology UNIV ?TR2 U)" sorry
  have hV_pc: "top1_path_connected_on V (subspace_topology UNIV ?TR2 V)" sorry
  \<comment> \<open>Step 4 (Bounded/unbounded): Under stereographic projection, one component maps to
     the bounded component and the other to the unbounded one (Lemma 61.1).\<close>
  have hU_bdd: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M" sorry
  have hV_unbdd: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M" sorry
  \<comment> \<open>Step 5 (Boundary = C): Both components have C as their common boundary.\<close>
  have hU_bdy: "closure U = U \<union> C" sorry
  have hV_bdy: "closure V = V \<union> C" sorry
  show ?thesis using hUV_ne hUV_disj hUV_cover hU_pc hV_pc hU_bdd hV_unbdd hU_bdy hV_bdy
    by blast
qed

(** from \<S>63 Theorem 63.5: two closed-connected sets C1, C2 with |C1\<inter>C2|=2 and neither separates S^2 imply C1\<union>C2 separates into exactly two components. **)
theorem Theorem_63_5_two_closed_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {}
    \<and> U \<union> V = top1_S2 - (C1 \<union> C2)
    \<and> top1_connected_on U
        (subspace_topology top1_S2 top1_S2_topology U)
    \<and> top1_connected_on V
        (subspace_topology top1_S2 top1_S2_topology V)"
proof -
  \<comment> \<open>Munkres 63.5: By Theorem 61.4, C1\<union>C2 separates S^2 (\<ge>2 components).
     To show exactly 2: use Theorem 63.1. If there were 3+ components,
     one could construct two independent nontrivial elements in \<pi>_1(S^2-{p,q})
     (where C1\<inter>C2 = {p,q}), but \<pi>_1(S^2-{p,q}) \<cong> Z has only one generator.
     So exactly 2 components.\<close>
  have hsep: "top1_separates_on top1_S2 top1_S2_topology (C1 \<union> C2)"
  proof -
    have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by blast
    have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by blast
    show ?thesis
      by (rule Theorem_61_4_general_separation[OF assms(1) hC1sub hC2sub assms(2,3,4,5,6)])
  qed
  \<comment> \<open>At least two components from separation.\<close>
  \<comment> \<open>At most two: \<pi>_1(S^2-{a,b}) \<cong> Z can distinguish at most 2 components via Theorem 63.1.\<close>
  show ?thesis sorry
qed

section \<open>\<S>65 The Winding Number of a Simple Closed Curve\<close>

text \<open>The winding number of a loop f in R^2-{0} around the origin.
  Munkres' definition: lift the loop (cos 2\<pi>t, sin 2\<pi>t)-valued normalization
  f/|f| to a path \<tilde>f in R via the covering p: R \<rightarrow> S^1, p(x) = (cos 2\<pi>x, sin 2\<pi>x),
  and define winding number = \<tilde>f(1) - \<tilde>f(0). This is an integer since f is a loop.\<close>
definition top1_winding_number_on ::
  "(real \<Rightarrow> real \<times> real) \<Rightarrow> int" where
  "top1_winding_number_on f =
     (SOME n::int.
        \<exists>ftilde. top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets ftilde
              \<and> (\<forall>s\<in>I_set. top1_R_to_S1 (ftilde s)
                   = (fst (f s) / sqrt (fst (f s)^2 + snd (f s)^2),
                      snd (f s) / sqrt (fst (f s)^2 + snd (f s)^2)))
              \<and> n = \<lfloor>ftilde 1 - ftilde 0\<rfloor>)"

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
  \<comment> \<open>Step 1: X = U \<union> V and U \<inter> V has two components A, B.\<close>
  have hUV: "?U \<union> ?V = ?X" sorry
  have hUV_components: "\<exists>A B. A \<inter> B = {} \<and> A \<union> B = ?U \<inter> ?V \<and> A \<noteq> {} \<and> B \<noteq> {}" sorry
  \<comment> \<open>Step 2: The path \<alpha> (a1→a2 via e12) lies in U, the path \<beta> (a2→a3 via e23) lies in V.
     By Theorem 63.1, the loop \<alpha>*\<beta> is nontrivial in X.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U (subspace_topology top1_S2 top1_S2_topology ?U) x0 x0 \<alpha>"
    sorry
  \<comment> \<open>Step 3: f is homotopic to such a loop, hence nontrivial.\<close>
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
      (top1_fundamental_group_induced_on C ?TC c0 ?Xpq ?TXpq c0 (\<lambda>x. x))" sorry
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hj_hom hj_inj hj_surj unfolding bij_betw_def by (by100 blast)
qed

section \<open>Chapter 11: The Seifert-van Kampen Theorem\<close>

text \<open>Group-theoretic definitions are now in the earlier subsection before \<S>52.\<close>

lemma top1_groups_isomorphic_on_refl:
  assumes "top1_is_group_on G mul e invg"
  shows "top1_groups_isomorphic_on G mul G mul"
  unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
proof (intro exI conjI)
  show "top1_group_hom_on G mul G mul id"
    unfolding top1_group_hom_on_def by simp
  show "bij_betw id G G" by simp
qed

lemma top1_groups_isomorphic_on_sym:
  assumes hiso: "top1_groups_isomorphic_on G mulG H mulH"
      and hG: "top1_is_group_on G mulG eG invgG"
      and hH: "top1_is_group_on H mulH eH invgH"
  shows "top1_groups_isomorphic_on H mulH G mulG"
proof -
  obtain f where hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using hiso unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  have hinj: "inj_on f G" using hf_bij unfolding bij_betw_def by blast
  have hsurj: "f ` G = H" using hf_bij unfolding bij_betw_def by blast
  let ?g = "the_inv_into G f"
  have hg_mem: "\<forall>y\<in>H. ?g y \<in> G"
    using the_inv_into_into[OF hinj] hsurj by blast
  have hfg_id: "\<forall>y\<in>H. f (?g y) = y"
    using f_the_inv_into_f[OF hinj] hsurj by blast
  have hgf_id: "\<forall>x\<in>G. ?g (f x) = x"
    using the_inv_into_f_f[OF hinj] by blast
  have hg_bij: "bij_betw ?g H G"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on ?g H"
    proof (rule inj_onI)
      fix y1 y2 assume "y1 \<in> H" "y2 \<in> H" "?g y1 = ?g y2"
      hence "f (?g y1) = f (?g y2)" by simp
      thus "y1 = y2" using hfg_id \<open>y1 \<in> H\<close> \<open>y2 \<in> H\<close> by simp
    qed
    show "?g ` H = G"
    proof
      show "?g ` H \<subseteq> G" using hg_mem by blast
      show "G \<subseteq> ?g ` H"
      proof
        fix x assume hx: "x \<in> G"
        have hfx: "f x \<in> H" using hsurj hx by blast
        have "?g (f x) = x" using hgf_id hx by blast
        thus "x \<in> ?g ` H" using hfx by force
      qed
    qed
  qed
  have hmul_cl: "\<forall>y1\<in>H. \<forall>y2\<in>H. mulH y1 y2 \<in> H"
    using hH unfolding top1_is_group_on_def by blast
  have hmulG_cl: "\<forall>x1\<in>G. \<forall>x2\<in>G. mulG x1 x2 \<in> G"
    using hG unfolding top1_is_group_on_def by blast
  have hg_hom: "top1_group_hom_on H mulH G mulG ?g"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix y assume "y \<in> H" thus "?g y \<in> G" using hg_mem by blast
  next
    fix y1 y2 assume hy1: "y1 \<in> H" and hy2: "y2 \<in> H"
    have hgy1: "?g y1 \<in> G" and hgy2: "?g y2 \<in> G" using hg_mem hy1 hy2 by blast+
    have hmul_H: "mulH y1 y2 \<in> H" using hmul_cl hy1 hy2 by blast
    have "f (?g (mulH y1 y2)) = mulH y1 y2" using hfg_id hmul_H by blast
    also have "... = mulH (f (?g y1)) (f (?g y2))" using hfg_id hy1 hy2 by simp
    also have "... = f (mulG (?g y1) (?g y2))"
    proof -
      have "f (mulG (?g y1) (?g y2)) = mulH (f (?g y1)) (f (?g y2))"
        using hf_hom hgy1 hgy2 unfolding top1_group_hom_on_def by blast
      thus ?thesis by (rule sym)
    qed
    finally have "f (?g (mulH y1 y2)) = f (mulG (?g y1) (?g y2))" .
    moreover have "?g (mulH y1 y2) \<in> G" using hg_mem hmul_H by blast
    moreover have "mulG (?g y1) (?g y2) \<in> G" using hmulG_cl hgy1 hgy2 by blast
    ultimately show "?g (mulH y1 y2) = mulG (?g y1) (?g y2)"
      using hinj by (meson inj_on_eq_iff)
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hg_hom hg_bij by blast
qed

lemma top1_groups_isomorphic_on_trans:
  assumes hGH: "top1_groups_isomorphic_on G mulG H mulH"
      and hHK: "top1_groups_isomorphic_on H mulH K mulK"
  shows "top1_groups_isomorphic_on G mulG K mulK"
proof -
  obtain f where hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using hGH unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  obtain g where hg_hom: "top1_group_hom_on H mulH K mulK g" and hg_bij: "bij_betw g H K"
    using hHK unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by blast
  have hgf_hom: "top1_group_hom_on G mulG K mulK (g \<circ> f)"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume hx: "x \<in> G"
    have "f x \<in> H" using hf_hom hx unfolding top1_group_hom_on_def by blast
    thus "(g \<circ> f) x \<in> K" using hg_hom unfolding top1_group_hom_on_def comp_def by blast
  next
    fix x y assume hx: "x \<in> G" and hy: "y \<in> G"
    have "f x \<in> H" "f y \<in> H" using hf_hom hx hy unfolding top1_group_hom_on_def by blast+
    have "(g \<circ> f) (mulG x y) = g (f (mulG x y))" by simp
    also have "... = g (mulH (f x) (f y))"
    proof -
      have "f (mulG x y) = mulH (f x) (f y)"
        using hf_hom hx hy unfolding top1_group_hom_on_def by blast
      thus ?thesis by simp
    qed
    also have "... = mulK (g (f x)) (g (f y))"
      using hg_hom \<open>f x \<in> H\<close> \<open>f y \<in> H\<close> unfolding top1_group_hom_on_def by blast
    also have "... = mulK ((g \<circ> f) x) ((g \<circ> f) y)" by simp
    finally show "(g \<circ> f) (mulG x y) = mulK ((g \<circ> f) x) ((g \<circ> f) y)" .
  qed
  have hgf_bij: "bij_betw (g \<circ> f) G K" by (rule bij_betw_trans[OF hf_bij hg_bij])
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hgf_hom hgf_bij by blast
qed

text \<open>Normal subgroup: N \<subseteq> G is a subgroup closed under conjugation.\<close>
definition top1_normal_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> bool" where
  "top1_normal_subgroup_on G mul e invg N \<longleftrightarrow>
     N \<subseteq> G \<and>
     top1_is_group_on N mul e invg \<and>
     (\<forall>g\<in>G. \<forall>n\<in>N. mul (mul g n) (invg g) \<in> N)"

text \<open>Kernel of a homomorphism is a normal subgroup.\<close>
definition top1_group_kernel_on ::
  "'g set \<Rightarrow> 'h \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'g set" where
  "top1_group_kernel_on G eH f = {x\<in>G. f x = eH}"

text \<open>Image of a group under a homomorphism.\<close>
definition top1_group_image_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'h set" where
  "top1_group_image_on G f = f ` G"

text \<open>Quotient group G/N: cosets g N under the product (gN)(hN) = (gh)N.
  Modelled as a set of equivalence classes.\<close>
definition top1_group_coset_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_group_coset_on G mul N g = {mul g n | n. n \<in> N}"

definition top1_quotient_group_carrier_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "top1_quotient_group_carrier_on G mul N = {top1_group_coset_on G mul N g | g. g \<in> G}"

text \<open>Multiplication on cosets: (gN)(hN) = (gh)N, computed as set product.\<close>
definition top1_quotient_group_mul_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_quotient_group_mul_on mul C1 C2 = {mul g h | g h. g \<in> C1 \<and> h \<in> C2}"

text \<open>Iterated product in a group (g * g * ... * g, n times).\<close>
fun top1_group_pow :: "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> nat \<Rightarrow> 'g" where
  "top1_group_pow mul e x 0 = e"
| "top1_group_pow mul e x (Suc n) = mul x (top1_group_pow mul e x n)"

text \<open>Product of a word in (G \<union> G\<inverse>): each letter is (g, b) where b=True means g
  contributes g to the product, and b=False means invg(g) contributes. For an empty
  word the result is the identity e.\<close>
fun top1_group_word_product ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('g \<times> bool) list \<Rightarrow> 'g" where
  "top1_group_word_product mul e invg [] = e"
| "top1_group_word_product mul e invg ((x, True) # ws)
     = mul x (top1_group_word_product mul e invg ws)"
| "top1_group_word_product mul e invg ((x, False) # ws)
     = mul (invg x) (top1_group_word_product mul e invg ws)"

text \<open>A word in ('g \<times> bool) list is reduced if no adjacent pair (x, b) (x, \<not>b) appears
  (which would represent x \<cdot> x\<inverse> or x\<inverse> \<cdot> x, cancelling to e).\<close>
fun top1_is_reduced_word ::
  "('g \<times> bool) list \<Rightarrow> bool" where
  "top1_is_reduced_word [] = True"
| "top1_is_reduced_word [_] = True"
| "top1_is_reduced_word ((x, b) # (y, c) # ws)
     = ((x \<noteq> y \<or> b = c) \<and> top1_is_reduced_word ((y, c) # ws))"

text \<open>Subgroup generated by a subset S \<subseteq> G.\<close>
definition top1_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_subgroup_generated_on G mul e invg S =
     \<Inter> { H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg }"

definition top1_normal_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normal_subgroup_generated_on G mul e invg S =
     \<Inter> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"

text \<open>Free group on a set S: a group F(S) with \<iota>: S \<hookrightarrow> F(S) such that:
  (1) \<iota> is injective,
  (2) \<iota>(S) generates F(S), and
  (3) no non-empty reduced word in \<iota>(S) \<union> \<iota>(S)\<inverse> equals e (the freeness condition).
  Together, (2)+(3) are equivalent to the universal extension property.\<close>
definition top1_is_free_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>ws :: ('s \<times> bool) list.
        ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws!i) \<in> S) \<longrightarrow>
        top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e)"

text \<open>External universal property for free groups: for a specific test type,
  any function S \<rightarrow> H extends uniquely to a homomorphism G \<rightarrow> H.\<close>
definition top1_free_group_universal_prop ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow>
   'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_free_group_universal_prop G mul \<iota> S H mulH eH invgH \<phi> \<longleftrightarrow>
     top1_is_group_on H mulH eH invgH \<and> (\<forall>s\<in>S. \<phi> s \<in> H) \<longrightarrow>
     (\<exists>!\<psi>. top1_group_hom_on G mul H mulH \<psi>
        \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s))"

text \<open>Free abelian group on a set S: abelian group G together with \<iota>: S \<hookrightarrow> G such that
  (1) \<iota> is injective, (2) \<iota>(S) generates G, and
  (3) no non-trivial finitely-supported integer combination of \<iota>(S) equals e.
  Condition (3) is the abelian freeness: for any nonzero c : S \<rightarrow> int with finite
  support, the product over s of \<iota>(s) raised to c(s) is not e.\<close>
definition top1_is_free_abelian_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_abelian_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_abelian_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>c :: 's \<Rightarrow> int.
        finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mul (map (\<lambda>s.
            if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
          (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e
        \<noteq> e)"

text \<open>Group presentation: G is presented by generators S modulo relations R.
  Relations are reduced words in S \<union> S\<inverse> (type ('s \<times> bool) list, as for free groups).
  G \<cong> F(S)/\<langle>\<langle>R\<rangle>\<rangle> means: there is a free group F on S and a surjective homomorphism
  \<pi>: F \<rightarrow> G whose kernel is the normal subgroup of F generated by the images of
  the relator words (computed via top1_group_word_product).\<close>
definition top1_group_presented_by_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g)
   \<Rightarrow> 's set \<Rightarrow> (('s \<times> bool) list set) \<Rightarrow> bool" where
  "top1_group_presented_by_on G mul e invg S R \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<exists>(F::'g set) mulF eF invgF \<iota> \<pi>.
        top1_is_free_group_full_on F mulF eF invgF \<iota> S
      \<and> top1_group_hom_on F mulF G mul \<pi>
      \<and> \<pi> ` F = G
      \<and> top1_group_kernel_on F e \<pi>
           = top1_normal_subgroup_generated_on F mulF eF invgF
               {r. \<exists>w\<in>R. r = top1_group_word_product mulF eF invgF
                            (map (\<lambda>(s, b). (\<iota> s, b)) w)})"

text \<open>Free product of a family of groups (Munkres §68): a group (G, mul, e, invg)
  with injective homomorphisms \<iota>_\<alpha>: G_\<alpha> \<hookrightarrow> G (one per index \<alpha>\<in>J), such that:
  (1) the images \<iota>_\<alpha>(G_\<alpha>) generate G, and
  (2) any non-empty reduced product of elements (alternating between different
      \<iota>_\<alpha>(G_\<alpha>\<setminus>{e_\<alpha>})) is not the identity of G.
  The last conjunct encodes (2): word = list of (index, element) pairs where
  each element differs from its group's identity and consecutive indices differ;
  its product in G is not e.\<close>
definition top1_is_free_product_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'gg set) \<Rightarrow> ('i \<Rightarrow> 'gg \<Rightarrow> 'gg \<Rightarrow> 'gg) \<Rightarrow>
   ('i \<Rightarrow> 'gg \<Rightarrow> 'g) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G) \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
        \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)) \<and>
     G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<and>
     (\<forall>indices word.
        length indices = length word \<longrightarrow>
        length indices > 0 \<longrightarrow>
        (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
        (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
        foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e)"

text \<open>The cyclic group Z/nZ with modular addition.\<close>
definition top1_Zn_group :: "nat \<Rightarrow> int set" where
  "top1_Zn_group n = {0..<int n}"

definition top1_Zn_mul :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_mul n a b = (a + b) mod int n"

definition top1_Zn_id :: "int" where
  "top1_Zn_id = 0"

definition top1_Zn_invg :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_invg n a = (int n - a) mod int n"

lemma top1_Zn_is_abelian_group:
  assumes hn: "n \<ge> 1"
  shows "top1_is_abelian_group_on (top1_Zn_group n) (top1_Zn_mul n) top1_Zn_id (top1_Zn_invg n)"
proof -
  have hn_pos: "int n > 0" using hn by simp
  show ?thesis
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def
              top1_Zn_group_def top1_Zn_mul_def top1_Zn_id_def top1_Zn_invg_def
  proof (intro conjI ballI)
    show "(0::int) \<in> {0..<int n}" using hn by simp
  next
    fix x y assume "x \<in> {0::int..<int n}" "y \<in> {0::int..<int n}"
    thus "(x + y) mod int n \<in> {0..<int n}" using hn_pos by simp
  next
    fix x assume "x \<in> {0::int..<int n}"
    thus "(int n - x) mod int n \<in> {0..<int n}" using hn_pos by simp
  next
    fix x y z assume hx: "x \<in> {0::int..<int n}" and hy: "y \<in> {0::int..<int n}" and hz: "z \<in> {0::int..<int n}"
    show "((x + y) mod int n + z) mod int n = (x + (y + z) mod int n) mod int n"
      by (simp add: mod_add_left_eq mod_add_right_eq add.assoc)
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    hence hx0: "0 \<le> x" and hxn: "x < int n" by auto
    show "(0 + x) mod int n = x" using hx0 hxn by simp
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    hence hx0: "0 \<le> x" and hxn: "x < int n" by auto
    show "(x + 0) mod int n = x" using hx0 hxn by simp
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    show "((int n - x) mod int n + x) mod int n = 0"
      using hx hn_pos by (simp add: mod_add_left_eq)
  next
    fix x assume hx: "x \<in> {0::int..<int n}"
    show "(x + (int n - x) mod int n) mod int n = 0"
      using hx hn_pos by (simp add: mod_add_right_eq)
  next
    fix x y assume "x \<in> {0::int..<int n}" "y \<in> {0::int..<int n}"
    show "(x + y) mod int n = (y + x) mod int n" by (simp add: add.commute)
  qed
qed

text \<open>The torsion subgroup of an abelian group.\<close>
definition top1_torsion_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_torsion_subgroup_on G mul e =
     {x\<in>G. \<exists>n. n > 0 \<and> top1_group_pow mul e x n = e}"

text \<open>Commutator [a, b] = a b a\<inverse> b\<inverse> in a group.\<close>
definition top1_group_commutator_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g" where
  "top1_group_commutator_on mul invg a b = mul (mul (mul a b) (invg a)) (invg b)"

text \<open>The commutator subgroup [G, G] generated by all commutators [a, b].\<close>
definition top1_commutator_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set" where
  "top1_commutator_subgroup_on G mul e invg =
     top1_subgroup_generated_on G mul e invg
       { top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"

text \<open>Normalizer of H in G: N(H) = {g \<in> G | gHg\<inverse> = H}.\<close>
definition top1_normalizer_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normalizer_on G mul invg H =
     {g \<in> G. {mul (mul g h) (invg g) | h. h \<in> H} = H}"

text \<open>H is the abelianization of G: H = G/[G, G] with the induced abelian structure.
  Equivalently, H is an abelian group together with a surjective homomorphism
  \<phi>: G \<rightarrow> H whose kernel is [G, G] (the commutator subgroup).\<close>
definition top1_is_abelianization_of ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi> \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     top1_is_group_on G mul e invg \<and>
     top1_group_hom_on G mul H mulH \<phi> \<and>
     \<phi> ` G = H \<and>
     top1_group_kernel_on G eH \<phi> = top1_commutator_subgroup_on G mul e invg"

section \<open>\<S>67 Direct Sums of Abelian Groups\<close>

text \<open>External direct sum: the set of finitely-supported functions J \<rightarrow> \<Union>G_\<alpha>.\<close>
text \<open>External direct sum: the set of finitely-supported functions f : J \<rightarrow> \<Union>_\<alpha> G_\<alpha>
  with f \<alpha> \<in> G_\<alpha> and f \<alpha> = e_\<alpha> (the identity of G_\<alpha>) for all but finitely many \<alpha>.\<close>
definition top1_direct_sum_carrier ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g) set" where
  "top1_direct_sum_carrier J G eFam =
     {f. (\<forall>i\<in>J. f i \<in> G i) \<and> (\<forall>i. i \<notin> J \<longrightarrow> f i = eFam i) \<and>
         finite {i\<in>J. f i \<noteq> eFam i}}"

text \<open>H is an (internal) direct sum of the abelian groups {G_\<alpha>}_{\<alpha>\<in>J} along
  injections \<iota>fam_\<alpha>: G_\<alpha> \<hookrightarrow> H iff H is abelian and the natural map from the
  external direct sum to H (sending f to the finite product \<Prod>_\<alpha> \<iota>fam_\<alpha>(f \<alpha>))
  is a group isomorphism whose restriction to the \<alpha>-th 'axis' is \<iota>fam_\<alpha>.\<close>
definition top1_is_direct_sum_of_on ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_direct_sum_of_on H mulH eH invgH J G mulG eG \<iota>fam \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mulG \<alpha>) H mulH (\<iota>fam \<alpha>)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>)) \<and>
     (\<exists>\<Phi>. top1_group_iso_on
            (top1_direct_sum_carrier J G eG)
            (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mulG \<alpha> (f \<alpha>) (g \<alpha>) else eG \<alpha>)
            H mulH \<Phi>
          \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<Phi> (\<lambda>\<beta>. if \<beta> = \<alpha> then x else eG \<beta>) = \<iota>fam \<alpha> x))"

lemma top1_direct_sum_carrier_mul_closed:
  assumes "\<forall>\<alpha>\<in>J. top1_is_abelian_group_on (G \<alpha>) (mul \<alpha>) (e \<alpha>) (invg \<alpha>)"
      and "f \<in> top1_direct_sum_carrier J G e" and "g \<in> top1_direct_sum_carrier J G e"
  shows "(\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) \<in> top1_direct_sum_carrier J G e"
proof -
  have hfm: "\<forall>\<alpha>\<in>J. f \<alpha> \<in> G \<alpha>" and hgm: "\<forall>\<alpha>\<in>J. g \<alpha> \<in> G \<alpha>"
    using assms(2,3) unfolding top1_direct_sum_carrier_def by blast+
  have hff: "finite {i \<in> J. f i \<noteq> e i}" and hgf: "finite {i \<in> J. g i \<noteq> e i}"
    using assms(2,3) unfolding top1_direct_sum_carrier_def by auto
  let ?h = "\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>"
  show ?thesis unfolding top1_direct_sum_carrier_def
  proof (intro CollectI conjI)
    show "\<forall>i\<in>J. ?h i \<in> G i"
      using hfm hgm assms(1) unfolding top1_is_abelian_group_on_def top1_is_group_on_def by simp
    show "\<forall>i. i \<notin> J \<longrightarrow> ?h i = e i" by simp
    show "finite {i \<in> J. ?h i \<noteq> e i}"
    proof -
      have "{i \<in> J. ?h i \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
      proof
        fix i assume "i \<in> {i \<in> J. ?h i \<noteq> e i}"
        hence hi: "i \<in> J" and hne: "mul i (f i) (g i) \<noteq> e i" by auto
        show "i \<in> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "f i = e i" "g i = e i" using hi by auto
          hence "mul i (f i) (g i) = mul i (e i) (e i)" by simp
          also have "... = e i"
            using assms(1) hi unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
          finally show False using hne by contradiction
        qed
      qed
      thus ?thesis using finite_subset hff hgf by blast
    qed
  qed
qed

(** from \<S>67 Theorem 67.4: existence of external direct sum of abelian groups.
    The direct sum (finitely-supported coordinate-wise functions) is an abelian group,
    equipped with natural injections \<iota>fam_\<alpha> : G_\<alpha> \<hookrightarrow> \<oplus>_\<alpha> G_\<alpha>. **)
theorem Theorem_67_4_direct_sum_exists:
  assumes hG: "\<forall>\<alpha>\<in>(J::'i set). top1_is_abelian_group_on (G \<alpha>::'g set) (mul \<alpha>) (e \<alpha>) (invg \<alpha>)"
  shows "\<exists>\<iota>fam.
           top1_is_abelian_group_on
             (top1_direct_sum_carrier J G e)
             (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>)
             e
             (\<lambda>f. \<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>)
         \<and> (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mul \<alpha>)
               (top1_direct_sum_carrier J G e)
               (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>)
               (\<iota>fam \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<iota>fam \<alpha> x \<alpha> = x \<and>
              (\<forall>\<beta>. \<beta> \<noteq> \<alpha> \<longrightarrow> \<iota>fam \<alpha> x \<beta> = e \<beta>))"
proof -
  \<comment> \<open>Natural axis injection: \<iota>_\<alpha>(x) is the function with value x at \<alpha> and e(\<beta>) elsewhere.\<close>
  let ?\<iota> = "\<lambda>\<alpha> x. \<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>"
  let ?DS = "top1_direct_sum_carrier J G e"
  let ?mulDS = "\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>"
  let ?invDS = "\<lambda>f. \<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>"
  have hGprops: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> e \<alpha> \<in> G \<alpha>"
               "\<And>\<alpha> x y. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x y \<in> G \<alpha>"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> invg \<alpha> x \<in> G \<alpha>"
               "\<And>\<alpha> x y z. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>; z \<in> G \<alpha>\<rbrakk>
                  \<Longrightarrow> mul \<alpha> (mul \<alpha> x y) z = mul \<alpha> x (mul \<alpha> y z)"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> (e \<alpha>) x = x"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x (e \<alpha>) = x"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> (invg \<alpha> x) x = e \<alpha>"
               "\<And>\<alpha> x. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x (invg \<alpha> x) = e \<alpha>"
               "\<And>\<alpha> x y. \<lbrakk>\<alpha> \<in> J; x \<in> G \<alpha>; y \<in> G \<alpha>\<rbrakk> \<Longrightarrow> mul \<alpha> x y = mul \<alpha> y x"
    using hG unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast+
  have hDS_mem: "\<And>f. f \<in> ?DS \<Longrightarrow> (\<forall>\<alpha>\<in>J. f \<alpha> \<in> G \<alpha>)"
    unfolding top1_direct_sum_carrier_def by blast
  have hDS_out: "\<And>f. f \<in> ?DS \<Longrightarrow> (\<forall>\<alpha>. \<alpha> \<notin> J \<longrightarrow> f \<alpha> = e \<alpha>)"
    unfolding top1_direct_sum_carrier_def by blast
  have he_DS: "e \<in> ?DS"
    unfolding top1_direct_sum_carrier_def
  proof (intro CollectI conjI)
    show "\<forall>i\<in>J. e i \<in> G i" using hGprops(1) by blast
    show "\<forall>i. i \<notin> J \<longrightarrow> e i = e i" by simp
    show "finite {i \<in> J. e i \<noteq> e i}" by simp
  qed
  have hmul_cl: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. ?mulDS x y \<in> ?DS"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS"
    show "?mulDS f g \<in> ?DS"
      unfolding top1_direct_sum_carrier_def
    proof (intro CollectI conjI)
      show "\<forall>i\<in>J. (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i \<in> G i"
        using hDS_mem[OF hf] hDS_mem[OF hg] hGprops(2) by simp
      show "\<forall>i. i \<notin> J \<longrightarrow> (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i = e i"
        by simp
      show "finite {i \<in> J. (\<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>) i \<noteq> e i}"
      proof -
        have "{i \<in> J. mul i (f i) (g i) \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
        proof
          fix i assume "i \<in> {i \<in> J. mul i (f i) (g i) \<noteq> e i}"
          hence hi: "i \<in> J" and hne: "mul i (f i) (g i) \<noteq> e i" by auto
          show "i \<in> {i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "f i = e i" "g i = e i" using hi by auto
            hence "mul i (f i) (g i) = mul i (e i) (e i)" by simp
            also have "... = e i" using hGprops(5) hi hGprops(1) by blast
            finally show False using hne by contradiction
          qed
        qed
        moreover have "finite ({i \<in> J. f i \<noteq> e i} \<union> {i \<in> J. g i \<noteq> e i})"
          using hf hg unfolding top1_direct_sum_carrier_def by auto
        ultimately have hfin: "finite {i \<in> J. mul i (f i) (g i) \<noteq> e i}"
          using finite_subset by blast
        have "{i. (i \<in> J \<longrightarrow> mul i (f i) (g i) \<noteq> e i) \<and> i \<in> J}
              = {i \<in> J. mul i (f i) (g i) \<noteq> e i}" by auto
        then show ?thesis using hfin by simp
      qed
    qed
  qed
  have hinvg_e: "\<And>i. i \<in> J \<Longrightarrow> invg i (e i) = e i"
  proof -
    fix i assume hi: "i \<in> J"
    have "mul i (invg i (e i)) (e i) = e i" using hGprops(7) hi hGprops(1) by blast
    moreover have "mul i (e i) (e i) = e i" using hGprops(5) hi hGprops(1) by blast
    moreover have "invg i (e i) \<in> G i" using hGprops(3) hi hGprops(1) by blast
    moreover have "e i \<in> G i" using hGprops(1) hi by blast
    ultimately show "invg i (e i) = e i"
      using hGprops(6) hi by force
  qed
  have hinv_cl: "\<forall>x\<in>?DS. ?invDS x \<in> ?DS"
  proof (intro ballI)
    fix f assume hf: "f \<in> ?DS"
    show "?invDS f \<in> ?DS"
      unfolding top1_direct_sum_carrier_def
    proof (intro CollectI conjI)
      show "\<forall>i\<in>J. (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i \<in> G i"
        using hDS_mem[OF hf] hGprops(3) by simp
      show "\<forall>i. i \<notin> J \<longrightarrow> (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i = e i"
        by simp
      show "finite {i \<in> J. (\<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>) i \<noteq> e i}"
      proof -
        have "{i \<in> J. invg i (f i) \<noteq> e i} \<subseteq> {i \<in> J. f i \<noteq> e i}"
        proof
          fix i assume "i \<in> {i \<in> J. invg i (f i) \<noteq> e i}"
          hence hi: "i \<in> J" and hne: "invg i (f i) \<noteq> e i" by auto
          show "i \<in> {i \<in> J. f i \<noteq> e i}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "f i = e i" using hi by simp
            hence "invg i (f i) = invg i (e i)" by simp
            also have "... = e i" using hinvg_e hi by blast
            finally show False using hne by contradiction
          qed
        qed
        moreover have "finite {i \<in> J. f i \<noteq> e i}"
          using hf unfolding top1_direct_sum_carrier_def by auto
        ultimately have hfin: "finite {i \<in> J. invg i (f i) \<noteq> e i}"
          using finite_subset by blast
        have "{i. (i \<in> J \<longrightarrow> invg i (f i) \<noteq> e i) \<and> i \<in> J}
              = {i \<in> J. invg i (f i) \<noteq> e i}" by auto
        then show ?thesis using hfin by simp
      qed
    qed
  qed
  have hassoc: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. \<forall>z\<in>?DS.
    ?mulDS (?mulDS x y) z = ?mulDS x (?mulDS y z)"
  proof (intro ballI)
    fix f g h assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS" and hh: "h \<in> ?DS"
    show "?mulDS (?mulDS f g) h = ?mulDS f (?mulDS g h)"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS (?mulDS f g) h \<alpha> = ?mulDS f (?mulDS g h) \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        hence "?mulDS (?mulDS f g) h \<alpha> = mul \<alpha> (mul \<alpha> (f \<alpha>) (g \<alpha>)) (h \<alpha>)" by simp
        also have "... = mul \<alpha> (f \<alpha>) (mul \<alpha> (g \<alpha>) (h \<alpha>))"
          using hGprops(4) True hDS_mem[OF hf] hDS_mem[OF hg] hDS_mem[OF hh] by blast
        also have "... = ?mulDS f (?mulDS g h) \<alpha>" using True by simp
        finally show ?thesis .
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have hid: "\<forall>x\<in>?DS. ?mulDS e x = x \<and> ?mulDS x e = x"
  proof (intro ballI conjI)
    fix f assume hf: "f \<in> ?DS"
    show "?mulDS e f = f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS e f \<alpha> = f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(5) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis using hDS_out[OF hf] by simp
      qed
    qed
    show "?mulDS f e = f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f e \<alpha> = f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(6) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis using hDS_out[OF hf] by simp
      qed
    qed
  qed
  have hinv_ax: "\<forall>x\<in>?DS. ?mulDS (?invDS x) x = e \<and> ?mulDS x (?invDS x) = e"
  proof (intro ballI conjI)
    fix f assume hf: "f \<in> ?DS"
    show "?mulDS (?invDS f) f = e"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS (?invDS f) f \<alpha> = e \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(7) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
    show "?mulDS f (?invDS f) = e"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f (?invDS f) \<alpha> = e \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(8) hDS_mem[OF hf] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have hcomm: "\<forall>x\<in>?DS. \<forall>y\<in>?DS. ?mulDS x y = ?mulDS y x"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?DS" and hg: "g \<in> ?DS"
    show "?mulDS f g = ?mulDS g f"
    proof (rule ext)
      fix \<alpha>
      show "?mulDS f g \<alpha> = ?mulDS g f \<alpha>"
      proof (cases "\<alpha> \<in> J")
        case True
        thus ?thesis using hGprops(9) hDS_mem[OF hf] hDS_mem[OF hg] by simp
      next
        case False thus ?thesis by simp
      qed
    qed
  qed
  have habel: "top1_is_abelian_group_on ?DS ?mulDS e ?invDS"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def
    using he_DS hmul_cl hinv_cl hassoc hid hinv_ax hcomm by argo
  have hhom: "\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mul \<alpha>)
               (top1_direct_sum_carrier J G e)
               (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>)
               (?\<iota> \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "top1_group_hom_on (G \<alpha>) (mul \<alpha>) (top1_direct_sum_carrier J G e)
           (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>) (?\<iota> \<alpha>)"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> G \<alpha>"
      show "?\<iota> \<alpha> x \<in> top1_direct_sum_carrier J G e"
        unfolding top1_direct_sum_carrier_def
      proof (intro CollectI conjI)
        show "\<forall>i\<in>J. (?\<iota> \<alpha> x) i \<in> G i"
        proof
          fix i assume "i \<in> J"
          show "(?\<iota> \<alpha> x) i \<in> G i"
          proof (cases "i = \<alpha>")
            case True thus ?thesis using hx by simp
          next
            case False
            have "e i \<in> G i" using \<open>i \<in> J\<close> hG
              unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
            moreover have "(?\<iota> \<alpha> x) i = e i" using False by simp
            ultimately show ?thesis by simp
          qed
        qed
        show "\<forall>i. i \<notin> J \<longrightarrow> (?\<iota> \<alpha> x) i = e i"
        proof (intro allI impI)
          fix i assume "i \<notin> J"
          hence "i \<noteq> \<alpha>" using h\<alpha> by blast
          thus "(?\<iota> \<alpha> x) i = e i" by simp
        qed
        show "finite {i \<in> J. (?\<iota> \<alpha> x) i \<noteq> e i}"
        proof -
          have "{i \<in> J. (?\<iota> \<alpha> x) i \<noteq> e i} \<subseteq> {\<alpha>}" by auto
          thus ?thesis using finite_subset by blast
        qed
      qed
    next
      fix x y assume hx: "x \<in> G \<alpha>" and hy: "y \<in> G \<alpha>"
      show "?\<iota> \<alpha> (mul \<alpha> x y) = (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>) (?\<iota> \<alpha> x) (?\<iota> \<alpha> y)"
      proof (rule ext)
        fix \<beta>
        show "?\<iota> \<alpha> (mul \<alpha> x y) \<beta> = (\<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> ((?\<iota> \<alpha> x) \<beta>) ((?\<iota> \<alpha> y) \<beta>) else e \<beta>) \<beta>"
        proof (cases "\<beta> = \<alpha>")
          case True thus ?thesis using h\<alpha> by simp
        next
          case False
          hence lhs: "?\<iota> \<alpha> (mul \<alpha> x y) \<beta> = e \<beta>" by simp
          have "(?\<iota> \<alpha> x) \<beta> = e \<beta>" "(?\<iota> \<alpha> y) \<beta> = e \<beta>" using False by simp_all
          hence rhs: "(\<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> ((?\<iota> \<alpha> x) \<beta>) ((?\<iota> \<alpha> y) \<beta>) else e \<beta>) \<beta>
                     = (if \<beta> \<in> J then mul \<beta> (e \<beta>) (e \<beta>) else e \<beta>)" by simp
          show ?thesis
          proof (cases "\<beta> \<in> J")
            case True
            hence "mul \<beta> (e \<beta>) (e \<beta>) = e \<beta>"
              using hG unfolding top1_is_abelian_group_on_def top1_is_group_on_def by blast
            thus ?thesis using lhs rhs True by simp
          next
            case False thus ?thesis using lhs rhs by simp
          qed
        qed
      qed
    qed
  qed
  have hinj: "\<forall>\<alpha>\<in>J. inj_on (?\<iota> \<alpha>) (G \<alpha>)"
  proof (intro ballI)
    fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
    show "inj_on (?\<iota> \<alpha>) (G \<alpha>)"
    proof (rule inj_onI)
      fix x y assume "x \<in> G \<alpha>" "y \<in> G \<alpha>" "?\<iota> \<alpha> x = ?\<iota> \<alpha> y"
      hence "(\<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>) = (\<lambda>\<beta>. if \<beta> = \<alpha> then y else e \<beta>)" by simp
      hence "(\<lambda>\<beta>. if \<beta> = \<alpha> then x else e \<beta>) \<alpha> = (\<lambda>\<beta>. if \<beta> = \<alpha> then y else e \<beta>) \<alpha>"
        by (rule fun_cong)
      thus "x = y" by simp
    qed
  qed
  have haxis: "\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. ?\<iota> \<alpha> x \<alpha> = x \<and> (\<forall>\<beta>. \<beta> \<noteq> \<alpha> \<longrightarrow> ?\<iota> \<alpha> x \<beta> = e \<beta>)"
    by simp
  show ?thesis
    apply (intro exI[where x = ?\<iota>] conjI)
       apply (rule habel)
      using hhom apply blast
     using hinj apply blast
    using haxis apply blast
    done
qed

(** from \<S>67 Theorem 67.6: uniqueness of external direct sum.
    If (H_1, \<iota>_1) and (H_2, \<iota>_2) are both direct sums of a family {G_\<alpha>}_{\<alpha>\<in>J} of
    abelian groups (with injective homomorphisms \<iota>_i_\<alpha>: G_\<alpha> \<rightarrow> H_i making H_i the
    internal direct sum of their images), then H_1 \<cong> H_2 as abelian groups. **)
theorem Theorem_67_6_direct_sum_unique:
  fixes J :: "'i set"
    and G :: "'i \<Rightarrow> 'g set" and mul :: "'i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and eG :: "'i \<Rightarrow> 'g" and invgG :: "'i \<Rightarrow> 'g \<Rightarrow> 'g"
    and H1 H2 :: "'h set" and mulH1 mulH2 :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH1 eH2 :: 'h and invgH1 invgH2 :: "'h \<Rightarrow> 'h"
    and \<iota>fam1 \<iota>fam2 :: "'i \<Rightarrow> 'g \<Rightarrow> 'h"
  assumes hG: "\<forall>\<alpha>\<in>J. top1_is_abelian_group_on (G \<alpha>) (mul \<alpha>) (eG \<alpha>) (invgG \<alpha>)"
      and "top1_is_direct_sum_of_on H1 mulH1 eH1 invgH1 J G mul eG \<iota>fam1"
      and "top1_is_direct_sum_of_on H2 mulH2 eH2 invgH2 J G mul eG \<iota>fam2"
  shows "top1_groups_isomorphic_on H1 mulH1 H2 mulH2"
proof -
  let ?DS = "top1_direct_sum_carrier J G eG"
  let ?mulDS = "\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else eG \<alpha>"
  obtain \<Phi>1 where h\<Phi>1: "top1_group_iso_on ?DS ?mulDS H1 mulH1 \<Phi>1"
    using assms(2) unfolding top1_is_direct_sum_of_on_def by blast
  obtain \<Phi>2 where h\<Phi>2: "top1_group_iso_on ?DS ?mulDS H2 mulH2 \<Phi>2"
    using assms(3) unfolding top1_is_direct_sum_of_on_def by blast
  have hiso1: "top1_groups_isomorphic_on ?DS ?mulDS H1 mulH1"
    unfolding top1_groups_isomorphic_on_def using h\<Phi>1 by blast
  have hiso2: "top1_groups_isomorphic_on ?DS ?mulDS H2 mulH2"
    unfolding top1_groups_isomorphic_on_def using h\<Phi>2 by blast
  \<comment> \<open>H1 \<cong> DS \<cong> H2 by transitivity and symmetry.\<close>
  \<comment> \<open>Both Φ₁, Φ₂ are bijective homs DS → H_i. Construct Φ₂ ∘ Φ₁⁻¹ : H₁ → H₂.\<close>
  have hH1_group: "top1_is_group_on H1 mulH1 eH1 invgH1"
    using assms(2) unfolding top1_is_direct_sum_of_on_def top1_is_abelian_group_on_def by blast
  have hH2_group: "top1_is_group_on H2 mulH2 eH2 invgH2"
    using assms(3) unfolding top1_is_direct_sum_of_on_def top1_is_abelian_group_on_def by blast
  have hbij1: "bij_betw \<Phi>1 ?DS H1" and hhom1: "top1_group_hom_on ?DS ?mulDS H1 mulH1 \<Phi>1"
    using h\<Phi>1 unfolding top1_group_iso_on_def by blast+
  have hbij2: "bij_betw \<Phi>2 ?DS H2" and hhom2: "top1_group_hom_on ?DS ?mulDS H2 mulH2 \<Phi>2"
    using h\<Phi>2 unfolding top1_group_iso_on_def by blast+
  \<comment> \<open>Φ₁ inverse.\<close>
  have hinj1: "inj_on \<Phi>1 ?DS" using hbij1 unfolding bij_betw_def by blast
  let ?\<Psi> = "\<lambda>h. \<Phi>2 (the_inv_into ?DS \<Phi>1 h)"
  have hbij_inv1: "bij_betw (the_inv_into ?DS \<Phi>1) H1 ?DS"
    by (rule bij_betw_the_inv_into[OF hbij1])
  have hbij_comp: "bij_betw (\<Phi>2 \<circ> the_inv_into ?DS \<Phi>1) H1 H2"
    by (rule bij_betw_trans[OF hbij_inv1 hbij2])
  have hpsi_eq: "?\<Psi> = \<Phi>2 \<circ> the_inv_into ?DS \<Phi>1" by (rule ext) (simp add: comp_def)
  have hbij_psi: "bij_betw ?\<Psi> H1 H2"
    using hbij_comp unfolding hpsi_eq[symmetric] .
  have hhom_psi: "top1_group_hom_on H1 mulH1 H2 mulH2 ?\<Psi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x assume hx: "x \<in> H1"
    have "the_inv_into ?DS \<Phi>1 x \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hx unfolding bij_betw_def by blast
    thus "?\<Psi> x \<in> H2"
      using hhom2 unfolding top1_group_hom_on_def by blast
  next
    fix x y assume hx: "x \<in> H1" and hy: "y \<in> H1"
    have hxDS: "the_inv_into ?DS \<Phi>1 x \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hx unfolding bij_betw_def by blast
    have hyDS: "the_inv_into ?DS \<Phi>1 y \<in> ?DS"
      using the_inv_into_into[OF hinj1] hbij1 hy unfolding bij_betw_def by blast
    have hsurj1: "\<Phi>1 ` ?DS = H1" using hbij1 unfolding bij_betw_def by blast
    \<comment> \<open>\<Phi>₁(inv(x) * inv(y)) = \<Phi>₁(inv(x)) * \<Phi>₁(inv(y)) = x * y.\<close>
    have hprod: "\<Phi>1 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y)) = mulH1 x y"
    proof -
      have "\<Phi>1 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y))
            = mulH1 (\<Phi>1 (the_inv_into ?DS \<Phi>1 x)) (\<Phi>1 (the_inv_into ?DS \<Phi>1 y))"
        using hhom1 hxDS hyDS unfolding top1_group_hom_on_def by blast
      also have "\<Phi>1 (the_inv_into ?DS \<Phi>1 x) = x"
        using f_the_inv_into_f[OF hinj1] hx hsurj1 by blast
      also have "\<Phi>1 (the_inv_into ?DS \<Phi>1 y) = y"
        using f_the_inv_into_f[OF hinj1] hy hsurj1 by blast
      finally show ?thesis .
    qed
    \<comment> \<open>So the_inv_into(x*y) = inv(x) * inv(y).\<close>
    have hmul_cl: "?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y) \<in> ?DS"
      by (rule top1_direct_sum_carrier_mul_closed[OF hG hxDS hyDS])
    have "the_inv_into ?DS \<Phi>1 (mulH1 x y) = ?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y)"
      using the_inv_into_f_f[OF hinj1 hmul_cl] hprod by simp
    hence "?\<Psi> (mulH1 x y) = \<Phi>2 (?mulDS (the_inv_into ?DS \<Phi>1 x) (the_inv_into ?DS \<Phi>1 y))"
      by simp
    also have "... = mulH2 (\<Phi>2 (the_inv_into ?DS \<Phi>1 x)) (\<Phi>2 (the_inv_into ?DS \<Phi>1 y))"
      using hhom2 hxDS hyDS unfolding top1_group_hom_on_def by blast
    finally show "?\<Psi> (mulH1 x y) = mulH2 (?\<Psi> x) (?\<Psi> y)" by simp
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
    using hhom_psi hbij_psi by blast
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

section \<open>\<S>68 Free Products of Groups\<close>

text \<open>Reduced words in a free product G_1 * G_2.\<close>
text \<open>Reduced words in the free product G_1 * G_2: non-empty alternating sequences
  w_1 w_2 ... w_n where each w_i is in G_1 \<setminus> {e_1} or G_2 \<setminus> {e_2}, and
  consecutive w_i's come from different factors.\<close>
definition top1_free_product_carrier ::
  "'g set \<Rightarrow> 'g \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> (('g \<times> bool) list) set" where
  "top1_free_product_carrier G1 e1 G2 e2 =
     {ws. (\<forall>i<length ws.
              (snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G1 \<and> fst (ws!i) \<noteq> e1)
            \<and> (\<not> snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G2 \<and> fst (ws!i) \<noteq> e2))
        \<and> (\<forall>i. i+1 < length ws \<longrightarrow> snd (ws!i) \<noteq> snd (ws!(i+1)))}"
     \<comment> \<open>The boolean flag indicates which factor each element belongs to.
         Empty list represents the identity.\<close>

(** from \<S>68 Theorem 68.2: given a family of groups, a free product exists. **)
theorem Theorem_68_2_free_product_exists:
  assumes "\<forall>\<alpha>\<in>(J::'i set). top1_is_group_on (GG \<alpha>::'gg set) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
  shows "\<exists>(G::'gg set) mul e invg \<iota>fam.
           top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
proof -
  \<comment> \<open>Munkres 68.2: Construct G as the set of reduced words in the G\<alpha>'s.
     A word is a list [(i1, g1), (i2, g2), ...] with i_k \<in> J, g_k \<in> G_{i_k} \ {e_{i_k}},
     and consecutive indices differ. The empty list is the identity.
     Multiplication = concatenation + iterative reduction (cancel adjacent elements
     from the same group, contract e's).
     The natural inclusions \<iota>\<alpha>(g) = [(a, g)] are injective homomorphisms.\<close>
  \<comment> \<open>Step 1: Define the carrier G as reduced words (lists of (index, element) pairs
     with alternating indices and non-identity elements).\<close>
  \<comment> \<open>Step 2: Define multiplication as concatenation + iterative reduction.\<close>
  \<comment> \<open>Step 3: Verify group axioms.\<close>
  have hG_group: "\<exists>(G::'gg set) mul e invg.
      top1_is_group_on G mul e invg
    \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<exists>g\<in>G. True)
    \<and> (\<forall>\<alpha>\<in>J. \<exists>\<iota>. inj_on \<iota> (GG \<alpha>) \<and> (\<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
         \<iota> (mulGG \<alpha> x y) = mul (\<iota> x) (\<iota> y)))" sorry
  \<comment> \<open>Step 4: No nonempty reduced word represents the identity (freeness condition).\<close>
  have hG_free: "\<exists>(G::'gg set) mul e invg \<iota>fam.
      top1_is_group_on G mul e invg
    \<and> (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>))
    \<and> (\<forall>indices word. length indices = length word \<longrightarrow> length indices > 0 \<longrightarrow>
        (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
        (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
        foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e)" sorry
  show ?thesis sorry
qed

(** from \<S>68 Theorem 68.4: uniqueness of free product — any two
    free products of the same family are isomorphic. **)
theorem Theorem_68_4_free_product_unique:
  assumes "top1_is_free_product_on (G1::'g set) mul1 e1 invg1 GG mulGG \<iota>1 J"
      and "top1_is_free_product_on (G2::'g set) mul2 e2 invg2 GG mulGG \<iota>2 J"
  shows "top1_groups_isomorphic_on G1 mul1 G2 mul2"
proof -
  \<comment> \<open>Munkres 68.4: Both G1, G2 have the extension property (Lemma 68.3).
     Step 1: Define \<phi>: G1 \<rightarrow> G2 by extending the maps \<iota>2_\<alpha> \<circ> \<iota>1_\<alpha>\<inverse> on generators.
     Step 2: Similarly define \<psi>: G2 \<rightarrow> G1.
     Step 3: \<psi>\<circ>\<phi> extends id on the generators of G1, so \<psi>\<circ>\<phi> = id by uniqueness.
     Step 4: Similarly \<phi>\<circ>\<psi> = id. Hence \<phi> is an isomorphism.\<close>
  show ?thesis sorry
qed

(** from \<S>68 Theorem 68.7: if G = G_1 * G_2 is a free product and N_i \<lhd> G_i are
    normal, then (G_1 * G_2) / \<langle>\<langle>N_1 \<union> N_2\<rangle>\<rangle> \<cong> (G_1/N_1) * (G_2/N_2). **)
theorem Theorem_68_7_quotient_free_product:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and N1 N2 :: "'g set"
  assumes "top1_is_group_on G1 mul1 e1 invg1"
      and "top1_is_group_on G2 mul2 e2 invg2"
      and "top1_normal_subgroup_on G1 mul1 e1 invg1 N1"
      and "top1_normal_subgroup_on G2 mul2 e2 invg2 N2"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12
          (FPQ::'fq set) mulFPQ eFPQ invgFPQ \<iota>famQ.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_product_on FPQ mulFPQ eFPQ invgFPQ
             (\<lambda>i::nat. if i = 0
                       then top1_quotient_group_carrier_on G1 mul1 N1
                       else top1_quotient_group_carrier_on G2 mul2 N2)
             (\<lambda>i::nat. top1_quotient_group_mul_on (if i = 0 then mul1 else mul2))
             \<iota>famQ {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   (\<iota>fam12 0 ` N1 \<union> \<iota>fam12 1 ` N2)))
             (top1_quotient_group_mul_on mulFP)
             FPQ mulFPQ"
proof -
  \<comment> \<open>Munkres 68.7: The natural map \<pi>: G1*G2 \<rightarrow> (G1/N1)*(G2/N2) is a surjective
     homomorphism. Its kernel is exactly the normal closure of \<iota>1(N1) \<union> \<iota>2(N2).
     By the first isomorphism theorem, (G1*G2)/ker \<cong> (G1/N1)*(G2/N2).\<close>
  \<comment> \<open>Step 1: Build free products FP = G1*G2 and FPQ = (G1/N1)*(G2/N2).\<close>
  obtain FP mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
    sorry
  \<comment> \<open>Step 2: Natural surjection \<pi>: FP \<rightarrow> FPQ with kernel = normal closure of \<iota>1(N1)\<union>\<iota>2(N2).\<close>
  have h_surj: "\<exists>\<pi>. top1_group_hom_on FP mulFP FP mulFP \<pi> \<and> \<pi> ` FP = FP" sorry
  \<comment> \<open>Step 3: First isomorphism theorem gives the result.\<close>
  show ?thesis sorry
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
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12 \<iota>S12.
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
  obtain FP mulFP eFP invgFP \<iota>fam12 where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2) \<iota>fam12 {0,1}"
    sorry
  \<comment> \<open>Step 2: Since G1, G2 are free on S1, S2, reduced words in FP correspond to
     reduced words in S1 \<union> S2. Define \<iota>S12.\<close>
  have h_free_on_union: "\<exists>\<iota>S12. top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
    \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s)) \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))" sorry
  show ?thesis sorry
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
  shows "\<exists>(H::'h set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
proof -
  \<comment> \<open>Munkres 69.4: G is free on S, so G/[G,G] is the abelianization.
     The images \<phi>(\<iota>(s)) for s \<in> S freely generate G/[G,G] as an abelian group:
     Step 1: \<phi>(\<iota>(S)) generates H (since \<iota>(S) generates G and \<phi> is surjective).
     Step 2: No nontrivial integer combination of \<phi>(\<iota>(s))'s equals eH.
     Proof: if \<Sigma> n_s \<phi>(\<iota>(s)) = eH, then \<Sigma> n_s \<iota>(s) \<in> [G,G].
     But [G,G] consists of products of commutators, and a free group element
     that's a product of commutators has zero exponent sum in each generator.
     So all n_s = 0.\<close>
  \<comment> \<open>Step 1: Form the abelianization H = G/[G,G] via natural projection \<phi>.\<close>
  have h_abel: "\<exists>(H::'h set) mulH eH invgH \<phi>.
      top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>" sorry
  \<comment> \<open>Step 2: \<phi>(\<iota>(S)) generates H and satisfies no nontrivial integer relations
     (exponent sum argument in the free group).\<close>
  have h_free_abel: "\<exists>(H::'h set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))" sorry
  show ?thesis sorry
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
  have hbase: "n = 0 \<longrightarrow> ?thesis" sorry
  \<comment> \<open>Inductive step: decompose X = X_{n-1} \<union> C_n. Apply SvK.\<close>
  have hstep: "n > 0 \<longrightarrow> (\<exists>Xprev TXprev Cn.
      Xprev \<union> Cn = X \<and> Xprev \<inter> Cn = {p}
    \<and> top1_is_wedge_of_circles_on Xprev TXprev {..<n-1} p
    \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Cn (subspace_topology X TX Cn) p)
        (top1_fundamental_group_mul Cn (subspace_topology X TX Cn) p)
        top1_Z_group top1_Z_mul)" sorry
  \<comment> \<open>By SvK (Theorem 70.2), \<pi>_1(X) \<cong> \<pi>_1(X_{n-1}) * \<pi>_1(C_n) / trivial = free on n gens.\<close>
  have hsvk: "n > 0 \<longrightarrow> ?thesis" sorry
  show ?thesis using hbase hsvk by (by100 blast)
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
  have hfinite: "\<forall>F. finite F \<and> F \<subseteq> J \<longrightarrow>
      (\<exists>(G::'g set) mul e invg \<iota>. top1_is_free_group_full_on G mul e invg \<iota> F
        \<and> top1_groups_isomorphic_on G mul
            (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p))" sorry
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
       (subspace_topology X TX A) ?\<iota>" sorry
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
  \<comment> \<open>Step 1: T is quotient of square \<Rightarrow> space A is wedge of 2 circles (1-skeleton).\<close>
  have hA_wedge: "\<exists>(A :: 'a set) TA p.
      top1_is_wedge_of_circles_on A TA {0::nat, 1} p \<and> A \<subseteq> T_torus" sorry
  \<comment> \<open>Step 2: \<pi>_1(A) is free on 2 generators \<alpha>, \<beta> (Theorem 71.1).\<close>
  have hpi1_A_free: "\<exists>(F::'g set) mulF eF invgF \<iota>.
      top1_is_free_group_full_on F mulF eF invgF \<iota> {0::nat, 1}" sorry
  \<comment> \<open>Step 3: Attaching the 2-cell kills the commutator \<alpha>\<beta>\<alpha>\<inverse>\<beta>\<inverse>.
     So \<pi>_1(T) \<cong> F({a,b})/\<langle>\<langle>aba\<inverse>b\<inverse>\<rangle>\<rangle> \<cong> Z\<times>Z.\<close>
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
  have hA_circle: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_mul A TA x0)
        top1_Z_group top1_Z_mul" sorry
  \<comment> \<open>The attaching map wraps S^1 n times around the circle A.\<close>
  \<comment> \<open>By Theorem 72.1: \<pi>_1(X) \<cong> Z/\<langle>\<langle>n\<rangle>\<rangle> = Z/nZ.\<close>
  show ?thesis sorry
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
proof -
  \<comment> \<open>Seifert-van Kampen: \<pi>_1(X, x_0) \<cong> (\<pi>_1(U) \<star> \<pi>_1(V)) / \<langle>\<langle>{i_1(\<gamma>) \<cdot> i_2(\<gamma>)\<inverse> |
      \<gamma> \<in> \<pi>_1(U\<inter>V)}\<rangle>\<rangle>: the amalgamated free product over \<pi>_1(U\<inter>V).\<close>
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU x0"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV x0"
  let ?\<pi>X = "top1_fundamental_group_carrier X TX x0"
  \<comment> \<open>Step 1: Construct the free product FP = \<pi>_1(U) \<star> \<pi>_1(V) (exists by Theorem 68.2).\<close>
  obtain FP mulFP eFP invgFP \<iota>fam where
      hFP: "top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V)
             (\<lambda>i. if i = 0 then top1_fundamental_group_mul U ?TU x0
                  else top1_fundamental_group_mul V ?TV x0)
             \<iota>fam {0, 1}"
    sorry
  \<comment> \<open>Step 2: Define the natural map j: FP \<rightarrow> \<pi>_1(X) induced by the inclusions U, V \<hookrightarrow> X.\<close>
  \<comment> \<open>Step 3 (Surjectivity): By Theorem 59.1, every loop in X decomposes into loops in U or V.
     Hence j is surjective onto \<pi>_1(X).\<close>
  have hj_surj: "\<exists>j. top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j
      \<and> j ` FP = ?\<pi>X" sorry
  \<comment> \<open>Step 4 (Kernel): The kernel of j is the normal subgroup N generated by
     {i_1(\<gamma>) \<cdot> i_2(\<gamma>)\<inverse> | \<gamma> \<in> \<pi>_1(U\<inter>V)}.
     These elements are clearly in ker(j) since the two inclusions U\<inter>V \<hookrightarrow> U and U\<inter>V \<hookrightarrow> V
     agree when composed with the inclusions U, V \<hookrightarrow> X.
     Conversely, any element of ker(j) can be reduced to a product of such relators
     by the same Lebesgue-number subdivision argument as in Theorem 59.1.\<close>
  have hker: "\<exists>j. top1_group_hom_on FP mulFP ?\<pi>X (top1_fundamental_group_mul X TX x0) j
      \<and> top1_group_kernel_on FP (top1_fundamental_group_id X TX x0) j
        = top1_normal_subgroup_generated_on FP mulFP eFP invgFP
           { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                (U \<inter> V) ?TUV x0 U ?TU x0 (\<lambda>x. x) c))
                    (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                      (U \<inter> V) ?TUV x0 V ?TV x0 (\<lambda>x. x) c)))
              | c. c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV x0 }" sorry
  \<comment> \<open>Step 5 (First isomorphism theorem): j induces FP/N \<cong> \<pi>_1(X).\<close>
  show ?thesis using hFP hj_surj hker sorry
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
  have hcompact: "top1_compact_on X TX" sorry
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
  \<comment> \<open>Step 1: All vertices of the 4n-gon are identified to one point (1-skeleton is a wedge).\<close>
  have h_1skel: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_is_wedge_of_circles_on A TA {..<2*n} x0" sorry
  \<comment> \<open>Step 2: Applying Theorem 72.1 (attaching the 2-cell) gives the presentation.\<close>
  have h_attach: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A TA x0)
              (top1_fundamental_group_mul A TA x0)
              (top1_fundamental_group_id A TA x0)
              (top1_fundamental_group_invg A TA x0)
              {top1_fundamental_group_id A TA x0}))
        (top1_quotient_group_mul_on (top1_fundamental_group_mul A TA x0))" sorry
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
  \<comment> \<open>Step 1: 1-skeleton is a wedge of m circles.\<close>
  have h_1skel: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_is_wedge_of_circles_on A TA {..<m} x0" sorry
  \<comment> \<open>Step 2: Attaching the 2-cell with relator a_1^2...a_m^2 gives the presentation.\<close>
  have h_attach: "\<exists>(A :: 'a set) TA.
      A \<subseteq> X \<and> top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0)
        (top1_quotient_group_carrier_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_normal_subgroup_generated_on
              (top1_fundamental_group_carrier A TA x0)
              (top1_fundamental_group_mul A TA x0)
              (top1_fundamental_group_id A TA x0)
              (top1_fundamental_group_invg A TA x0)
              {top1_fundamental_group_id A TA x0}))
        (top1_quotient_group_mul_on (top1_fundamental_group_mul A TA x0))" sorry
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
  shows "\<exists>(H::'h set) mulH eH invgH \<phi>.
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
  have h_comm_normal: "top1_normal_subgroup_on ?G ?mul ?e ?inv ?comm" sorry
  \<comment> \<open>Step 2: G/[G,G] is an abelian group with the natural projection \<phi>.\<close>
  have h_quotient_abelian: "\<exists>\<phi>. top1_group_hom_on ?G ?mul
      (top1_quotient_group_carrier_on ?G ?mul ?comm)
      (top1_quotient_group_mul_on ?mul) \<phi>
    \<and> \<phi> ` ?G = top1_quotient_group_carrier_on ?G ?mul ?comm
    \<and> top1_group_kernel_on ?G (top1_quotient_group_mul_on ?mul ?comm ?comm) \<phi> = ?comm" sorry
  show ?thesis sorry
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
  have h_decomp: "\<exists>(H::'h set) mulH eH invgH. card (top1_torsion_subgroup_on H mulH eH) = 2
      \<and> (\<exists>(K::'h set). K \<subseteq> H
          \<and> top1_is_free_abelian_group_full_on K mulH eH invgH (\<lambda>i. undefined) {..<m-1})" sorry
  show ?thesis sorry
qed

section \<open>*\<S>78 Constructing Compact Surfaces\<close>

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
  have h_simplex_poly: "top1_is_polygonal_region_on top1_standard_simplex 3" sorry
  \<comment> \<open>Step 3: Assemble with quotient map q = identity on interior, edge-pasting on boundary.\<close>
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
  obtain \<T> q where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      and hcovers: "(\<Union>T\<in>\<T>. q ` T) = X"
    using Theorem_78_1_triangulable_surface[OF assms(1,3)] sorry
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
  have "\<exists>scheme. top1_quotient_of_scheme_on X TX scheme
      \<and> (scheme = [] \<or>
         (\<exists>n>0. scheme = top1_n_torus_scheme n) \<or>
         (\<exists>m>0. scheme = top1_m_projective_scheme m))" sorry
  show ?thesis sorry
qed

section \<open>Chapter 13: Classification of Covering Spaces\<close>

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
  show "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'" sorry
next
  \<comment> \<open>Backward: if subgroup images equal, use path-lifting to construct h.\<close>
  assume hH_eq: "top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  \<comment> \<open>For e \<in> E, choose path \<alpha> in E from e0 to e. Define h(e) = lift of p\<circ>\<alpha> in E' starting at e0'.
     Equal subgroups guarantee the lift exists and is well-defined.\<close>
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e) \<and> h e0 = e0'" sorry
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
  \<comment> \<open>Let e1' = h(e0). Choose path \<gamma> in E' from e0' to e1'. Set c = [p'\<circ>\<gamma>].\<close>
  let ?e1' = "h e0"
  have h_path_exists: "\<exists>\<gamma>. top1_is_path_on E' TE' e0' ?e1' \<gamma>" sorry
  have h_conjugacy: "\<exists>c\<in>top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E' TE' e0' B TB b0 p')" sorry
  show "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)" sorry
next
  \<comment> \<open>Backward: conjugacy means subgroups differ by a basepoint change in E'.
     Theorem 79.2 applies after adjusting basepoints.\<close>
  assume "\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
      top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
      = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
          ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                    (top1_fundamental_group_invg B TB b0 c)) ` H))
          (top1_fundamental_group_image_hom E TE e0 B TB b0 p)"
  \<comment> \<open>Conjugate subgroups \<Rightarrow> there exists e1' with p'(e1')=b0 s.t. the subgroups
     become equal after basepoint change. Then Theorem 79.2 gives the equivalence.\<close>
  have "\<exists>e1'. e1' \<in> E' \<and> p' e1' = b0 \<and>
      top1_fundamental_group_image_hom E TE e0 B TB b0 p
      = top1_fundamental_group_image_hom E' TE' e1' B TB b0 p'" sorry
  show "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)" sorry
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
        hcovE assms(10) hcovE' assms(11) assms(6,7,8,9)]] hRHS by (by100 blast)
qed

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
proof -
  \<comment> \<open>Munkres 80.3: Define q: E \<rightarrow> Y by path-lifting. For e \<in> E, choose path \<alpha> in E
     from e0 to e. Lift r\<inverse> \<circ> p \<circ> \<alpha> to Y starting at y0 (where r(y0)=b0).
     The lift's endpoint is q(e). Well-defined because E is simply connected.\<close>
  obtain e0 where he0: "e0 \<in> E" sorry
  let ?b0 = "p e0"
  obtain y0 where hy0: "y0 \<in> Y" and hry0: "r y0 = ?b0" sorry
  \<comment> \<open>For each e \<in> E, pick path \<alpha> from e0 to e. Lift p\<circ>\<alpha> to Y starting at y0.
     Simple connectivity ensures uniqueness (different \<alpha>'s give same endpoint).\<close>
  have "\<exists>q. (\<forall>e\<in>E. q e \<in> Y) \<and> (\<forall>e\<in>E. r (q e) = p e)
      \<and> top1_continuous_map_on E TE Y TY q" sorry
  \<comment> \<open>q is a covering map: evenly covered because p and r both are.\<close>
  show ?thesis sorry
qed

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-5) by (by100 blast)

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
  \<comment> \<open>Step 2: Define \<Phi> and show it's a well-defined homomorphism into N(H)/H.\<close>
  have h\<Phi>_hom: "\<exists>\<Phi>. top1_group_hom_on ?Cov (\<lambda>h k e. h (k e))
      (top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H)
      (top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0)) \<Phi>" sorry
  \<comment> \<open>Step 3: \<Phi> is injective (if h(e0)=e0 then h=id by unique lifting) and surjective
     (for [c] \<in> N(H)/H, lift c starting at e0 to get e1; the unique covering
     transformation mapping e0 to e1 is the preimage).\<close>
  have h\<Phi>_bij: "\<exists>\<Phi>. bij_betw \<Phi> ?Cov
      (top1_quotient_group_carrier_on
         (top1_normalizer_on
            (top1_fundamental_group_carrier B TB b0)
            (top1_fundamental_group_mul B TB b0)
            (top1_fundamental_group_invg B TB b0) ?H)
         (top1_fundamental_group_mul B TB b0) ?H)" sorry
  show ?thesis using hCov_group h\<Phi>_hom h\<Phi>_bij sorry
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
  \<comment> \<open>Step 1: Define E as the set of right cosets [\<alpha>]H.\<close>
  have hE_def: "\<exists>E p. (\<forall>e\<in>E. p e \<in> B) \<and> p ` E = B" sorry
  \<comment> \<open>Step 2: Define TE using basis sets B(U, [\<alpha>]) for path-connected open U in B.\<close>
  have hTE_basis: "\<exists>E TE. is_topology_on_strict E TE" sorry
  \<comment> \<open>Step 3: p is a covering map (evenly covered neighborhoods from semilocal simple connectivity).\<close>
  have hp_covering: "\<exists>E TE p. top1_covering_map_on E TE B TB p" sorry
  \<comment> \<open>Step 4: E is path-connected and locally path-connected.\<close>
  have hE_conn: "\<exists>E TE. top1_path_connected_on E TE \<and> top1_locally_path_connected_on E TE" sorry
  \<comment> \<open>Step 5: p_*(\<pi>_1(E, e0)) = H.\<close>
  have hH_match: "\<exists>E TE p e0. top1_fundamental_group_image_hom E TE e0 B TB b0 p = H" sorry
  show ?thesis sorry
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>
definition top1_is_arc_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_arc_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>h. top1_homeomorphism_on I_set I_top X TX h)"

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
  \<comment> \<open>Step 1: Lift each arc A to its sheets in E.\<close>
  have "\<exists>\<A>E. (\<forall>A\<in>\<A>E. A \<subseteq> E \<and> top1_is_arc_on A (subspace_topology E TE A))
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A\<in>\<A>E. \<forall>C\<in>\<A>E. A \<noteq> C \<longrightarrow>
           A \<inter> C \<subseteq> top1_arc_endpoints_on A (subspace_topology E TE A)
         \<and> finite (A \<inter> C) \<and> card (A \<inter> C) \<le> 2)
      \<and> (\<forall>D. D \<subseteq> E \<longrightarrow>
           (closedin_on E TE D \<longleftrightarrow>
            (\<forall>A\<in>\<A>E. closedin_on A (subspace_topology E TE A) (A \<inter> D))))" sorry
  \<comment> \<open>Step 2: E is Hausdorff (covering space of Hausdorff is Hausdorff).\<close>
  have "is_hausdorff_on E TE" sorry
  show ?thesis unfolding top1_is_graph_on_def sorry
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
  \<comment> \<open>Step 1: Choose maximal tree T.\<close>
  obtain T where hT: "T \<subseteq> X" and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
    sorry
  \<comment> \<open>Step 2: Collapsing T gives a wedge of circles.\<close>
  have "\<exists>W TW J p. top1_is_wedge_of_circles_on W TW J p
      \<and> top1_homotopy_equivalence_on X TX W TW
           (\<lambda>x. SOME w. True) (\<lambda>w. SOME x. True)" sorry
  \<comment> \<open>Step 3: Free group from wedge of circles (Theorem 71.3).\<close>
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
  have "\<exists>(X::'a set) TX x0. top1_is_graph_on X TX \<and> top1_connected_on X TX \<and> x0 \<in> X
      \<and> top1_groups_isomorphic_on G mul
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)" sorry
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
  have "\<exists>(X::'a set) TX x0 E TE p.
      top1_is_graph_on X TX \<and> top1_connected_on X TX
    \<and> top1_covering_map_on E TE X TX p
    \<and> top1_is_graph_on E TE \<and> top1_connected_on E TE" sorry
  \<comment> \<open>Step 2: Euler characteristic computation gives rank kn+1.\<close>
  \<comment> \<open>Step 3: H \<cong> \<pi>_1(E) is free on kn+1 generators.\<close>
  show ?thesis sorry
qed

end
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
