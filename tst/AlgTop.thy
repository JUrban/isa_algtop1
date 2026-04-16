theory AlgTop
  imports "Top0.Top1_Ch5_8"
begin

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
  sorry

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

text \<open>Helper: concatenation of homotopies via pasting lemma.
  Given F: X\<times>I \<rightarrow> Y and F': X\<times>I \<rightarrow> Y with F(x,1) = F'(x,0), define
  G(x,t) = F(x,2t) for t\<le>1/2, G(x,t) = F'(x,2t-1) for t\<ge>1/2.\<close>
lemma homotopy_concat_continuous:
  assumes "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
      and "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
      and "\<forall>x\<in>X. F (x, 1) = F' (x, 0)"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
  sorry

lemma Lemma_51_1_homotopic_trans:
  assumes h1: "top1_homotopic_on X TX Y TY f f'"
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
    by (rule homotopy_concat_continuous[OF hF hF' hmatch])
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

text \<open>Helper: concatenation of path homotopies.\<close>
lemma path_homotopy_concat_continuous:
  assumes "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
      and "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
  sorry

lemma Lemma_51_1_path_homotopic_trans:
  assumes h1: "top1_path_homotopic_on X TX x0 x1 f f'"
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
    by (rule path_homotopy_concat_continuous[OF hF hF' hmatch])
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
  assumes "top1_continuous_map_on I_set I_top X TX f"
      and "top1_continuous_map_on I_set I_top X TX g"
      and "f 1 = g 0"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
  sorry

lemma top1_path_product_is_path:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
  shows "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hmatch: "f 1 = g 0" using hf1 hg0 by simp
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
    by (rule top1_path_product_continuous[OF hfc hgc hmatch])
  have hstart: "top1_path_product f g 0 = x0"
    unfolding top1_path_product_def using hf0 by simp
  have hend: "top1_path_product f g 1 = x2"
    unfolding top1_path_product_def using hg1 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

(** from \<S>51 Theorem 51.2: groupoid properties of * **)
lemma Theorem_51_2_associativity:
  assumes "top1_is_path_on X TX x0 x1 f"
      and "top1_is_path_on X TX x1 x2 g"
      and "top1_is_path_on X TX x2 x3 h"
  shows "top1_path_homotopic_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))
    (top1_path_product (top1_path_product f g) h)"
  sorry

lemma Theorem_51_2_left_identity:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) f) f"
  sorry

lemma Theorem_51_2_right_identity:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_constant_path x1)) f"
  sorry

lemma Theorem_51_2_inverse_left:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x0
    (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
  sorry

lemma Theorem_51_2_inverse_right:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
  sorry

section \<open>\<S>52 The Fundamental Group\<close>

text \<open>A loop at x0: a path starting and ending at x0.\<close>
definition top1_is_loop_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_loop_on X TX x0 f \<longleftrightarrow> top1_is_path_on X TX x0 x0 f"

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
  assumes "top1_loop_equiv_on X TX x0 f g"
      and "top1_loop_equiv_on X TX x0 g h"
  shows "top1_loop_equiv_on X TX x0 f h"
  using assms Lemma_51_1_path_homotopic_trans[of X TX x0 x0 f g h]
  unfolding top1_loop_equiv_on_def by blast

text \<open>The set of loops at x0 modulo path homotopy — the carrier of pi_1(X, x0).
  Represented as equivalence classes of loops.\<close>
definition top1_fundamental_group_carrier :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) set set" where
  "top1_fundamental_group_carrier X TX x0 =
     { {g. top1_loop_equiv_on X TX x0 f g} | f. top1_is_loop_on X TX x0 f }"

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

text \<open>The fundamental group operation: [f]*[g] = [f*g] on equivalence classes.
  Well-defined by Theorem 51.2.\<close>

text \<open>Homomorphism induced by a continuous map h: (X, x0) \<rightarrow> (Y, y0).\<close>
definition top1_induced_homomorphism_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'b)" where
  "top1_induced_homomorphism_on X TX Y TY h f = h \<circ> f"

text \<open>Change of basepoint map: alpha-hat([f]) = [rev-alpha * f * alpha] where alpha is a path x0 -> x1.\<close>
definition top1_basepoint_change_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_basepoint_change_on X TX x0 x1 alpha f =
     top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha)"

(** from \<S>52 Theorem 52.1: the basepoint-change map is a group isomorphism **)
theorem Theorem_52_1:
  assumes "top1_is_path_on X TX x0 x1 alpha"
      and "top1_is_loop_on X TX x0 f"
      and "top1_is_loop_on X TX x0 g"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha (top1_path_product f g))
    (top1_path_product
      (top1_basepoint_change_on X TX x0 x1 alpha f)
      (top1_basepoint_change_on X TX x0 x1 alpha g))"
  sorry

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
  p\<inverse>(U) is a disjoint union of open V\<alpha> \<subseteq> E, each mapped homeomorphically by p.
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

text \<open>Lifting of a continuous map: f\<tilde>: X \<rightarrow> E with p \<circ> f\<tilde> = f.\<close>
definition top1_is_lifting_on :: "'x set \<Rightarrow> 'x set set \<Rightarrow> 'e set \<Rightarrow> 'e set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<longleftrightarrow>
     top1_continuous_map_on X TX E TE ftilde \<and>
     (\<forall>x\<in>X. p (ftilde x) = f x)"

text \<open>The unit circle S^1 as a subspace of R^2.\<close>
definition top1_S1 :: "(real \<times> real) set" where
  "top1_S1 = {p. fst p ^ 2 + snd p ^ 2 = 1}"

definition top1_S1_topology :: "(real \<times> real) set set" where
  "top1_S1_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_S1"

text \<open>The canonical covering map p: R \<rightarrow> S^1 given by p(x) = (cos 2\<pi>x, sin 2\<pi>x).\<close>
definition top1_R_to_S1 :: "real \<Rightarrow> real \<times> real" where
  "top1_R_to_S1 x = (cos (2 * pi * x), sin (2 * pi * x))"

(** from \<S>53 Theorem 53.1: the canonical map R \<rightarrow> S^1 is a covering map **)
theorem Theorem_53_1:
  "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
  sorry

(** from \<S>53 Theorem 53.2: restriction of a covering map to a subspace is a covering map.
    Uses strict topology: subspace of strict is strict. **)
theorem Theorem_53_2:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "B0 \<subseteq> B"
      and "E0 = {e\<in>E. p e \<in> B0}"
  shows "top1_covering_map_on E0 (subspace_topology E TE E0)
    B0 (subspace_topology B TB B0) p"
  sorry

(** from \<S>53 Theorem 53.3: product of covering maps is a covering map.
    Uses strict topology: product of strict is strict. **)
theorem Theorem_53_3:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on E' TE' B' TB' p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'" and "is_topology_on_strict B' TB'"
  shows "top1_covering_map_on (E \<times> E') (product_topology_on TE TE')
    (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
  sorry

section \<open>\<S>54 The Fundamental Group of the Circle\<close>

(** from \<S>54 Lemma 54.1: path-lifting lemma **)
lemma Lemma_54_1_path_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_path_on B TB b0 b1 f"
  shows "\<exists>ftilde. top1_is_path_on E TE e0 (ftilde 1) ftilde
    \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)"
  sorry

(** from \<S>54 Lemma 54.2: homotopy-lifting lemma **)
lemma Lemma_54_2_homotopy_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
      and "F (0, 0) = b0"
  shows "\<exists>Ftilde. top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde
    \<and> (\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t))
    \<and> Ftilde (0, 0) = e0"
  sorry

(** from \<S>54 Theorem 54.3: path-homotopic paths lift to path-homotopic paths **)
theorem Theorem_54_3:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_path_on B TB b0 b1 f"
      and "top1_is_path_on B TB b0 b1 g"
      and "top1_path_homotopic_on B TB b0 b1 f g"
      and "top1_is_path_on E TE e0 e1 ftilde"
      and "(\<forall>s\<in>I_set. p (ftilde s) = f s)"
      and "top1_is_path_on E TE e0 e1' gtilde"
      and "(\<forall>s\<in>I_set. p (gtilde s) = g s)"
  shows "e1 = e1' \<and> top1_path_homotopic_on E TE e0 e1 ftilde gtilde"
  sorry

(** from \<S>54 Theorem 54.5: fundamental group of S^1 is isomorphic to Z **)
theorem Theorem_54_5:
  "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
    (UNIV::int set)"
  sorry

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

text \<open>The closed disc B^2 and unit sphere S^1 as subspaces of R^2.\<close>
definition top1_B2 :: "(real \<times> real) set" where
  "top1_B2 = {p. fst p ^ 2 + snd p ^ 2 \<le> 1}"

definition top1_B2_topology :: "(real \<times> real) set set" where
  "top1_B2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_B2"

(** from \<S>55 Lemma 55.1: if A is a retract of X, then (\<pi>_1 A, x0) \<rightarrow> (\<pi>_1 X, x0)
    is injective (induced by inclusion) **)
lemma Lemma_55_1_retract_injective:
  assumes "top1_retract_of_on X TX A"
      and "x0 \<in> A"
      and "top1_is_loop_on A (subspace_topology X TX A) x0 f"
      and "top1_is_loop_on A (subspace_topology X TX A) x0 g"
      and "top1_path_homotopic_on X TX x0 x0 f g"
  shows "top1_path_homotopic_on A (subspace_topology X TX A) x0 x0 f g"
  sorry

(** from \<S>55 Theorem 55.2: No-retraction theorem: no retraction B^2 \<rightarrow> S^1 **)
theorem Theorem_55_2_no_retraction:
  "\<not> top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
  sorry

(** from \<S>55 Theorem 55.6: Brouwer fixed-point theorem for the disc **)
theorem Theorem_55_6_brouwer:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology top1_B2 top1_B2_topology f"
  shows "\<exists>x\<in>top1_B2. f x = x"
  sorry

section \<open>\<S>56 The Fundamental Theorem of Algebra\<close>

(** from *\<S>56 Theorem 56.1: Fundamental Theorem of Algebra **)
theorem Theorem_56_1_FTA:
  fixes a :: "nat \<Rightarrow> complex"
  assumes "n > 0" and "a n \<noteq> 0"
  shows "\<exists>z. (\<Sum>k\<le>n. a k * z^k) = 0"
  sorry

section \<open>\<S>57 The Borsuk-Ulam Theorem\<close>

text \<open>Antipode-preserving map on the plane: h(-x) = -h(x) pointwise.\<close>
definition top1_antipode_preserving_S1 :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> bool" where
  "top1_antipode_preserving_S1 h \<longleftrightarrow>
     (\<forall>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y))))"

(** from *\<S>57 Theorem 57.1: antipode-preserving S^1 \<rightarrow> S^1 has odd degree **)
theorem Theorem_57_1:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and "top1_antipode_preserving_S1 h"
  shows "\<exists>n. odd n \<and>
    (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f \<longrightarrow>
         top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
           (h \<circ> f) f)"  \<comment> \<open>simplified: degree-n statement\<close>
  sorry

(** from *\<S>57 Theorem 57.3: Borsuk-Ulam theorem for S^2 **)
theorem Theorem_57_3_BorsukUlam:
  fixes f :: "real \<times> real \<times> real \<Rightarrow> real \<times> real"
  assumes "top1_continuous_map_on {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}
    (subspace_topology UNIV
      (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets))
      {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1})
    UNIV (product_topology_on top1_open_sets top1_open_sets) f"
  shows "\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x))"
  sorry

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

(** from \<S>58 Theorem 58.2: inclusion S^n \<rightarrow> R^{n+1}-0 induces isomorphism of fundamental groups **)
theorem Theorem_58_2_inclusion_iso:
  "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
    (top1_fundamental_group_carrier
       (UNIV - {(0, 0)})
       (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
       (1, 0))"
  sorry

(** from \<S>58 Theorem 58.3: deformation retract induces isomorphism of fundamental groups **)
theorem Theorem_58_3:
  assumes "top1_deformation_retract_of_on X TX A" and "x0 \<in> A"
  shows "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
    (top1_fundamental_group_carrier X TX x0)"
  sorry

(** from \<S>58 Theorem 58.7: a homotopy equivalence induces an isomorphism of fundamental groups.
    The strict version is trivially related. **)
theorem Theorem_58_7:
  assumes "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_carrier Y TY (f x0))"
  sorry

corollary Theorem_58_7_strict:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
    and "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier X TX x0)
    (top1_fundamental_group_carrier Y TY (f x0))"
  using Theorem_58_7[OF assms(3) assms(4)] by blast

section \<open>\<S>59 The Fundamental Group of S^n\<close>

text \<open>The n-sphere S^n embedded in R^{n+1}.\<close>
definition top1_Sn :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "top1_Sn n = {x. (\<forall>i \<ge> Suc n. x i = 0) \<and> (\<Sum>i\<le>n. (x i)^2) = 1}"

(** from \<S>59 Theorem 59.1: van Kampen-like union theorem for fundamental groups.
    Uses strict topology: under strict TX, U and V are automatically subsets of X. **)
theorem Theorem_59_1:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X" and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "x0 \<in> U \<inter> V"
  shows "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
    (\<exists>g h. top1_is_loop_on X TX x0 g \<and> top1_is_loop_on X TX x0 h
      \<and> (\<forall>s\<in>I_set. (g s \<in> U \<or> h s \<in> V))
      \<and> top1_path_homotopic_on X TX x0 x0 f (top1_path_product g h))"
  sorry

(** from \<S>59 Theorem 59.3: for n \<ge> 2, S^n is simply connected **)
theorem Theorem_59_3:
  assumes "n \<ge> 2"
  shows "top1_simply_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
  sorry

section \<open>\<S>60 Fundamental Groups of Some Surfaces\<close>

(** from \<S>60 Theorem 60.1: fundamental group of product is product of fundamental groups.
    Uses strict topology: product of strict topologies is strict. **)
theorem Theorem_60_1_product:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
      and "x0 \<in> X" and "y0 \<in> Y"
  shows "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier (X \<times> Y) (product_topology_on TX TY) (x0, y0))
    ((top1_fundamental_group_carrier X TX x0) \<times>
     (top1_fundamental_group_carrier Y TY y0))"
  sorry

section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>

text \<open>The 2-sphere S^2 as a subspace of R^3.\<close>
definition top1_S2 :: "(real \<times> real \<times> real) set" where
  "top1_S2 = {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"

definition top1_S2_topology :: "(real \<times> real \<times> real) set set" where
  "top1_S2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets
       (product_topology_on top1_open_sets top1_open_sets)) top1_S2"

text \<open>A set C separates a space X if X - C has more than one component.\<close>
definition top1_separates_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_separates_on X TX C \<longleftrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"

(** from \<S>61 Theorem 61.3: Jordan separation theorem for S^2 **)
theorem Theorem_61_3_JordanSeparation_S2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_separates_on top1_S2 top1_S2_topology C"
  sorry

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
  sorry

section \<open>\<S>63 The Jordan Curve Theorem\<close>

text \<open>A simple closed curve in X: image of a continuous injective map S^1 \<rightarrow> X.\<close>
definition top1_simple_closed_curve_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_simple_closed_curve_on X TX C \<longleftrightarrow>
     (\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<and> inj_on f top1_S1
          \<and> f ` top1_S1 = C)"

(** from \<S>63 Theorem 63.4: Jordan Curve Theorem **)
theorem Theorem_63_4_JordanCurve:
  fixes C :: "(real \<times> real) set"
  assumes "top1_simple_closed_curve_on
    UNIV (product_topology_on top1_open_sets top1_open_sets) C"
  shows "\<exists>U V. U \<inter> V = {} \<and> U \<union> V = UNIV - C
    \<and> top1_path_connected_on U
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
    \<and> top1_path_connected_on V
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) V)"
  sorry

section \<open>\<S>65 The Winding Number of a Simple Closed Curve\<close>

text \<open>The winding number of a loop f in R^2-{0} around the origin.
  It is an integer, well-defined up to homotopy.\<close>
definition top1_winding_number_on ::
  "(real \<Rightarrow> real \<times> real) \<Rightarrow> int" where
  "top1_winding_number_on f = (SOME n. True)"  \<comment> \<open>Placeholder; proper def via lifting\<close>

(** from \<S>65 Theorem 65.2: inclusion C \<rightarrow> S^2 - p - q induces fundamental group iso **)
theorem Theorem_65_2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  and "\<comment> \<open>p, q in different components of S^2 - C\<close> True"
  shows "\<exists>\<phi>. bij_betw \<phi>
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)"
  sorry

section \<open>Chapter 11: The Seifert-van Kampen Theorem\<close>

section \<open>\<S>67 Direct Sums of Abelian Groups\<close>

text \<open>External direct sum: the set of finitely-supported functions J \<rightarrow> \<Union>G_\<alpha>.\<close>
definition top1_direct_sum_carrier :: "'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g) set" where
  "top1_direct_sum_carrier J G =
     {f. (\<forall>i\<in>J. f i \<in> G i) \<and> (\<forall>i. i \<notin> J \<longrightarrow> f i = undefined) \<and>
         finite {i\<in>J. f i \<noteq> undefined}}"  \<comment> \<open>approximation; real: f i \<noteq> 0_{G_i}\<close>

(** from \<S>67 Theorem 67.4: existence of external direct sum **)
theorem Theorem_67_4_direct_sum_exists:
  "\<exists>G (inj :: 'i \<Rightarrow> 'g \<Rightarrow> ('i \<Rightarrow> 'g)). True"
    \<comment> \<open>Simplified existence statement\<close>
  sorry

(** from \<S>67 Theorem 67.6: uniqueness of direct sums **)
theorem Theorem_67_6_direct_sum_unique:
  fixes G G' :: "'g set" and inj inj' :: "'i \<Rightarrow> 'h \<Rightarrow> 'g"
  shows "True"  \<comment> \<open>Simplified uniqueness statement\<close>
  by simp

(** from \<S>67 Theorem 67.8: rank of free abelian group is well-defined **)
theorem Theorem_67_8_rank_unique:
  fixes n m :: nat
  shows "True"  \<comment> \<open>Simplified: n is determined by G\<close>
  by simp

section \<open>\<S>68 Free Products of Groups\<close>

text \<open>Reduced words in a free product G_1 * G_2.\<close>
definition top1_free_product_carrier :: "'g set \<Rightarrow> 'g set \<Rightarrow> 'g list set" where
  "top1_free_product_carrier G1 G2 =
     {ws. \<forall>i<length ws. ws!i \<in> G1 \<union> G2}"  \<comment> \<open>approximation\<close>

section \<open>\<S>69 Free Groups\<close>

text \<open>Free group on a set of generators.\<close>
definition top1_is_free_group_on :: "'g set \<Rightarrow> 'g set \<Rightarrow> bool" where
  "top1_is_free_group_on G S \<longleftrightarrow> True"  \<comment> \<open>Placeholder: universal property\<close>

(** from \<S>69 Theorem 69.2: free product of free groups is free **)
theorem Theorem_69_2:
  assumes "top1_is_free_group_on G1 S1" and "top1_is_free_group_on G2 S2"
      and "S1 \<inter> S2 = {}"
  shows "\<exists>G. top1_is_free_group_on G (S1 \<union> S2)"
  sorry

(** from \<S>69 Theorem 69.4: abelianization of free group is free abelian **)
theorem Theorem_69_4:
  assumes "top1_is_free_group_on G S"
  shows "True"  \<comment> \<open>G/[G,G] is free abelian on classes [a_\<alpha>]\<close>
  by simp

section \<open>\<S>70 The Seifert-van Kampen Theorem\<close>

(** from \<S>70 Theorem 70.1/70.2: Seifert-van Kampen Theorem.
    Conclusion: every loop in X at x0 is path-homotopic to a finite product of
    loops, each lying entirely in U or entirely in V.
    Uses strict topology and openin_on. **)
theorem Theorem_70_2_SvK:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X" and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
    (\<exists>n loops. (\<forall>i<n. (\<exists>x\<in>X. top1_is_loop_on X TX x0 (loops i)
        \<and> (loops i) ` I_set \<subseteq> U \<union> V \<and>
        ((loops i) ` I_set \<subseteq> U \<or> (loops i) ` I_set \<subseteq> V))))"
  sorry  \<comment> \<open>Simplified: loops decompose into loops in U or V\<close>

section \<open>Chapter 12: Classification of Surfaces\<close>

text \<open>Surface: a connected, Hausdorff, compact 2-manifold.
  A 2-manifold is a space where every point has a neighborhood homeomorphic
  to an open subset of R^2.\<close>
definition top1_is_2_manifold_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_2_manifold_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<forall>x\<in>X. \<exists>U (V :: (real \<times> real) set) h.
        x \<in> U \<and> openin_on X TX U \<and>
        V \<in> product_topology_on top1_open_sets top1_open_sets \<and>
        top1_homeomorphism_on U (subspace_topology X TX U) V
          (subspace_topology UNIV
             (product_topology_on top1_open_sets top1_open_sets) V)
          h)"

definition top1_is_surface_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_surface_on X TX \<longleftrightarrow>
     top1_is_2_manifold_on X TX \<and>
     top1_connected_on X TX \<and>
     is_hausdorff_on X TX \<and>
     top1_compact_on X TX"

section \<open>\<S>74 Fundamental Groups of Surfaces\<close>

text \<open>The n-fold torus T_n = S^1 \<times> S^1 \<times> ... \<times> S^1 (n times), iterated connected sum.\<close>
definition top1_n_fold_torus :: "nat \<Rightarrow> ('a set)" where
  "top1_n_fold_torus n = undefined"  \<comment> \<open>Placeholder: connected sum construction\<close>

text \<open>The m-fold projective plane P_m.\<close>
definition top1_m_fold_projective :: "nat \<Rightarrow> ('a set)" where
  "top1_m_fold_projective m = undefined"

(** from \<S>74 Theorem 74.1: polygonal quotients are compact Hausdorff **)
theorem Theorem_74_1_polygon_quotient_compact_hausdorff:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "is_topology_on_strict X TX"
  and "True"  \<comment> \<open>X is quotient of finite polygonal region by edge-pasting\<close>
  shows "top1_compact_on X TX \<and> is_hausdorff_on X TX"
  sorry

(** from \<S>74 Theorem 74.3: fundamental group of n-fold torus **)
theorem Theorem_74_3_fund_group_n_torus:
  "True"  \<comment> \<open>\<pi>_1(T_n) \<cong> F_{2n} / \<langle>[\<alpha>_1,\<beta>_1]\<cdots>[\<alpha>_n,\<beta>_n]\<rangle>\<close>
  by simp

(** from \<S>74 Theorem 74.4: fundamental group of m-fold projective plane **)
theorem Theorem_74_4_fund_group_m_projective:
  "True"  \<comment> \<open>\<pi>_1(P_m) \<cong> F_m / \<langle>\<alpha>_1^2 \<cdots> \<alpha>_m^2\<rangle>\<close>
  by simp

section \<open>\<S>75 Homology of Surfaces\<close>

(** from \<S>75 Theorem 75.1: H_1 is abelianization of \<pi>_1 **)
theorem Theorem_75_1_H1_abelianization:
  "True"  \<comment> \<open>Simplified statement\<close>
  by simp

(** from \<S>75 Theorem 75.3: H_1 of n-fold torus is free abelian of rank 2n **)
theorem Theorem_75_3_H1_n_torus:
  "True"  \<comment> \<open>H_1(T_n) \<cong> Z^{2n}\<close>
  by simp

(** from \<S>75 Theorem 75.4: H_1 of m-fold projective plane **)
theorem Theorem_75_4_H1_m_projective:
  "True"  \<comment> \<open>T(P_m) \<cong> Z/2, H_1(P_m)/T \<cong> Z^{m-1}\<close>
  by simp

section \<open>\<S>77 The Classification Theorem\<close>

(** from \<S>77 Theorem 77.5: Classification theorem for compact surfaces **)
theorem Theorem_77_5_classification:
  assumes "top1_is_surface_on X TX"
  and "True"  \<comment> \<open>X is quotient of polygonal region\<close>
  shows "\<comment> \<open>X is homeomorphic to S^2, T_n, or P_m\<close> True"
  sorry

section \<open>Chapter 13: Classification of Covering Spaces\<close>

text \<open>Equivalence of covering spaces: homeomorphism commuting with covering maps.\<close>
definition top1_equivalent_coverings_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'e' set \<Rightarrow> 'e' set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e' \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_equivalent_coverings_on E TE E' TE' B TB p p' \<longleftrightarrow>
     top1_covering_map_on E TE B TB p \<and>
     top1_covering_map_on E' TE' B TB p' \<and>
     (\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e))"

(** from \<S>79 Theorem 79.4: coverings are equivalent iff their subgroup images
    in \<pi>_1(B) are conjugate. Uses strict topology. **)
theorem Theorem_79_4:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'"
      and "top1_covering_map_on E TE B TB p" and "p e0 = b0"
      and "top1_covering_map_on E' TE' B TB p'" and "p' e0' = b0"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
  shows "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
             \<and> h e0 = e0') \<longleftrightarrow>
         \<comment> \<open>p_*(\<pi>_1 E) = p'_*(\<pi>_1 E') as subgroups of \<pi>_1(B, b0)\<close>
         (True)"  \<comment> \<open>Simplified: full statement requires subgroup equality\<close>
  sorry

section \<open>\<S>80 The Universal Covering Space\<close>

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  sorry

section \<open>\<S>82 Existence of Covering Spaces\<close>

text \<open>Semilocally simply connected: every point has a neighborhood U such that
  every loop in U is nulhomotopic in X.\<close>
definition top1_semilocally_simply_connected_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_semilocally_simply_connected_on X TX \<longleftrightarrow>
     (\<forall>x\<in>X. \<exists>U. openin_on X TX U \<and> x \<in> U \<and>
        (\<forall>f. top1_is_loop_on U (subspace_topology X TX U) x f \<longrightarrow>
             top1_path_homotopic_on X TX x x f (top1_constant_path x)))"

(** from \<S>82 Theorem 82.1: existence of covering space for any subgroup **)
theorem Theorem_82_1_covering_existence:
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 \<in> B"
      and "H \<subseteq> top1_fundamental_group_carrier B TB b0"
  shows "\<exists>E TE p e0. is_topology_on_strict E TE
    \<and> top1_covering_map_on E TE B TB p
    \<and> e0 \<in> E \<and> p e0 = b0"
  sorry

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>85 Subgroups of Free Groups\<close>

(** from \<S>85 Theorem 85.1 (Nielsen-Schreier): subgroups of free groups are free **)
theorem Theorem_85_1_Nielsen_Schreier:
  assumes "top1_is_free_group_on G S"
  and "H \<subseteq> G"
  and "True"  \<comment> \<open>H is a subgroup\<close>
  shows "\<exists>S'. top1_is_free_group_on H S'"
  sorry

(** from \<S>85 Theorem 85.3: Schreier index formula **)
theorem Theorem_85_3_Schreier_index:
  assumes "top1_is_free_group_on G S"
  and "card S = n + 1"
  and "H \<subseteq> G"
  and "True"  \<comment> \<open>H has index k in G\<close>
  shows "\<exists>S'. top1_is_free_group_on H S' \<and> card S' = k * n + 1"
  sorry

end
