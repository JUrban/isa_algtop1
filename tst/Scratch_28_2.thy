theory Scratch_28_2
  imports Top1_Ch5_8
begin

(* Temporary scratch file for developing Theorem_28_2 proof with sledgehammer.
   Once proofs are found, copy back to i/Top1_Ch3.thy *)

text \<open>Goal: prove the sorry steps in Theorem_28_2.\<close>

text \<open>Step 1: pigeonhole — finite range gives infinite repetition.\<close>
lemma pigeonhole_step:
  assumes "finite (s ` UNIV)"
  shows "\<exists>x. x \<in> s ` UNIV \<and> infinite {n::nat. s n = x}"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 2: from x ∈ range s, x ∈ X.\<close>
lemma range_in_X:
  assumes "\<forall>n::nat. s n \<in> X" and "x \<in> s ` UNIV"
  shows "x \<in> X"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 3: infinite nat set is unbounded.\<close>
lemma infinite_nat_unbounded:
  assumes "infinite {n::nat. P n}"
  shows "\<forall>m. \<exists>n > m. P n"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 4: LEAST gives the property.\<close>
lemma least_pick:
  assumes "\<exists>n > m. P n"
  defines "k \<equiv> LEAST n. n > m \<and> P n"
  shows "k > m \<and> P k"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 5: rec_nat sub values.\<close>
lemma rec_nat_val:
  assumes "sub = rec_nat (pick 0) (\<lambda>_ prev. pick prev)"
  assumes "\<And>m. s (pick m) = x"
  shows "\<And>n. s (sub n) = x"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 6: rec_nat strict mono.\<close>
lemma rec_nat_mono:
  assumes "sub = rec_nat (pick 0) (\<lambda>_ prev. pick prev)"
  assumes "\<And>m. pick m > m"
  shows "\<And>n. sub n < sub (Suc n)"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 7: strict_mono from Suc.\<close>
lemma strict_mono_from_suc:
  assumes "\<And>n. (f::nat\<Rightarrow>nat) n < f (Suc n)"
  shows "strict_mono f"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 8: constant subsequence converges.\<close>
lemma const_subseq_converges:
  assumes "is_topology_on X T" and "x \<in> X" and "\<forall>n. s (sub n) = x"
  shows "seq_converges_to_on (s \<circ> sub) x X T"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 9: limit point in closure.\<close>
lemma limit_point_in_closure:
  assumes "is_topology_on X T" and "A \<subseteq> X" and "x \<in> X"
  and "is_limit_point_of x A X T"
  shows "x \<in> closure_on X T A"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 10: T1 for metric space.\<close>
lemma metric_T1:
  assumes "top1_metric_on X d" and "T = top1_metric_topology_on X d"
  shows "satisfies_T1_on X T"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 11: limit point + T1 + infinite range → ball hit at large indices.\<close>
lemma ball_hit_large:
  assumes "top1_metric_on X d" and "T = top1_metric_topology_on X d"
  and "\<forall>n. s n \<in> X" and "x \<in> X"
  and "is_limit_point_of x (s ` UNIV) X T"
  and "infinite (s ` UNIV)"
  and "0 < (e::real)"
  shows "\<exists>n > m. d x (s n) < e"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 12: Archimedean for 1/(N+2) < e.\<close>
lemma archimedean_inv:
  assumes "0 < (e::real)"
  shows "\<exists>N::nat. 1 / real (N + 2) < e"
  sledgehammer [timeout = 10]
  sorry

text \<open>Step 13: monotonicity 1/(n+2).\<close>
lemma inv_mono:
  assumes "(N::nat) \<le> n"
  shows "1 / real (n + 2) \<le> 1 / real (N + (2::nat))"
  sledgehammer [timeout = 10]
  sorry

end
