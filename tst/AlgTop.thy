theory AlgTop
  imports "AlgTopCached20.AlgTopCached20"
begin


\<comment> \<open>SIGMA DICTIONARY (expert audit 39).\<close>
lemma open_unit_interval_one_minus:
  "t \<in> {0<..<(1::real)} \<Longrightarrow> 1 - t \<in> {0<..<(1::real)}"
  by (by100 auto)

\<comment> \<open>Bool excluded middle helper for sign transport.\<close>
lemma bool_neq_eq: "\<lbrakk>(a::bool) \<noteq> c; b \<noteq> c\<rbrakk> \<Longrightarrow> a = b"
  by (by100 auto)

lemma bool_neq_neq: "\<lbrakk>(a::bool) \<noteq> c; b = c\<rbrakk> \<Longrightarrow> a \<noteq> b"
  by (by100 auto)

\<comment> \<open>Real arithmetic: cancel subtraction from 1.\<close>
lemma one_minus_cancel [simp]: "(1 - (a::real) = 1 - b) = (a = b)"
  by (by100 auto)

\<comment> \<open>SIGMA DICTIONARY (expert audit 39). Non-c target edge data.\<close>
lemma paste_sigma_non_c_edge_data:
  fixes a c :: "'b" and u2 v :: "('b \<times> bool) list" and vx vy :: "nat \<Rightarrow> real"
  defines "k \<equiv> Suc (length u2)"
      and "n \<equiv> Suc (Suc (length u2 + length v))"
      and "w \<equiv> [(a, True)] @ u2 @ [(a, True)] @ v"
      and "w' \<equiv> [(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  assumes hi: "i < n" and hi0: "i \<noteq> 0" and hinm1: "i \<noteq> n - 1"
      and ht: "t \<in> {0<..<(1::real)}"
  shows "\<exists>i_old rev_flag.
      i_old < n
    \<and> (if rev_flag then 1 - t else t) \<in> {0<..<(1::real)}
    \<and> paste_chain_sigma_x vx k n i t =
        (1 - (if rev_flag then 1 - t else t)) * vx i_old +
        (if rev_flag then 1 - t else t) * vx (Suc i_old mod n)
    \<and> paste_chain_sigma_y vy k n i t =
        (1 - (if rev_flag then 1 - t else t)) * vy i_old +
        (if rev_flag then 1 - t else t) * vy (Suc i_old mod n)
    \<and> fst (w' ! i) = fst (w ! i_old)
    \<and> (snd (w' ! i) = snd (w ! i_old)) = (\<not> rev_flag)
    \<and> i_old = (if rev_flag then k - i else Suc i)"
proof (cases "i \<le> k - 1")
  case True
  have h1: "k - i < n" using True hi unfolding k_def n_def by (by100 linarith)
  have h2: "(1 - t) \<in> {0<..<(1::real)}" using open_unit_interval_one_minus[OF ht] .
  have hSuc_mod: "Suc (k - i) mod n = k + 1 - i"
  proof -
    have "i \<le> k" using True unfolding k_def by (by100 linarith)
    have "k - i < n - 1" using True hi hinm1 hi0 unfolding k_def n_def by (by100 linarith)
    hence "Suc (k - i) < n" unfolding n_def by (by100 linarith)
    hence "Suc (k - i) mod n = Suc (k - i)" by (by100 simp)
    also have "Suc (k - i) = k + 1 - i" using \<open>i \<le> k\<close> by (by100 linarith)
    finally show ?thesis .
  qed
  have h3: "paste_chain_sigma_x vx k n i t = t * vx (k-i) + (1-t) * vx (Suc (k-i) mod n)"
  proof -
    have "paste_chain_sigma_x vx k n i t = t*vx(k-i) + (1-t)*vx(k+1-i)"
      using hi0 hinm1 True unfolding paste_chain_sigma_x_def k_def n_def by (by100 simp)
    thus ?thesis using hSuc_mod by (by100 simp)
  qed
  have h4: "paste_chain_sigma_y vy k n i t = t * vy (k-i) + (1-t) * vy (Suc (k-i) mod n)"
  proof -
    have "paste_chain_sigma_y vy k n i t = t*vy(k-i) + (1-t)*vy(k+1-i)"
      using hi0 hinm1 True unfolding paste_chain_sigma_y_def k_def n_def by (by100 simp)
    thus ?thesis using hSuc_mod by (by100 simp)
  qed
  have h5h6: "fst (w' ! i) = fst (w ! (k-i)) \<and> snd (w' ! i) \<noteq> snd (w ! (k-i))"
  proof -
    have hi1: "1 \<le> i" using hi0 by (by100 simp)
    have hik: "i \<le> length u2" using True unfolding k_def by (by100 simp)
    \<comment> \<open>w'!i = rev(inv(u2))!(i-1).\<close>
    have hw'i: "w' ! i = rev (map top1_inverse_edge u2) ! (i - 1)"
    proof -
      have "w' ! i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
        unfolding w'_def using hi1 by (by100 simp)
      moreover have "i - 1 < length (rev (map top1_inverse_edge u2))"
        using hi1 hik by (by100 simp)
      ultimately show ?thesis
        using nth_append_first[of "i-1" "rev (map top1_inverse_edge u2)" "v @ [(c, True)]"]
        by (by100 simp)
    qed
    \<comment> \<open>rev(inv(u2))!(i-1) = inv(u2!(|u2|-i)).\<close>
    have him1_lt: "i - 1 < length u2" using hi1 hik by (by100 linarith)
    have "rev (map top1_inverse_edge u2) ! (i - 1) = top1_inverse_edge (u2 ! (length u2 - i))"
    proof -
      from rev_nth[of "i - 1" "map top1_inverse_edge u2"] him1_lt
      have "rev (map top1_inverse_edge u2) ! (i - 1) =
        (map top1_inverse_edge u2) ! (length u2 - 1 - (i - 1))" by (by100 simp)
      moreover have "length u2 - 1 - (i - 1) = length u2 - i" using hi1 him1_lt by (by100 linarith)
      moreover have "length u2 - i < length u2" using hi1 hik by (by100 linarith)
      ultimately show ?thesis by (by100 simp)
    qed
    hence hw'i2: "w' ! i = top1_inverse_edge (u2 ! (length u2 - i))" using hw'i by (by100 simp)
    \<comment> \<open>w!(k-i) = u2!(k-i-1) = u2!(length u2 - i).\<close>
    have "k - i \<ge> 1" using hi1 True unfolding k_def by (by100 linarith)
    have "k - i - 1 < length u2"
    proof -
      have "k - i - 1 = length u2 - i" unfolding k_def using hi1 by (by100 linarith)
      thus ?thesis using hi1 hik by (by100 linarith)
    qed
    have hw_ki: "w ! (k - i) = u2 ! (k - i - 1)"
    proof -
      have hki_bound: "k - i < Suc (length u2)"
        using \<open>k - i - 1 < length u2\<close> by (by100 linarith)
      have "w = [(a, True)] @ u2 @ [(a, True)] @ v" unfolding w_def by (by100 simp)
      hence "w ! (k - i) = ([(a, True)] @ u2 @ [(a, True)] @ v) ! (k - i)" by (by100 simp)
      also have "\<dots> = ((a, True) # u2) ! (k - i)"
        using nth_append_first[of "k-i" "(a,True)#u2" "[(a,True)] @ v"] hki_bound
        by (by100 simp)
      also have "\<dots> = u2 ! (k - i - 1)" using \<open>k - i \<ge> 1\<close> by (by100 simp)
      finally show ?thesis .
    qed
    have "k - i - 1 = length u2 - i" unfolding k_def using hi1 by (by100 linarith)
    hence hw_ki2: "w ! (k - i) = u2 ! (length u2 - i)" using hw_ki by (by100 simp)
    \<comment> \<open>fst and snd from top1\\_inverse\\_edge.\<close>
    show ?thesis using hw'i2 hw_ki2 unfolding top1_inverse_edge_def by (by100 simp)
  qed
  hence h5: "fst (w' ! i) = fst (w ! (k-i))" and h6: "snd (w' ! i) \<noteq> snd (w ! (k-i))"
    by (by100 simp)+
  show ?thesis
    apply (rule exI[of _ "k - i"], rule exI[of _ True])
    using h1 h2 h3 h4 h5 h6 by (by5000 simp)
next
  case False hence hige: "i \<ge> k" using hi0 unfolding k_def by (by100 simp)
  have h1: "i + 1 < n" using hinm1 hi unfolding n_def by (by100 linarith)
  have h2: "t \<in> {0<..<(1::real)}" using ht .
  have h3: "paste_chain_sigma_x vx k n i t = (1-t) * vx (i+1) + t * vx (Suc (i+1) mod n)"
    using hi0 hinm1 False unfolding paste_chain_sigma_x_def k_def n_def by (by100 simp)
  have h4: "paste_chain_sigma_y vy k n i t = (1-t) * vy (i+1) + t * vy (Suc (i+1) mod n)"
    using hi0 hinm1 False unfolding paste_chain_sigma_y_def k_def n_def by (by100 simp)
  have h5h6: "fst (w' ! i) = fst (w ! (i+1)) \<and> snd (w' ! i) = snd (w ! (i+1))"
  proof -
    \<comment> \<open>w'!i for k\\<le>i\\<le>n-2: w'!i = v!(i-k). v!(i-k) = w!(i+1).\<close>
    have "i - 1 \<ge> length u2" using hige unfolding k_def by (by100 linarith)
    have him1_lt: "i - 1 < length u2 + length v"
    proof -
      have "i \<le> n - 2" using hi hinm1 unfolding n_def by (by100 linarith)
      hence "i \<le> length u2 + length v" unfolding n_def by (by100 linarith)
      thus ?thesis using hi0 by (by100 linarith)
    qed
    \<comment> \<open>w'!i = (rev(inv(u2)) @ v @ [(c,T)])!(i-1) then nth\\_append to get v!(i-1-|u2|).\<close>
    have hw'_step1: "w' ! i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
      unfolding w'_def using hi0 by (by100 simp)
    have him1_ge: "i - 1 \<ge> length (rev (map top1_inverse_edge u2))" using \<open>i - 1 \<ge> length u2\<close> by (by100 simp)
    have hw'_step2: "(rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1) =
      (v @ [(c, True)]) ! (i - 1 - length u2)"
      using nth_append_second[OF him1_ge] by (by100 simp)
    have "i - 1 - length u2 < length v" using him1_lt \<open>i - 1 \<ge> length u2\<close> by (by100 linarith)
    hence hw'_step3: "(v @ [(c, True)]) ! (i - 1 - length u2) = v ! (i - 1 - length u2)"
      using nth_append_first by (by100 blast)
    have hw'i: "w' ! i = v ! (i - 1 - length u2)"
      using hw'_step1 hw'_step2 hw'_step3 by (by100 simp)
    \<comment> \<open>w!(i+1) = v!(i+1 - (2+|u2|)) = v!(i-1-|u2|).\<close>
    have "i + 1 \<ge> 2 + length u2" using hige unfolding k_def by (by100 linarith)
    hence "i + 1 \<ge> length ([(a, True)] @ u2 @ [(a, True)])" by (by100 simp)
    hence hw_step: "w ! (i + 1) = v ! (i + 1 - (2 + length u2))"
      unfolding w_def using nth_append_second[of "[(a,True)] @ u2 @ [(a,True)]" "i+1" v]
      by (by100 simp)
    have "i + 1 - (2 + length u2) = i - 1 - length u2" using hige unfolding k_def by (by100 linarith)
    hence hw_i1: "w ! (i + 1) = v ! (i - 1 - length u2)" using hw_step by (by100 simp)
    show ?thesis using hw'i hw_i1 by (by100 simp)
  qed
  hence h5: "fst (w' ! i) = fst (w ! (i+1))" and h6: "snd (w' ! i) = snd (w ! (i+1))"
    by (by100 simp)+
  show ?thesis
    apply (rule exI[of _ "Suc i"], rule exI[of _ False])
    using h1 h2 h3 h4 h5 h6 hige unfolding k_def by (by5000 simp)
qed

\<comment> \<open>C9 TRANSPORT (expert audit 39 Step 2): translate old C9 to target C9
   via sigma dictionary orientation flags.\<close>
lemma paste_sigma_non_c_C9_transport:
  fixes w w' :: "('c \<times> bool) list"
  assumes hlbl_i: "fst (w' ! i) = fst (w ! i_old)"
      and hsnd_i: "(snd (w' ! i) = snd (w ! i_old)) = (\<not> ri)"
      and hpar_i: "ti_old = (if ri then 1 - (t::real) else t)"
      and hlbl_j: "fst (w' ! j) = fst (w ! j_old)"
      and hsnd_j: "(snd (w' ! j) = snd (w ! j_old)) = (\<not> rj)"
      and hpar_j: "tj_old = (if rj then 1 - (s::real) else s)"
      and hold: "(i_old = j_old \<and> ti_old = tj_old)
          \<or> (fst (w ! i_old) = fst (w ! j_old) \<and>
             (if snd (w ! i_old) = snd (w ! j_old) then tj_old = ti_old else tj_old = 1 - ti_old))"
  shows "(i_old = j_old \<and> t = s)
      \<or> (fst (w' ! i) = fst (w' ! j) \<and>
         (if snd (w' ! i) = snd (w' ! j) then s = t else s = 1 - t))"
proof -
  \<comment> \<open>Helper: sign relation between target and old scheme via orientation flags.\<close>
  have hsign_eq: "i_old = j_old \<or> snd (w ! i_old) = snd (w ! j_old)
    \<Longrightarrow> (snd (w' ! i) = snd (w' ! j)) = (ri = rj)"
    using hsnd_i hsnd_j by (cases ri; cases rj; cases "snd (w ! i_old)"; cases "snd (w ! j_old)") simp_all
  have hsign_neq: "snd (w ! i_old) \<noteq> snd (w ! j_old)
    \<Longrightarrow> (snd (w' ! i) = snd (w' ! j)) = (ri \<noteq> rj)"
    using hsnd_i hsnd_j by (cases ri; cases rj; cases "snd (w ! i_old)"; cases "snd (w ! j_old)") simp_all
  \<comment> \<open>Helper: parameter transport via if-unfolding.\<close>
  have hpar_same: "ti_old = tj_old \<Longrightarrow> if ri = rj then t = s else s = 1 - t"
  proof (cases ri; cases rj)
    assume "ri" "rj" "ti_old = tj_old"
    have hts: "t = s"
    proof -
      have "1 - t = 1 - s" using hpar_i hpar_j \<open>ri\<close> \<open>rj\<close> \<open>ti_old = tj_old\<close> by (by100 simp)
      thus ?thesis by (by100 algebra)
    qed
    thus ?thesis using \<open>ri\<close> \<open>rj\<close> by (by100 simp)
  next
    assume "ri" "\<not>rj" "ti_old = tj_old"
    have "ti_old = 1 - t" using hpar_i \<open>ri\<close> by (by100 simp)
    moreover have "tj_old = s" using hpar_j \<open>\<not>rj\<close> by (by100 simp)
    ultimately have "s = 1 - t" using \<open>ti_old = tj_old\<close> by (by100 simp)
    thus ?thesis using \<open>ri\<close> \<open>\<not>rj\<close> by (by100 simp)
  next
    assume "\<not>ri" "rj" "ti_old = tj_old"
    have "ti_old = t" using hpar_i \<open>\<not>ri\<close> by (by100 simp)
    moreover have "tj_old = 1 - s" using hpar_j \<open>rj\<close> by (by100 simp)
    ultimately have "s = 1 - t" using \<open>ti_old = tj_old\<close> by (by100 simp)
    thus ?thesis using \<open>\<not>ri\<close> \<open>rj\<close> by (by100 simp)
  next
    assume "\<not>ri" "\<not>rj" "ti_old = tj_old"
    have "ti_old = t" using hpar_i \<open>\<not>ri\<close> by (by100 simp)
    moreover have "tj_old = s" using hpar_j \<open>\<not>rj\<close> by (by100 simp)
    ultimately have "t = s" using \<open>ti_old = tj_old\<close> by (by100 simp)
    thus ?thesis using \<open>\<not>ri\<close> \<open>\<not>rj\<close> by (by100 simp)
  qed
  have hpar_diff: "tj_old = 1 - ti_old \<Longrightarrow> if ri = rj then s = 1 - t else t = s"
  proof (cases ri; cases rj)
    assume "ri" "rj" "tj_old = 1 - ti_old"
    have "ti_old = 1 - t" using hpar_i \<open>ri\<close> by (by100 simp)
    moreover have "tj_old = 1 - s" using hpar_j \<open>rj\<close> by (by100 simp)
    ultimately have "s = 1 - t" using \<open>tj_old = 1 - ti_old\<close> by (by100 simp)
    thus ?thesis using \<open>ri\<close> \<open>rj\<close> by (by100 simp)
  next
    assume "ri" "\<not>rj" "tj_old = 1 - ti_old"
    have "ti_old = 1 - t" using hpar_i \<open>ri\<close> by (by100 simp)
    moreover have "tj_old = s" using hpar_j \<open>\<not>rj\<close> by (by100 simp)
    ultimately have "t = s" using \<open>tj_old = 1 - ti_old\<close> by (by100 simp)
    thus ?thesis using \<open>ri\<close> \<open>\<not>rj\<close> by (by100 simp)
  next
    assume "\<not>ri" "rj" "tj_old = 1 - ti_old"
    have "ti_old = t" using hpar_i \<open>\<not>ri\<close> by (by100 simp)
    moreover have "tj_old = 1 - s" using hpar_j \<open>rj\<close> by (by100 simp)
    ultimately have "t = s" using \<open>tj_old = 1 - ti_old\<close> by (by100 simp)
    thus ?thesis using \<open>\<not>ri\<close> \<open>rj\<close> by (by100 simp)
  next
    assume "\<not>ri" "\<not>rj" "tj_old = 1 - ti_old"
    have "ti_old = t" using hpar_i \<open>\<not>ri\<close> by (by100 simp)
    moreover have "tj_old = s" using hpar_j \<open>\<not>rj\<close> by (by100 simp)
    ultimately have "s = 1 - t" using \<open>tj_old = 1 - ti_old\<close> by (by100 simp)
    thus ?thesis using \<open>\<not>ri\<close> \<open>\<not>rj\<close> by (by100 simp)
  qed
  \<comment> \<open>Main proof: case split on old C9 conclusion.\<close>
  from hold show ?thesis
  proof (elim disjE conjE)
    assume "i_old = j_old" "ti_old = tj_old"
    have "fst (w' ! i) = fst (w' ! j)" using hlbl_i hlbl_j \<open>i_old = j_old\<close> by (by100 simp)
    moreover have "if snd (w' ! i) = snd (w' ! j) then s = t else s = 1 - t"
      using hsign_eq[OF disjI1[OF \<open>i_old = j_old\<close>]] hpar_same[OF \<open>ti_old = tj_old\<close>] by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  next
    assume hlbl_old: "fst (w ! i_old) = fst (w ! j_old)"
      and hpar_old: "if snd (w ! i_old) = snd (w ! j_old) then tj_old = ti_old else tj_old = 1 - ti_old"
    have hlbl: "fst (w' ! i) = fst (w' ! j)" using hlbl_i hlbl_j hlbl_old by (by100 simp)
    have "if snd (w' ! i) = snd (w' ! j) then s = t else s = 1 - t"
    proof (cases "snd (w ! i_old) = snd (w ! j_old)")
      case True
      hence "ti_old = tj_old" using hpar_old by (by100 simp)
      from hpar_same[OF this] hsign_eq[OF disjI2[OF True]]
      show ?thesis by (by100 simp)
    next
      case False
      hence "tj_old = 1 - ti_old" using hpar_old by (by100 simp)
      from hpar_diff[OF this] hsign_neq[OF False]
      show ?thesis by (by100 simp)
    qed
    with hlbl show ?thesis by (by100 blast)
  qed
qed

\<comment> \<open>PHI\\_L CRAMER EVALUATION: given the LEAST sector j, the Cramer computation
   in phi\\_L evaluates to paste\\_sigma.
   For j = 1 (i=0 case): uses cramer\\_on\\_triangle\\_base\\_edge (s=t, t\\_par=0).
   For j = i (1\\<le>i<k): uses cramer\\_on\\_triangle\\_edge (s=1-t, t\\_par=t).\<close>
\<comment> \<open>phi\\_L\\_cramer\\_gives\\_sigma: After sector selection (LEAST = j), the Cramer computation
   in phi\\_L evaluates to paste\\_sigma. This is the algebraic core of hphi\\_L\\_sigma.
   Proved using cramer\\_on\\_triangle\\_edge (j=i, i\\<ge>1) or cramer\\_on\\_triangle\\_base\\_edge (j=1, i=0).\<close>

lemma theorem_76_1_paste_chain:
  assumes hq: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and hfresh_c: "c \<notin> fst ` set ([(a, True)] @ u2 @ [(a, True)] @ v)"
      and ha_fresh_u2: "a \<notin> fst ` set u2"
      and ha_fresh_v: "a \<notin> fst ` set v"
  shows "top1_quotient_of_scheme_on Y TY
    ([(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)])"
proof (cases "u2 = []")
  case True
  \<comment> \<open>DEGENERATE CASE: u2 = []. Source: [(a,T),(a,T)] @ v. Target: [(c,T)] @ v @ [(c,T)].
     k = 1, so left fan has no sectors. The paste-chain operation is a simple
     edge-pair relabel + rotation. Proof sorry'd: needs separate argument.\<close>
  \<comment> \<open>u2 = []: source = [(a,T),(a,T)] @ v, target = [(c,T)] @ v @ [(c,T)].
     Step 1: Relabel a \\<to> c. Gives [(c,T),(c,T)] @ v' where v' = map(a\\<to>c) v.
     Step 2: Rotate. [(c,T),(c,T)] @ v' \\<to> [(c,T)] @ v' @ [(c,T)].
     Step 3: If a \\<notin> fst ` set v, then v' = v. Done.
     Step 4: If a \\<in> fst ` set v, need separate argument.\<close>
  have hTarget: "?thesis = top1_quotient_of_scheme_on Y TY ([(c, True)] @ v @ [(c, True)])"
    using True by simp
  have hSource: "top1_quotient_of_scheme_on Y TY ([(a, True), (a, True)] @ v)"
    using hq True by simp
  \<comment> \<open>c is fresh in the source.\<close>
  have hc_fresh: "c \<notin> fst ` set ([(a, True), (a, True)] @ v)"
    using hfresh_c True by simp
  hence hc_ne_a: "c \<noteq> a" by (by100 auto)
  \<comment> \<open>Relabel a \\<to> c.\<close>
  from quotient_of_scheme_relabel_fresh[OF hSource hc_fresh hc_ne_a]
  have h1: "top1_quotient_of_scheme_on Y TY (map (\<lambda>(l,b). (if l = a then c else l, b)) ([(a, True), (a, True)] @ v))" .
  have h1_simp: "map (\<lambda>(l,b). (if l = a then c else l, b)) ([(a, True), (a, True)] @ v)
    = [(c, True), (c, True)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) v"
    by (by100 simp)
  \<comment> \<open>Rotate: [(c,T),(c,T)] @ v' \\<to> [(c,T)] @ v' @ [(c,T)].\<close>
  have h2: "top1_quotient_of_scheme_on Y TY ([(c, True), (c, True)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) v)"
    using h1 h1_simp by simp
  from quotient_of_scheme_rotate[OF h2]
  have h3: "top1_quotient_of_scheme_on Y TY
      (map (\<lambda>(l,b). (if l = a then c else l, b)) v @ [(c, True), (c, True)])" by simp
  \<comment> \<open>h3 has v' @ [(c,T),(c,T)]. Split as (v' @ [(c,T)]) @ [(c,T)] and rotate.\<close>
  have h3_rewrite: "map (\<lambda>(l,b). (if l = a then c else l, b)) v @ [(c, True), (c, True)]
      = (map (\<lambda>(l,b). (if l = a then c else l, b)) v @ [(c, True)]) @ [(c, True)]" by simp
  from quotient_of_scheme_rotate[OF h3[unfolded h3_rewrite]]
  have h4: "top1_quotient_of_scheme_on Y TY
      ([(c, True)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) v @ [(c, True)])" by simp
  \<comment> \<open>If a \\<notin> fst ` set v, then the relabeled v equals v.\<close>
  \<comment> \<open>Need: map(a\\<to>c) v = v. Requires a \\<notin> fst ` set v.
     For proper schemes (used by classification): a appears exactly twice at positions 0,1.
     For general case: sorry.\<close>
  have hrelabel_v: "map (\<lambda>(l,b). (if l = a then c else l, b)) v = v"
  proof (rule map_idI)
    fix e assume "e \<in> set v" hence "fst e \<noteq> a" using ha_fresh_v by (by100 auto)
    thus "(\<lambda>(l,b). (if l = a then c else l, b)) e = e" by (cases e) simp
  qed
  have "top1_quotient_of_scheme_on Y TY ([(c, True)] @ v @ [(c, True)])"
    using h4 hrelabel_v by simp
  thus ?thesis using True by simp
next
  case False hence hu2_ne: "u2 \<noteq> []" .
  hence hk_ge2: "1 + length u2 \<ge> 2" by (cases u2) simp+
  show ?thesis
  proof (cases "v = []")
    case True
    \<comment> \<open>DEGENERATE CASE: v = []. Source: [(a,T)] @ u2 @ [(a,T)].
       Target: [(c,T)] @ rev(inv(u2)) @ [(c,T)].
       Proof: invert source \\<to> [(a,F)] @ rev(inv(u2)) @ [(a,F)].
       Relabel a\\<to>c \\<to> [(c,F)] @ rev(inv(u2)) @ [(c,F)].
       Flip label c \\<to> [(c,T)] @ rev(inv(u2)) @ [(c,T)].\<close>
    have hSource_v: "top1_quotient_of_scheme_on Y TY ([(a, True)] @ u2 @ [(a, True)])"
      using hq True by simp
    \<comment> \<open>Step 1: Invert: rev(inv(source)) has same quotient Y.\<close>
    from quotient_of_scheme_invert[OF hSource_v]
    have h_inv: "top1_quotient_of_scheme_on Y TY
        (rev (map top1_inverse_edge ([(a, True)] @ u2 @ [(a, True)])))" .
    have h_inv_simp: "rev (map top1_inverse_edge ([(a, True)] @ u2 @ [(a, True)]))
        = [(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)]"
      unfolding top1_inverse_edge_def by simp
    have h1: "top1_quotient_of_scheme_on Y TY
        ([(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)])"
      using h_inv h_inv_simp by simp
    \<comment> \<open>Step 2: Relabel a\\<to>c. c is fresh in the inverted scheme.\<close>
    have hc_fresh_inv: "c \<notin> fst ` set ([(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)])"
    proof -
      have "fst ` set ([(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)])
        = {a} \<union> fst ` set (rev (map top1_inverse_edge u2))"
        by (by100 auto)
      also have "fst ` set (rev (map top1_inverse_edge u2)) = fst ` set u2"
        unfolding top1_inverse_edge_def by (by100 force)
      finally show ?thesis using hfresh_c True by (by100 auto)
    qed
    have hc_ne_a: "c \<noteq> a" using hfresh_c by (by100 auto)
    from quotient_of_scheme_relabel_fresh[OF h1 hc_fresh_inv hc_ne_a]
    have h2: "top1_quotient_of_scheme_on Y TY
        (map (\<lambda>(l,b). (if l = a then c else l, b)) ([(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)]))" .
    have h2_simp: "map (\<lambda>(l,b). (if l = a then c else l, b)) ([(a, False)] @ rev (map top1_inverse_edge u2) @ [(a, False)])
        = [(c, False)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)) @ [(c, False)]"
      by (by100 simp)
    have h3: "top1_quotient_of_scheme_on Y TY
        ([(c, False)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)) @ [(c, False)])"
      using h2 h2_simp by simp
    \<comment> \<open>Step 3: Flip label c: changes (c,F)\\<to>(c,T) at all c-positions.
       Since c is fresh in u2, this only affects the two c-edges.\<close>
    from quotient_scheme_flip_label[OF h3, of c]
    have h4: "top1_quotient_of_scheme_on Y TY
        (map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) ([(c, False)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)) @ [(c, False)]))" .
    \<comment> \<open>Simplify: the flip of c changes (c,F) to (c,T) and doesn't affect u2 labels.\<close>
    have "map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) ([(c, False)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)) @ [(c, False)])
        = [(c, True)] @ map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) (map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2))) @ [(c, True)]"
      by simp
    \<comment> \<open>The inner map: since a \\<notin> fst ` set u2, c doesn't appear in the relabeled inner edges.
       So the c-flip only affects the outer [(c,F)] markers.\<close>
    \<comment> \<open>ha\\_fresh\\_u2 from theorem assumptions.\<close>
    have ha_fresh_inv: "a \<notin> fst ` set (rev (map top1_inverse_edge u2))"
      using ha_fresh_u2 unfolding top1_inverse_edge_def by (by100 force)
    \<comment> \<open>Since a \\<notin> labels of inv(u2), relabeling a\\<to>c has no effect on inv(u2).\<close>
    have hrelabel_noop: "map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2))
        = rev (map top1_inverse_edge u2)"
    proof (rule map_idI)
      fix e assume "e \<in> set (rev (map top1_inverse_edge u2))"
      hence "fst e \<noteq> a" using ha_fresh_inv by (by100 auto)
      thus "(\<lambda>(l,b). (if l = a then c else l, b)) e = e"
        by (cases e) simp
    qed
    \<comment> \<open>Since c \\<notin> labels of inv(u2), flipping c has no effect on inv(u2).\<close>
    have hc_fresh_inv: "c \<notin> fst ` set (rev (map top1_inverse_edge u2))"
    proof -
      have "fst ` set (rev (map top1_inverse_edge u2)) = fst ` set u2"
        unfolding top1_inverse_edge_def by (by100 force)
      thus ?thesis using hfresh_c True by (by100 auto)
    qed
    have hflip_noop: "map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) (rev (map top1_inverse_edge u2))
        = rev (map top1_inverse_edge u2)"
    proof (rule map_idI)
      fix e assume "e \<in> set (rev (map top1_inverse_edge u2))"
      hence "fst e \<noteq> c" using hc_fresh_inv by (by100 auto)
      thus "(\<lambda>(l,b). (l, if l = c then \<not>b else b)) e = e"
        by (cases e) simp
    qed
    moreover have "map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) (map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)))
        = rev (map top1_inverse_edge u2)"
      using hrelabel_noop hflip_noop by simp
    ultimately have "map (\<lambda>(l,b). (l, if l = c then \<not>b else b)) ([(c, False)] @ map (\<lambda>(l,b). (if l = a then c else l, b)) (rev (map top1_inverse_edge u2)) @ [(c, False)])
        = [(c, True)] @ rev (map top1_inverse_edge u2) @ [(c, True)]"
      by simp
    with h4 have "top1_quotient_of_scheme_on Y TY
        ([(c, True)] @ rev (map top1_inverse_edge u2) @ [(c, True)])"
      by simp
    thus ?thesis using True by simp
  next
    case hv_ne: False
    hence hk_lt_nm1: "Suc (length u2) < length ([(a, True)] @ u2 @ [(a, True)] @ v) - 1"
      by (cases v) simp+
  show ?thesis
  proof -
  let ?w = "[(a, True)] @ u2 @ [(a, True)] @ v"
  let ?n = "length ?w"
  let ?k = "1 + length u2"  \<comment> \<open>Position of the diagonal cut: v\\_0 to v\\_{?k}.\<close>
  let ?w' = "[(c, True)] @ rev (map top1_inverse_edge u2) @ v @ [(c, True)]"
  \<comment> \<open>Step 1: Extract polygon P with vertices vx/vy and quotient map q.\<close>
  from scheme_a_pair_identification[OF hq]
  obtain P q vx vy where
      hP: "top1_is_polygonal_region_on P ?n"
    and hqmap: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hv_in: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC7_a: "\<forall>t\<in>I_set.
       q ((1-t) * vx 0 + t * vx 1, (1-t) * vy 0 + t * vy 1)
     = q ((1-t) * vx ?k + t * vx (Suc ?k mod ?n),
          (1-t) * vy ?k + t * vy (Suc ?k mod ?n))"
    by (by100 blast)
  \<comment> \<open>Step 2: Vertex identifications from the a-pair.
     q(v\\_0) = q(v\\_{?k}) and q(v\\_1) = q(v\\_{Suc ?k mod n}).\<close>
  have h0_in: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
  have h1_in: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
  have hq_v0: "q (vx 0, vy 0) = q (vx ?k, vy ?k)"
    using hC7_a[rule_format, OF h0_in] by (by100 simp)
  have hq_v1: "q (vx 1, vy 1) = q (vx (Suc ?k mod ?n), vy (Suc ?k mod ?n))"
    using hC7_a[rule_format, OF h1_in] by (by100 simp)
  \<comment> \<open>Step 3: Construct pasted polygon P' for the target scheme w'.
     P' is obtained by cutting P along diagonal v\\_0 to v\\_{?k},
     flipping Q1, permuting Q2, and pasting along the a-edges.
     Geometrically: the two sub-polygons are rearranged and combined.
     For formalization: use scheme\\_quotient\\_exists for proper schemes,
     or construct P' directly as a regular n-gon.\<close>
  \<comment> \<open>Step 4: Define quotient map q': P' \\<to> Y.
     q' is defined piecewise on the two halves of P'
     (separated by the diagonal of P' from the paste junction):
     - On Q1-flipped half: q' = q \\<circ> (un-flip back to Q1 \\<subset> P)
     - On Q2-permuted half: q' = q \\<circ> (un-permute back to Q2 \\<subset> P)
     At the junction (former a-edges): both pieces give the same q-value
     by the a-pair identification (hC7\\_a).
     At the c-edges (diagonal): both pieces map to the diagonal of P,
     approaching from opposite sides.\<close>
  \<comment> \<open>Step 5: Verify that q' is a valid quotient map for scheme w' on P'.
     C1: P' is a valid polygon (from construction)
     C2: q' is a quotient map (continuous closed surjection from compact to Hausdorff)
     C7: edge identifications match w' (c-pair from diagonal, other labels from original)
     C8: interior injectivity (from q's C8 + disjointness of the two halves)
     C9: edge-interior (from original C9 + the piecewise construction)\<close>
  \<comment> \<open>KEY DISCOVERY: The piecewise map IS continuous WITHOUT one-vertex-class.
     At internal junction (former a-edges): C7 with parameter (1-s) gives
       q(first\\_a(1-s)) = q(second\\_a(1-s)), which is exactly what the paste matching needs.
     At paste vertices: C7(t=0) gives q(v\\_0) = q(v\\_{1+|u2|}) and
       C7(t=1) gives q(v\\_1) = q(v\\_{2+|u2| mod n}),
     which are exactly the vertex pairs created by the opposite-exponent paste.\<close>
  \<comment> \<open>The full geometric construction of P' and q' requires:
     1. Define Q1 = sub-polygon {v\\_0,...,v\\_{1+|u2|}} and Q2 = sub-polygon {v\\_{1+|u2|},...,v\\_0}
     2. Q1 and Q2 are valid polygonal regions (from sub\\_polygon\\_in\\_polygon + convexity)
     3. Define pasted polygon P' by geometric placement of Q1-flipped next to Q2-permuted
     4. Define q': P' \\<to> Y piecewise (Q1 half \\<to> Q1 \\<subset> P, Q2 half \\<to> Q2 \\<subset> P)
     5. Verify C1-C11 for P', q', target scheme w'
     The continuity at junctions follows from hC7\\_a (steps hq\\_v0, hq\\_v1 above).\<close>
  \<comment> \<open>Step 6: Extract full C1-C11 from P to get all conditions needed.\<close>
  from quotient_of_scheme_extract_vx[OF hq]
  obtain P2 q2 vx2 vy2 where
      hP2: "top1_is_polygonal_region_on P2 ?n"
    and hq2: "top1_quotient_map_on P2
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) Y TY q2"
    and hC3_2: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
    and hv2_in: "\<forall>i<?n. (vx2 i, vy2 i) \<in> P2"
    and hC5_2: "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
    and hC6_2: "\<forall>i<?n. \<forall>j<?n.
          i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
          (\<forall>s\<in>{0<..<(1::real)}. \<forall>t\<in>{0<..<(1::real)}.
             \<not>(((1-s) * vx2 i + s * vx2 (Suc i mod ?n), (1-s) * vy2 i + s * vy2 (Suc i mod ?n))
              = ((1-t) * vx2 j + t * vx2 (Suc j mod ?n), (1-t) * vy2 j + t * vy2 (Suc j mod ?n))))"
    and hC7_2: "\<forall>i<?n. \<forall>j<?n. fst (?w!i) = fst (?w!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q2 ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
         = (if snd(?w!i) = snd(?w!j)
            then q2 ((1-t)*vx2 j + t*vx2(Suc j mod ?n), (1-t)*vy2 j + t*vy2(Suc j mod ?n))
            else q2 (t*vx2 j + (1-t)*vx2(Suc j mod ?n), t*vy2 j + (1-t)*vy2(Suc j mod ?n))))"
    and hC8_2: "\<forall>p\<in>P2. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P2. q2 p = q2 p' \<longrightarrow> p = p')"
    and hC9_2: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
          q2 ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
        = q2 ((1-s)*vx2 j + s*vx2(Suc j mod ?n), (1-s)*vy2 j + s*vy2(Suc j mod ?n))
        \<longrightarrow> (i = j \<and> t = s) \<or> (fst(?w!i) = fst(?w!j) \<and>
              (if snd(?w!i) = snd(?w!j) then s = t else s = 1 - t))"
    and hC10_2: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx2 j) / real ?n;
                           cy = (\<Sum>j<?n. vy2 j) / real ?n
         in (vx2 i - cx) * (vy2 (Suc i mod ?n) - cy)
          - (vy2 i - cy) * (vx2 (Suc i mod ?n) - cx) > 0"
    and hC11_2: "\<forall>i<?n. \<forall>kk<?n. kk \<noteq> i \<longrightarrow> kk \<noteq> Suc i mod ?n \<longrightarrow>
          (vx2 kk - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
          - (vy2 kk - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0"
    by (rule quotient_of_scheme_extract_vx[OF hq])
  \<comment> \<open>PROOF OF THEOREM 76.1 (CUT+FLIP+PASTE CHAIN).
     Strategy: use SAME polygon P2 with vertices vx2/vy2 as witness for scheme w'.
     Define new quotient map g: P2 \\<to> Y that follows the target scheme w'.

     BOUNDARY MAP g (edge-by-edge):
     - Edge 0 of P2 at param t (c,T): g = q2(diagonal from v\\_0 to v\\_{k+1} at param t)
       = q2((1-t)*vx2 0+t*vx2(k+1), (1-t)*vy2 0+t*vy2(k+1))
     - Edge i (1\\<le>i\\<le>k) at param t (inv(u2)): g = q2(REVERSED edge k+1-i at param 1-t)
       = q2(t*vx2(k+1-i)+(1-t)*vx2(k+2-i), t*vy2(k+1-i)+(1-t)*vy2(k+2-i))
     - Edge i (k+1\\<le>i\\<le>n-2) at param t (v): g = q2(original edge i+1 at param t)
       = q2((1-t)*vx2(i+1)+t*vx2(Suc(i+1) mod n), (1-t)*vy2(i+1)+t*vy2(Suc(i+1) mod n))
     - Edge n-1 at param t (c,T): SAME as edge 0 (same diagonal, same parameter)
       = q2((1-t)*vx2 0+t*vx2(k+1), (1-t)*vy2 0+t*vy2(k+1))

     INTERIOR: half-and-half extension via sub-polygon homeomorphisms.
     Left half (edges 0..k + dividing line) maps to Q1 = conv(v\\_0,...,v\\_{k+1}).
     Right half (edges k+1..n-1 + dividing line) maps to Q2 = conv(v\\_{k+1},...,v\\_0).
     At dividing line: left gives q2(edge\\_0(s)), right gives q2(edge\\_{k+1}(s)).
     These match by C7 for the a-pair (hC7\\_a at param s). \\<checkmark>

     JUNCTION CONTINUITY (all verified):
     v'(0): edge(n-1,1)=q2(v(k+1)), edge(0,0)=q2(v(0)). Match by hq\\_v0.
     v'(1): edge(0,1)=q2(v(k+1)), edge(1,0)=q2(v(k+1)).
     v'(i) (2<=i<=k): edge(i-1,1)=q2(v(k+2-i)), edge(i,0)=q2(v(k+2-i)).
     v'(k+1): edge(k,1)=q2(v(1)), edge(k+1,0)=q2(v(k+2)). Match by hq\\_v1.
     v'(i) (k+2<=i<=n-2): edge(i-1,1)=q2(v(i+1)), edge(i,0)=q2(v(i+1)).
     v'(n-1): edge(n-2,1)=q2(v(0)), edge(n-1,0)=q2(v(0)).

     C7 (target scheme w'):
     - c-pair (0,n-1): both map to q2(diagonal(t)). Same exponent \\<to> same param. \\<checkmark>
     - inv(u2) pairs: target param t \\<to> original param (1-t). Double negation
       (reversed param + flipped exponent) makes C7 work. \\<checkmark>
     - v pairs: direct from original C7 at shifted indices. \\<checkmark>
     - Cross pairs (inv(u2) vs v): reversed param + flipped exponent cancel. \\<checkmark>
     - c vs non-c: can't have same label (c is fresh). \\<checkmark>

     C8 (interior injectivity): half-and-half maps each half injectively.
     Interior Q1 and Q2 are disjoint. q2 injective on interior by C8. \\<checkmark>

     C9 (edge-edge injectivity):
     - c vs non-c: diagonal is interior, edges are boundary. C8 separates. \\<checkmark>
     - c vs c: q2 injective on diagonal (interior). \\<checkmark>
     - non-c pairs: follows from original C9. \\<checkmark>\<close>
  \<comment> \<open>Step 10: Construct the witness for top1\\_quotient\\_of\\_scheme\\_on Y TY w'.
     WITNESS: P = P2 (same polygon), vx = vx2, vy = vy2.
     Need a new quotient map g: P2 \\<to> Y defined piecewise.
     BOUNDARY MAP g(edge'(i, t)):
     - i = 0 or n-1 (c-pair): q2((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) [diagonal]
     - 1 \\<le> i \\<le> |u2| (inv(u2)): q2(t*vx2(?k-i) + (1-t)*vx2(?k+1-i), ...) [reversed u2 edge]
     - |u2|+1 \\<le> i \\<le> n-2 (v): q2((1-t)*vx2(i+1) + t*vx2(Suc(i+1) mod n), ...) [original v edge]
     INTERIOR: half-and-half piecewise extension through sub-polygons Q1, Q2.\<close>
  \<comment> \<open>CONSTRUCTION: define boundary map g on P2 (same polygon, new quotient map).
     g(edge\\_i, t) for target scheme w':
     - i = 0 or n-1 (c-pair): q2((1-t)*v0 + t*v(k), (1-t)*vy0 + t*vy(k))
     - 1 \\<le> i \\<le> |u2| (inv(u2)): q2(t*v(k-i) + (1-t)*v(k+1-i), ...)
     - |u2|+1 \\<le> i \\<le> n-2 (v): q2((1-t)*v(i+1) + t*v(Suc(i+1) mod n), ...)
     Interior: half-and-half via sub-polygon homeomorphisms (Q1 left, Q2 right).
     All junction continuity, C7, C8, C9 verified mathematically (see comments above).\<close>
  \<comment> \<open>Step 11: Extract topology\\_on\\_strict from hq.\<close>
  have htopo_Y: "is_topology_on_strict Y TY"
    using hq unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hlen_eq: "length ?w' = ?n" by (by100 simp)
  \<comment> \<open>Step 12: Construct the map g: P2 -> Y satisfying C7/C8/C9 for scheme w'.
     g is defined piecewise on the boundary:
     - c-edges (0, n-1): map to the diagonal q2(v0..v(k+1))
     - inv(u2) edges (1..k): map to reversed original u2 edges
     - v edges (k+1..n-2): map to original v edges
     Interior: half-and-half extension through sub-polygons.
     The construction and verification of all conditions uses the half-and-half
     approach documented in the PROOF OF THEOREM 76.1 comment block above.\<close>
  \<comment> \<open>For now: sorry the full construction. The mathematical proof is complete
     (all junction continuity, C7 cases, C8, C9 verified in comments above).
     The formal verification requires defining g, proving continuity,
     and verifying C7/C8/C9 as separate sub-goals (~380 lines total).

     KEY FACT: the proof uses ONLY the following from the original quotient:
     - hC7\\_2: edge identifications for scheme w (especially the a-pair)
     - hC8\\_2: interior injectivity of q2
     - hC9\\_2: edge-edge injectivity of q2
     - hq\\_v0, hq\\_v1: vertex identifications from the a-pair
     All other conditions (C1-C6, C10, C11) are pure polygon properties
     inherited from P2 unchanged.\<close>
  \<comment> \<open>Unfold the definition and provide witnesses.\<close>
  show "top1_quotient_of_scheme_on Y TY ?w'"
    unfolding top1_quotient_of_scheme_on_def
  proof (intro conjI)
    show "is_topology_on_strict Y TY" by (rule htopo_Y)
  next
    \<comment> \<open>Need: \\<exists>P q vx vy. C1 \\<and> C2 \\<and> ... \\<and> C11 for scheme w' on P with map q.
       Witness: P = P2, q = g (piecewise map), vx = vx2, vy = vy2.
       g is defined by the half-and-half construction:
       - On boundary: edge-by-edge map to original polygon (diagonal for c-edges)
       - On interior: piecewise extension through sub-polygon homeomorphisms\<close>
    \<comment> \<open>Witness: P = P2 (same polygon), vx = vx2, vy = vy2.
       g = the half-and-half piecewise quotient map (construction sorry'd).
       C1, C3-C6, C10, C11: inherit from P2 via hlen\\_eq (length w' = length w = n).
       C2, C7, C8, C9: need the new map g.\<close>
    \<comment> \<open>Inherit polygon properties from P2 (same polygon, same vertices, same length).\<close>
    have hC1': "top1_is_polygonal_region_on P2 (length ?w')"
      using hP2 hlen_eq by simp
    have hC3': "\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
      using hC3_2 hlen_eq by simp
    have hC4': "\<forall>i<length ?w'. (vx2 i, vy2 i) \<in> P2"
      using hv2_in hlen_eq by simp
    have hC5': "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<length ?w'. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<length ?w'. coeffs i) = 1
                     \<and> x = (\<Sum>i<length ?w'. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<length ?w'. coeffs i * vy2 i)}"
      using hC5_2 hlen_eq by simp
    \<comment> \<open>C6, C10, C11: polygon properties from hq, transferred via hlen\\_eq.
       These are the same polygon P2 with the same vertices, just different scheme length.\<close>
    have hC6': "\<forall>i<length ?w'. \<forall>j<length ?w'.
          i \<noteq> j \<longrightarrow> Suc i mod length ?w' \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length ?w' \<longrightarrow>
          (\<forall>s\<in>{0<..<(1::real)}. \<forall>t\<in>{0<..<(1::real)}.
             ((1-s) * vx2 i + s * vx2 (Suc i mod length ?w'),
              (1-s) * vy2 i + s * vy2 (Suc i mod length ?w'))
           \<noteq> ((1-t) * vx2 j + t * vx2 (Suc j mod length ?w'),
               (1-t) * vy2 j + t * vy2 (Suc j mod length ?w')))"
      using hC6_2 hlen_eq by simp
    have hC10': "\<forall>i<length ?w'. let cx = (\<Sum>j<length ?w'. vx2 j) / real (length ?w');
                               cy = (\<Sum>j<length ?w'. vy2 j) / real (length ?w')
         in (vx2 i - cx) * (vy2 (Suc i mod length ?w') - cy)
          - (vy2 i - cy) * (vx2 (Suc i mod length ?w') - cx) > 0"
      using hC10_2 hlen_eq by simp
    have hC11': "\<forall>i<length ?w'. \<forall>k<length ?w'.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length ?w' \<longrightarrow>
          (vx2 k - vx2 i) * (vy2 (Suc i mod length ?w') - vy2 i)
          - (vy2 k - vy2 i) * (vx2 (Suc i mod length ?w') - vx2 i) < 0"
      using hC11_2 hlen_eq by simp
    \<comment> \<open>C2 (quotient map g: P2 -> Y), C7, C8, C9 for scheme w' with map g.
       These require the full geometric half-and-half construction.
       Sorry'd: the mathematical argument is complete (see comments above).\<close>
    \<comment> \<open>The existential needs a quotient map q on P2 satisfying C2+C7+C8+C9.
       C7 is now proved (paste\\_chain\\_boundary\\_C7). C2/C8/C9 need the geometric construction.
       The geometric part requires defining q on the interior of P2 via half-and-half
       extension, proving continuity, surjectivity, and injectivity properties.
       For now: sorry the full existential. The C7 part can be closed once q is defined.\<close>
    show "\<exists>P q (vx::nat\<Rightarrow>real) vy.
        top1_is_polygonal_region_on P (length ?w')
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length ?w'. (vx i, vy i) \<in> P)
      \<and> P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length ?w'. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length ?w'. coeffs i) = 1
                       \<and> x = (\<Sum>i<length ?w'. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length ?w'. coeffs i * vy i)}
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'.
            i \<noteq> j \<longrightarrow> Suc i mod length ?w' \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length ?w' \<longrightarrow>
            (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
               ((1-s) * vx i + s * vx (Suc i mod length ?w'),
                (1-s) * vy i + s * vy (Suc i mod length ?w'))
             \<noteq> ((1-t) * vx j + t * vx (Suc j mod length ?w'),
                (1-t) * vy j + t * vy (Suc j mod length ?w'))))
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. fst (?w'!i) = fst (?w'!j) \<longrightarrow>
            (\<forall>t\<in>I_set.
               q ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                  (1-t) * vy i + t * vy (Suc i mod length ?w'))
             = (if snd (?w'!i) = snd (?w'!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length ?w'),
                        (1-t) * vy j + t * vy (Suc j mod length ?w'))
                else q (t * vx j + (1-t) * vx (Suc j mod length ?w'),
                        t * vy j + (1-t) * vy (Suc j mod length ?w')))))
      \<and> (\<forall>p\<in>P. (\<forall>i<length ?w'. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                          (1-t) * vy i + t * vy (Suc i mod length ?w')))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
      \<and> (\<forall>i<length ?w'. \<forall>j<length ?w'. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
              q ((1-t) * vx i + t * vx (Suc i mod length ?w'),
                 (1-t) * vy i + t * vy (Suc i mod length ?w'))
            = q ((1-s) * vx j + s * vx (Suc j mod length ?w'),
                 (1-s) * vy j + s * vy (Suc j mod length ?w'))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (?w'!i) = fst (?w'!j) \<and>
                 (if snd (?w'!i) = snd (?w'!j) then s = t else s = 1 - t)))
      \<and> (\<forall>i<length ?w'. let cx = (\<Sum>j<length ?w'. vx j) / real (length ?w');
                               cy = (\<Sum>j<length ?w'. vy j) / real (length ?w')
           in (vx i - cx) * (vy (Suc i mod length ?w') - cy)
            - (vy i - cy) * (vx (Suc i mod length ?w') - cx) > 0)
      \<and> (\<forall>i<length ?w'. \<forall>k<length ?w'.
            k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length ?w' \<longrightarrow>
            (vx k - vx i) * (vy (Suc i mod length ?w') - vy i)
            - (vy k - vy i) * (vx (Suc i mod length ?w') - vx i) < 0)"
    proof -
      \<comment> \<open>GEOMETRIC CONSTRUCTION: define g = q2 composed with phi piecewise on two halves.
         Half determined by cross product with diagonal v\\_0 to v\\_k.
         Left half: fan from v\\_0, reverse vertex mapping.
         Right half: fan from v\\_0, shift vertex mapping.
         g is continuous at the dividing line because C7 absorbs the jump.\<close>
      let ?k = "1 + length u2"
      \<comment> \<open>Define the half-and-half map phi: P2 -> P2 (DISCONTINUOUS at dividing line).
         Then g = q2 o phi is continuous.\<close>
      define cross_diag :: "real \<times> real \<Rightarrow> real" where
        "cross_diag p = (vx2 ?k - vx2 0) * (snd p - vy2 0)
                       - (vy2 ?k - vy2 0) * (fst p - vx2 0)" for p
      \<comment> \<open>Left half phi: for sector j (1<=j<k), Cramer coords in (v0, vj, v{j+1}),
         map to (v0, v{k+1-j}, v{k-j}).\<close>
      define phi_L :: "real \<times> real \<Rightarrow> real \<times> real" where
        "phi_L p = (let j = (LEAST j. 1 \<le> j \<and> j < ?k \<and>
            (vx2 j - vx2 0)*(snd p - vy2 0) - (vy2 j - vy2 0)*(fst p - vx2 0) \<ge> 0 \<and>
            (vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0) \<le> 0) in
          let ex = vx2 j - vx2 0; ey = vy2 j - vy2 0;
              fx = vx2(Suc j) - vx2 0; fy = vy2(Suc j) - vy2 0;
              det = ex*fy - ey*fx;
              dx = fst p - vx2 0; dy = snd p - vy2 0;
              s = (fy*dx - fx*dy)/det;
              t_par = (ex*dy - ey*dx)/det in
          ((1-s-t_par)*vx2 0 + s*vx2(?k+1-j) + t_par*vx2(?k-j),
           (1-s-t_par)*vy2 0 + s*vy2(?k+1-j) + t_par*vy2(?k-j)))" for p
      \<comment> \<open>Right half phi: for sector j (k<=j<n-1), Cramer coords in (v0, vj, v{j+1}),
         map to (vk, v{j+1}, v{(j+2) mod n}).\<close>
      define phi_R :: "real \<times> real \<Rightarrow> real \<times> real" where
        "phi_R p = (let j = (LEAST j. ?k \<le> j \<and> j < ?n - 1 \<and>
            (vx2 j - vx2 0)*(snd p - vy2 0) - (vy2 j - vy2 0)*(fst p - vx2 0) \<ge> 0 \<and>
            (vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0) \<le> 0) in
          let ex = vx2 j - vx2 0; ey = vy2 j - vy2 0;
              fx = vx2(Suc j) - vx2 0; fy = vy2(Suc j) - vy2 0;
              det = ex*fy - ey*fx;
              dx = fst p - vx2 0; dy = snd p - vy2 0;
              s = (fy*dx - fx*dy)/det;
              t_par = (ex*dy - ey*dx)/det in
          ((1-s-t_par)*vx2 ?k + s*vx2(Suc j) + t_par*vx2(Suc(Suc j) mod ?n),
           (1-s-t_par)*vy2 ?k + s*vy2(Suc j) + t_par*vy2(Suc(Suc j) mod ?n)))" for p
      \<comment> \<open>The piecewise map g = q2 o phi.\<close>
      define g where
        "g p = (if cross_diag p \<le> 0 then q2 (phi_L p) else q2 (phi_R p))" for p
      \<comment> \<open>Fan determinant positivity from v\\_0: cross(v\\_a - v\\_0, v\\_b - v\\_0) > 0 for 1 \\<le> a < b < n.
         Follows from C11\\_2 (all non-adjacent vertices on interior side of each edge).\<close>
      have hn_ge3: "?n \<ge> 3" using quotient_scheme_length_ge3[OF hq] .
      have hfan_det_0: "\<forall>a<?n. \<forall>b<?n. 1 \<le> a \<longrightarrow> a < b \<longrightarrow>
          (vx2 a - vx2 0) * (vy2 b - vy2 0) - (vy2 a - vy2 0) * (vx2 b - vx2 0) > 0"
        using convex_polygon_fan_det_from_v0[OF hn_ge3 hC11_2] .
      \<comment> \<open>KEY FACT: g on boundary edges equals q2 composed with sigma.
         PROOF PLAN (expert audit 36):
         For each target edge i at parameter t:
         (A) Left half (i < k): cross\\_diag(edge(i,t)) \\<le> 0 (proved: fan det antisymmetry + bilinearity).
             g = q2(phi\\_L). LEAST sector = i (proved: PL(i) holds, PL(j) false for j<i from fan det).
             Cramer coords (0, 1-t, t) from cramer\\_on\\_triangle\\_edge.
             phi\\_L result = (1-t)*v(k+1-i) + t*v(k-i) = sigma(i,t). QED.
         (B) Right half (i \\<ge> k): symmetric with phi\\_R.
         (C) Vertices (t=0,1): LEAST may differ but result matches by vertex identification.
         Infrastructure in place: hfan\\_det\\_0, cross2\\_plucker, cramer\\_on\\_triangle\\_edge/base\\_edge.\<close>
      \<comment> \<open>HELPER: cross\\_diag at edge(i,t) is \\<le> 0 for left half (i < k), \\<ge> 0 for right half (i \\<ge> k).
         Proof: cross\\_diag = (1-t)*cross(v\\_k-v\\_0, v\\_i-v\\_0) + t*cross(v\\_k-v\\_0, v\\_{i+1}-v\\_0).
         Left half: both terms \\<le> 0 from fan det antisymmetry. Right half: both \\<ge> 0.\<close>
      have hcd_left: "\<And>i t. i < ?k \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) \<le> 0"
      proof -
        fix i :: nat and t :: real assume hik: "i < ?k" and ht: "t \<in> I_set"
        have ht01: "t \<ge> 0 \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
        have ht_ge0: "t \<ge> 0" using ht01 by linarith
        have h1mt: "1 - t \<ge> 0" using ht01 by linarith
        \<comment> \<open>cross(v\\_k - v\\_0, v\\_i - v\\_0) \\<le> 0: zero for i=0, negative for i \\<ge> 1.\<close>
        have hcki: "(vx2 ?k - vx2 0) * (vy2 i - vy2 0) - (vy2 ?k - vy2 0) * (vx2 i - vx2 0) \<le> 0"
        proof (cases "i = 0")
          case True thus ?thesis by simp
        next
          case False hence hi1: "1 \<le> i" by linarith
          have hi_lt: "i < ?n" using hik by simp
          have hk_lt: "?k < ?n" by simp
          from hfan_det_0[rule_format, OF hi_lt hk_lt hi1 hik]
          have hpos: "(vx2 i - vx2 0)*(vy2 ?k - vy2 0) - (vy2 i - vy2 0)*(vx2 ?k - vx2 0) > 0" .
          moreover have "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)
            = -((vx2 i - vx2 0)*(vy2 ?k - vy2 0) - (vy2 i - vy2 0)*(vx2 ?k - vx2 0))"
            by (by100 algebra)
          ultimately have "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0) < 0"
            by linarith
          thus ?thesis by linarith
        qed
        \<comment> \<open>cross(v\\_k - v\\_0, v\\_{Suc i} - v\\_0) \\<le> 0: zero if Suc i = k, negative if Suc i < k.\<close>
        have hsi_lt: "Suc i < ?n" using hik by simp
        have hsi_mod: "Suc i mod ?n = Suc i" using hsi_lt by simp
        have hcksi: "(vx2 ?k - vx2 0) * (vy2 (Suc i mod ?n) - vy2 0)
            - (vy2 ?k - vy2 0) * (vx2 (Suc i mod ?n) - vx2 0) \<le> 0"
        proof (cases "Suc i = ?k")
          case True thus ?thesis using hsi_mod by simp
        next
          case False hence "Suc i < ?k" using hik by linarith
          hence "1 \<le> Suc i" by simp
          have hk_lt2: "?k < ?n" by simp
          from hfan_det_0[rule_format, OF hsi_lt hk_lt2 \<open>1 \<le> Suc i\<close> \<open>Suc i < ?k\<close>]
          have "(vx2 (Suc i) - vx2 0)*(vy2 ?k - vy2 0) - (vy2 (Suc i) - vy2 0)*(vx2 ?k - vx2 0) > 0" .
          moreover have "(vx2 ?k - vx2 0)*(vy2 (Suc i) - vy2 0) - (vy2 ?k - vy2 0)*(vx2 (Suc i) - vx2 0)
            = -((vx2 (Suc i) - vx2 0)*(vy2 ?k - vy2 0) - (vy2 (Suc i) - vy2 0)*(vx2 ?k - vx2 0))"
            by (by100 algebra)
          ultimately have "(vx2 ?k - vx2 0)*(vy2 (Suc i) - vy2 0) - (vy2 ?k - vy2 0)*(vx2 (Suc i) - vx2 0) < 0"
            by linarith
          thus ?thesis using hsi_mod by simp
        qed
        \<comment> \<open>Bilinearity: cross\\_diag = (1-t)*hcki + t*hcksi \\<le> 0.\<close>
        have "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = (vx2 ?k - vx2 0) * ((1-t)*vy2 i + t*vy2(Suc i mod ?n) - vy2 0)
          - (vy2 ?k - vy2 0) * ((1-t)*vx2 i + t*vx2(Suc i mod ?n) - vx2 0)"
          unfolding cross_diag_def by simp
        also have "\<dots> = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
          + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))"
          by (by100 algebra)
        finally have "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
          + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))" .
        moreover have "(1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) \<le> 0"
          using mult_nonneg_nonpos[of "1-t" "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)"]
                h1mt hcki by linarith
        moreover have "t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0)) \<le> 0"
          using mult_nonneg_nonpos[of t "(vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0)"]
                ht_ge0 hcksi by linarith
        ultimately show "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) \<le> 0"
          by linarith
      qed
      have hcd_right: "\<And>i t. i \<ge> ?k \<Longrightarrow> i < ?n \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) \<ge> 0"
      proof -
        fix i :: nat and t :: real assume hik: "i \<ge> ?k" and hi_lt: "i < ?n" and ht: "t \<in> I_set"
        have ht01: "t \<ge> 0 \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
        have ht_ge0: "t \<ge> 0" using ht01 by linarith
        have h1mt: "1 - t \<ge> 0" using ht01 by linarith
        \<comment> \<open>cross(v\\_k - v\\_0, v\\_i - v\\_0) \\<ge> 0: zero for i=k, positive for i > k.\<close>
        have hcki: "(vx2 ?k - vx2 0) * (vy2 i - vy2 0) - (vy2 ?k - vy2 0) * (vx2 i - vx2 0) \<ge> 0"
        proof (cases "i = ?k")
          case True thus ?thesis by simp
        next
          case False hence "i > ?k" using hik by linarith
          hence "1 \<le> ?k" by simp
          have hk_lt: "?k < ?n" by simp
          from hfan_det_0[rule_format, OF hk_lt hi_lt \<open>1 \<le> ?k\<close> \<open>i > ?k\<close>]
          show ?thesis by linarith
        qed
        \<comment> \<open>cross(v\\_k - v\\_0, v\\_{Suc i mod n} - v\\_0) \\<ge> 0.\<close>
        have hcksi: "(vx2 ?k - vx2 0) * (vy2 (Suc i mod ?n) - vy2 0)
            - (vy2 ?k - vy2 0) * (vx2 (Suc i mod ?n) - vx2 0) \<ge> 0"
        proof (cases "Suc i mod ?n = 0")
          case True \<comment> \<open>i = n-1, Suc i mod n = 0. cross(v\\_k, v\\_0) = 0.\<close>
          thus ?thesis by simp
        next
          case False
          hence hsi_ne0: "Suc i mod ?n \<noteq> 0" .
          have hsi_lt: "Suc i mod ?n < ?n" by simp
          show ?thesis
          proof (cases "Suc i mod ?n = ?k")
            case True thus ?thesis by simp
          next
            case False
            \<comment> \<open>Suc i mod n > k (since i \\<ge> k and Suc i mod n \\<noteq> k and \\<noteq> 0).
               But wait: i could be n-2, then Suc i = n-1 and Suc i mod n = n-1 > k. \\<checkmark>
               Or i = n-1, Suc i mod n = 0, handled above.\<close>
            \<comment> \<open>Since Suc i mod n \\<noteq> 0 (handled above), i < n-1 so Suc i < n.\<close>
            have hsi_lt2: "Suc i < ?n"
            proof (rule ccontr)
              assume "\<not> Suc i < ?n"
              hence "Suc i \<ge> ?n" by linarith
              hence "Suc i = ?n" using hi_lt by linarith
              hence "Suc i mod ?n = 0" by simp
              with hsi_ne0 show False by simp
            qed
            hence "Suc i < ?n" using hi_lt by linarith
            have hsi_eq: "Suc i mod ?n = Suc i" using \<open>Suc i < ?n\<close> by simp
            have "Suc i > ?k" using hik by linarith
            hence hgt: "?k < Suc i mod ?n" using hsi_eq by simp
            have "1 \<le> ?k" by simp
            have hk_lt3: "?k < ?n" by simp
            from hfan_det_0[rule_format, OF hk_lt3 hsi_lt \<open>1 \<le> ?k\<close> hgt]
            show ?thesis by linarith
          qed
        qed
        \<comment> \<open>Bilinearity: cross\\_diag = (1-t)*hcki + t*hcksi \\<ge> 0.\<close>
        have "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = (vx2 ?k - vx2 0) * ((1-t)*vy2 i + t*vy2(Suc i mod ?n) - vy2 0)
          - (vy2 ?k - vy2 0) * ((1-t)*vx2 i + t*vx2(Suc i mod ?n) - vx2 0)"
          unfolding cross_diag_def by simp
        also have "\<dots> = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
          + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))"
          by (by100 algebra)
        finally have hdecomp: "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
          + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))" .
        have "(1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) \<ge> 0"
          using mult_nonneg_nonneg[of "1-t" "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)"]
                h1mt hcki by linarith
        moreover have "t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0)) \<ge> 0"
          using mult_nonneg_nonneg[of t "(vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0)"]
                ht_ge0 hcksi by linarith
        ultimately show "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) \<ge> 0"
          using hdecomp by linarith
      qed
      \<comment> \<open>HELPER: phi\\_L at left-half boundary point gives sigma.
         For 1 \\<le> i < k: LEAST = i, cramer\\_on\\_triangle\\_edge gives (0, 1-t, t).
         For i = 0: LEAST = 1, cramer\\_on\\_triangle\\_base\\_edge gives (1-t, t, 0).
         Both give phi\\_L = sigma.\<close>
      have hphi_L_sigma: "\<And>i t. i < ?k \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          phi_L ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
        = paste_sigma vx2 vy2 ?k ?n i t"
      proof -
        fix i :: nat and t :: real assume hik: "i < ?k" and ht: "t \<in> I_set"
        \<comment> \<open>Case split: t > 0 (use left\\_fan\\_edge\\_sector) vs t = 0 (vertex case).\<close>
        show "phi_L ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = paste_sigma vx2 vy2 ?k ?n i t"
        proof (cases "t > 0")
          case True
          \<comment> \<open>t > 0: LEAST = expected from left\\_fan\\_edge\\_sector.\<close>
          have hk_lt_n_local: "?k < ?n" by simp
          note hLeast = left_fan_edge_sector[OF hn_ge3 hk_ge2 hk_lt_n_local ht True hik hfan_det_0]
          \<comment> \<open>Step 1: Unfold phi\\_L with LEAST = (if i=0 then 1 else i) substituted.\<close>
          define j where "j = (if i = 0 then (1::nat) else i)"
          have hj_eq: "(LEAST j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) - vy2 0) -
              (vy2 j - vy2 0)*(fst ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) - vy2 0) -
              (vy2(Suc j) - vy2 0)*(fst ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) - vx2 0) \<le> 0)
            = j" using hLeast unfolding j_def by simp
          \<comment> \<open>Step 2: phi\\_L unfolds to a let-expression with j substituted.\<close>
          have hphi_L_eq: "phi_L ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
            = (let ex = vx2 j - vx2 0; ey = vy2 j - vy2 0;
                   fx = vx2(Suc j) - vx2 0; fy = vy2(Suc j) - vy2 0;
                   dd = ex*fy - ey*fx;
                   dx = (1-t)*vx2 i + t*vx2(Suc i mod ?n) - vx2 0;
                   dy = (1-t)*vy2 i + t*vy2(Suc i mod ?n) - vy2 0;
                   s = (fy*dx - fx*dy)/dd; tp = (ex*dy - ey*dx)/dd in
               ((1-s-tp)*vx2 0 + s*vx2(?k+1-j) + tp*vx2(?k-j),
                (1-s-tp)*vy2 0 + s*vy2(?k+1-j) + tp*vy2(?k-j)))"
            unfolding phi_L_def Let_def using hj_eq by simp
          \<comment> \<open>Step 3: Case split i=0 vs i\\<ge>1 for Cramer evaluation.\<close>
          show ?thesis
          proof (cases "i = 0")
            case True
            \<comment> \<open>i=0, j=1. Edge from v\\_0 to v\\_1. Cramer on base edge gives s=t, tp=0.\<close>
            have hj1: "j = 1" unfolding j_def using True by simp
            \<comment> \<open>Fan det for sector 1: dd = cross(v\\_1, v\\_2) > 0.\<close>
            have hdd_ne: "(vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0) \<noteq> 0"
            proof -
              have "(1::nat) < ?n" using hn_ge3 by linarith
              have "(2::nat) < ?n" using hn_ge3 by linarith
              from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> \<open>2 < ?n\<close>]
              show ?thesis by simp
            qed
            \<comment> \<open>Cramer on base edge: s = t, tp = 0.\<close>
            from cramer_on_triangle_base_edge[of "vx2 0" "vy2 0" "vx2 1" "vy2 1" "vx2 2" "vy2 2" t]
            have hs_val: "((vy2 2 - vy2 0) * (t * (vx2 1 - vx2 0)) -
                           (vx2 2 - vx2 0) * (t * (vy2 1 - vy2 0))) /
                          ((vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0)) = t"
              and htp_val: "((vx2 1 - vx2 0) * (t * (vy2 1 - vy2 0)) -
                            (vy2 1 - vy2 0) * (t * (vx2 1 - vx2 0))) /
                           ((vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0)) = 0"
              using hdd_ne using cramer_on_triangle_base_edge(1) cramer_on_triangle_base_edge(2) by (by5000 blast)
            \<comment> \<open>Assemble: phi\\_L = ((1-t)*vx2 0 + t*vx2 k, (1-t)*vy2 0 + t*vy2 k) = sigma(0,t).\<close>
            \<comment> \<open>From hphi\\_L\\_eq with j=1 + hs\\_val (s=t) + htp\\_val (tp=0):
               phi\\_L(edge(0,t)) = ((1-t-0)*vx2 0 + t*vx2(k+1-1) + 0*vx2(k-1), ...)
               = ((1-t)*vx2 0 + t*vx2 k, (1-t)*vy2 0 + t*vy2 k) = sigma(0,t).\<close>
            \<comment> \<open>i=0: unfold phi\\_L\\_def + Let + sigma defs with LEAST + Cramer facts.
               All local define variables removed to avoid abbreviation issues.\<close>
            \<comment> \<open>Local simp rule for the Suc/numeral mismatch.\<close>
            have hSuc_len: "Suc (length u2) = ?k" by simp
            show ?thesis
              apply (simp only: phi_L_def Let_def fst_conv snd_conv hLeast Suc_1 diff_Suc_1 hSuc_len
                                paste_chain_sigma_x_def paste_chain_sigma_y_def)
              apply (insert hs_val htp_val hdd_ne)
              apply (simp add: divide_simps)
              apply (simp add: algebra_simps)
              using True numeral_2_eq_2 by (by5000 fastforce)
          next
            case False
            hence "j = i"
            proof -
              have "\<not> (i = 0)" using False .
              thus "j = i" unfolding j_def by (rule if_not_P)
            qed
            \<comment> \<open>i\\<ge>1, j=i. Edge from v\\_i to v\\_{i+1}. Cramer on edge gives s=1-t, tp=t.\<close>
            \<comment> \<open>Fan det: dd = cross(v\\_i, v\\_{i+1}) > 0 (from hfan\\_det\\_0).\<close>
            have hdd_ne2: "(vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0) \<noteq> 0"
            proof -
              have "i < ?n" using hik by simp
              have "Suc i < ?n" using hik by simp
              have "1 \<le> i" using False by linarith
              from hfan_det_0[rule_format, OF \<open>i < ?n\<close> \<open>Suc i < ?n\<close> \<open>1 \<le> i\<close>]
              show ?thesis using hik by linarith
            qed
            \<comment> \<open>Cramer on triangle edge: s = 1-t, tp = t.\<close>
            have hsi_local: "Suc i mod ?n = Suc i" using hik by simp
            from cramer_on_triangle_edge[of "vx2 0" "vy2 0" "vx2 i" "vy2 i" "vx2(Suc i)" "vy2(Suc i)" t]
            have hs2: "((vy2(Suc i) - vy2 0) * ((1-t)*(vx2 i - vx2 0) + t*(vx2(Suc i) - vx2 0)) -
                        (vx2(Suc i) - vx2 0) * ((1-t)*(vy2 i - vy2 0) + t*(vy2(Suc i) - vy2 0))) /
                       ((vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0)) = 1 - t"
              and htp2: "((vx2 i - vx2 0) * ((1-t)*(vy2 i - vy2 0) + t*(vy2(Suc i) - vy2 0)) -
                          (vy2 i - vy2 0) * ((1-t)*(vx2 i - vx2 0) + t*(vx2(Suc i) - vx2 0))) /
                         ((vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0)) = t"
              using hdd_ne2 using cramer_on_triangle_edge(1) cramer_on_triangle_edge(2) by (by5000 blast)+
            \<comment> \<open>Assemble: phi\\_L = 0*v\\_0 + (1-t)*v\\_{k+1-i} + t*v\\_{k-i} = sigma(i,t).\<close>
            \<comment> \<open>Apply phi\\_L\\_def + Let\\_def + hLeast in one simp pass, then try to close.\<close>
            have hSuc_len2: "Suc (length u2) = ?k" by simp
            show ?thesis
              apply (simp only: phi_L_def Let_def fst_conv snd_conv hLeast Suc_1 diff_Suc_1 hSuc_len2
                                paste_chain_sigma_x_def paste_chain_sigma_y_def)
              apply (insert hs2 htp2 hdd_ne2)
              apply (simp add: divide_simps)
              apply (simp add: algebra_simps)
              using False hsi_local hik by (by5000 fastforce)
          qed
        next
          case False hence "t = 0" using ht unfolding top1_unit_interval_def by (by100 auto)
          \<comment> \<open>t = 0: vertex case. phi\\_L(v\\_i) gives same sigma value regardless of sector.\<close>
          \<comment> \<open>t=0: vertex v\\_i. phi\\_L\\_def with t=0 simplifies significantly.\<close>
          show ?thesis
          proof (cases "i = 0")
            case True
            \<comment> \<open>i=0, t=0: p = v\\_0. phi\\_L(v\\_0) = v\\_0 = sigma(0,0).\<close>
            have "phi_L ((1-0)*vx2 0 + 0*vx2(Suc 0 mod ?n), (1-0)*vy2 0 + 0*vy2(Suc 0 mod ?n))
              = phi_L (vx2 0, vy2 0)" by simp
            also have "\<dots> = (vx2 0, vy2 0)"
              unfolding phi_L_def Let_def by simp
            also have "\<dots> = paste_sigma vx2 vy2 ?k ?n 0 0"
              unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by simp
            finally show ?thesis using True \<open>t = 0\<close> by simp
          next
            case False hence hi1: "i \<ge> 1" by linarith
            \<comment> \<open>1 \\<le> i < k, t=0: p = v\\_i. Direct Cramer computation.\<close>
            \<comment> \<open>For i=1: LEAST = 1. Cramer with dx=ex gives s=1, tp=0. Result = v\\_k.
               For i\\<ge>2: LEAST = i-1. Cramer with dx=fx gives s=0, tp=1. Result = v\\_{k+1-i}.\<close>
            \<comment> \<open>Direct Cramer computation at vertex v\\_i (same pattern as phi\\_L(v\\_k) = v\\_1).\<close>
            \<comment> \<open>LEAST at v\\_i: sector i-1 satisfies PL (for i\\<ge>2). For i=1: sector 1.\<close>
            \<comment> \<open>In both cases result = v\\_{k+1-i} = sigma(i,0).\<close>
            show ?thesis
            proof (cases "i = 1")
              case True
              \<comment> \<open>i=1: LEAST = 1. At v\\_1: dx = ex (sector 1). Cramer: s=1, tp=0.\<close>
              \<comment> \<open>Result: (1-1-0)*vx2 0 + 1*vx2 k + 0*vx2(k-1) = vx2 k = sigma(1,0).\<close>
              \<comment> \<open>Direct Cramer at v\\_1 with LEAST=1: dx=ex, dy=ey. s=1, tp=0. Result = v\\_k.\<close>
              have "phi_L (vx2 1, vy2 1)
                = (let ex = vx2 1 - vx2 0; ey = vy2 1 - vy2 0;
                       fx = vx2 2 - vx2 0; fy = vy2 2 - vy2 0;
                       dd = ex*fy - ey*fx;
                       dx = vx2 1 - vx2 0; dy = vy2 1 - vy2 0;
                       s = (fy*dx - fx*dy)/dd; tp = (ex*dy - ey*dx)/dd in
                   ((1-s-tp)*vx2 0 + s*vx2 ?k + tp*vx2(?k-1),
                    (1-s-tp)*vy2 0 + s*vy2 ?k + tp*vy2(?k-1)))"
              proof -
                \<comment> \<open>At i=1: the LEAST predicate holds at j=1 and 1 is minimal (j\\<ge>1).\<close>
                let ?PL1 = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
                  (vx2 j - vx2 0)*(vy2 1 - vy2 0) - (vy2 j - vy2 0)*(vx2 1 - vx2 0) \<ge> 0 \<and>
                  (vx2(Suc j) - vx2 0)*(vy2 1 - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 1 - vx2 0) \<le> 0"
                have hPL1_1: "?PL1 1"
                proof -
                  have h1: "1 \<le> (1::nat)" by simp
                  have h2: "(1::nat) < ?k" using hk_ge2 by linarith
                  have h3: "(vx2 1 - vx2 0)*(vy2 1 - vy2 0) - (vy2 1 - vy2 0)*(vx2 1 - vx2 0) \<ge> 0"
                  proof -
                    have "(vx2 1 - vx2 0)*(vy2 1 - vy2 0) - (vy2 1 - vy2 0)*(vx2 1 - vx2 0) = 0"
                      by (by100 algebra)
                    thus ?thesis by linarith
                  qed
                  have h4: "(vx2(Suc 1) - vx2 0)*(vy2 1 - vy2 0) - (vy2(Suc 1) - vy2 0)*(vx2 1 - vx2 0) \<le> 0"
                  proof -
                    have "(1::nat) < ?n" using hn_ge3 by linarith
                    have "(2::nat) < ?n" using hn_ge3 by linarith
                    from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> \<open>2 < ?n\<close>]
                    have hfd: "(vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0) > 0" by simp
                    have "(vx2 2 - vx2 0)*(vy2 1 - vy2 0) - (vy2 2 - vy2 0)*(vx2 1 - vx2 0)
                      = -((vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0))" by (by100 algebra)
                    hence "(vx2 2 - vx2 0)*(vy2 1 - vy2 0) - (vy2 2 - vy2 0)*(vx2 1 - vx2 0) \<le> 0"
                      using hfd by linarith
                    moreover have "(2::nat) = Suc 1" by simp
                    ultimately show ?thesis by metis
                  qed
                  from h1 h2 h3 h4 show ?thesis by simp
                qed
                have hLeast1: "(LEAST j. ?PL1 j) = 1"
                  using Least_equality[of ?PL1 1] hPL1_1 by (by100 blast)
                have hSuc1: "Suc 1 = (2::nat)" by simp
                have hk1: "?k + 1 - 1 = ?k" using hk_ge2 by linarith
                have hSuc0: "(1::nat) = Suc 0" by simp
                have hSucSuc0: "(2::nat) = Suc (Suc 0)" by simp
                show ?thesis unfolding phi_L_def Let_def
                  using hLeast1 hSuc1 hk1
                  by (simp add: numeral_2_eq_2)
              qed
              also have "\<dots> = (vx2 ?k, vy2 ?k)"
              proof -
                \<comment> \<open>dx = ex: s = (fy*ex-fx*ey)/dd = dd/dd = 1. tp = (ex*ey-ey*ex)/dd = 0.\<close>
                have hdd1: "(vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0) \<noteq> 0"
                proof -
                  have "(1::nat) < ?n" using hn_ge3 by linarith
                  have "(2::nat) < ?n" using hn_ge3 by linarith
                  from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> \<open>2 < ?n\<close>]
                  show ?thesis by simp
                qed
                have "((vy2 2 - vy2 0)*(vx2 1 - vx2 0) - (vx2 2 - vx2 0)*(vy2 1 - vy2 0)) =
                  ((vx2 1 - vx2 0)*(vy2 2 - vy2 0) - (vy2 1 - vy2 0)*(vx2 2 - vx2 0))"
                  by (by100 algebra)
                moreover have "((vx2 1 - vx2 0)*(vy2 1 - vy2 0) - (vy2 1 - vy2 0)*(vx2 1 - vx2 0)) = 0"
                  by (by100 algebra)
                ultimately show ?thesis unfolding Let_def using hdd1
                  by (simp add: divide_simps)
              qed
              finally have "phi_L (vx2 1, vy2 1) = (vx2 ?k, vy2 ?k)" .
              moreover have "paste_sigma vx2 vy2 ?k ?n 1 0 = (vx2 ?k, vy2 ?k)"
              proof -
                have "u2 \<noteq> []" using hk_ge2 by (cases u2) simp+
                thus ?thesis
                  unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def using hk_ge2 by simp
              qed
              moreover have "Suc 1 mod ?n = 2"
              proof -
                have h2n: "(2::nat) < ?n" using hn_ge3 by linarith
                have hS1: "Suc 1 = (2::nat)" by simp
                hence "Suc 1 mod ?n = 2 mod ?n" by (simp only: hS1)
                also have "2 mod ?n = (2::nat)" using h2n by (rule mod_less)
                finally show ?thesis .
              qed
              ultimately show ?thesis using True \<open>t = 0\<close> by simp
            next
              case False hence hi2: "i \<ge> 2" using hi1 by linarith
              \<comment> \<open>i\\<ge>2: LEAST = i-1. Direct Cramer at v\\_i with j=i-1.\<close>
              \<comment> \<open>Need LEAST evaluation: PL(i-1) holds and minimality from fan det.\<close>
              let ?PL_vi = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
                  (vx2 j - vx2 0)*(vy2 i - vy2 0) - (vy2 j - vy2 0)*(vx2 i - vx2 0) \<ge> 0 \<and>
                  (vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
              have hPL_im1: "?PL_vi (i - 1)"
              proof -
                have "1 \<le> i - 1" using hi2 by linarith
                moreover have "i - 1 < ?k" using hik by linarith
                moreover have "(vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0) \<ge> 0"
                proof -
                  have "i - 1 < ?n" using hik by simp
                  have "i < ?n" using hik by simp
                  have "1 \<le> i - 1" using hi2 by linarith
                  from hfan_det_0[rule_format, OF \<open>i - 1 < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> i - 1\<close>]
                  show ?thesis using hi2 by linarith
                qed
                moreover have "Suc (i - 1) = i" using hi2 by linarith
                hence "(vx2(Suc(i-1)) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc(i-1)) - vy2 0)*(vx2 i - vx2 0) = 0"
                  by simp
                hence "(vx2(Suc(i-1)) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc(i-1)) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
                  by linarith
                ultimately show ?thesis by (by100 auto)
              qed
              have hPL_min_vi: "\<And>j. ?PL_vi j \<Longrightarrow> i - 1 \<le> j"
              proof -
                fix j assume hj: "?PL_vi j"
                hence hj1: "1 \<le> j" and hjk: "j < ?k" and
                  hupper: "(vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
                  by simp+
                show "i - 1 \<le> j"
                proof (rule ccontr)
                  assume "\<not> i - 1 \<le> j" hence "j < i - 1" by linarith
                  hence "Suc j < i" by linarith
                  hence "Suc j < ?n" using hik by simp
                  have "i < ?n" using hik by simp
                  have "1 \<le> Suc j" using hj1 by linarith
                  from hfan_det_0[rule_format, OF \<open>Suc j < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < i\<close>]
                  have "(vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) > 0" .
                  with hupper show False by linarith
                qed
              qed
              have hLeast_vi: "(LEAST j. ?PL_vi j) = i - 1"
                using Least_equality[of ?PL_vi "i - 1"] hPL_im1 hPL_min_vi by (by100 blast)
              \<comment> \<open>Unfold phi\\_L with LEAST = i-1, then direct Cramer.\<close>
              have hSuc_im1: "Suc (i - 1) = i" using hi2 by linarith
              \<comment> \<open>Cramer at v\\_i with j=i-1: dx=fx, dy=fy. s=0, tp=1.\<close>
              have "phi_L (vx2 i, vy2 i)
                = (let ex = vx2(i-1) - vx2 0; ey = vy2(i-1) - vy2 0;
                       fx = vx2 i - vx2 0; fy = vy2 i - vy2 0;
                       dd = ex*fy - ey*fx;
                       dx = vx2 i - vx2 0; dy = vy2 i - vy2 0;
                       s = (fy*dx - fx*dy)/dd; tp = (ex*dy - ey*dx)/dd in
                   ((1-s-tp)*vx2 0 + s*vx2(?k+1-(i-1)) + tp*vx2(?k-(i-1)),
                    (1-s-tp)*vy2 0 + s*vy2(?k+1-(i-1)) + tp*vy2(?k-(i-1))))"
                unfolding phi_L_def Let_def using hLeast_vi hSuc_im1 by simp
              \<comment> \<open>dx = fx and dy = fy. So s = (fy*fx - fx*fy)/dd = 0 and tp = (ex*fy - ey*fx)/dd = dd/dd = 1.\<close>
              also have "\<dots> = (vx2(?k-(i-1)), vy2(?k-(i-1)))"
              proof -
                have "((vy2 i - vy2 0)*(vx2 i - vx2 0) - (vx2 i - vx2 0)*(vy2 i - vy2 0)) = 0"
                  by (by100 algebra)
                moreover have hdd_vi: "(vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0) \<noteq> 0"
                proof -
                  have "i - 1 < ?n" using hik by simp
                  have "i < ?n" using hik by simp
                  have "1 \<le> i - 1" using hi2 by linarith
                  from hfan_det_0[rule_format, OF \<open>i - 1 < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> i - 1\<close>]
                  show ?thesis using hi2 by linarith
                qed
                ultimately show ?thesis unfolding Let_def using hdd_vi by simp
              qed
              also have "\<dots> = (vx2(?k+1-i), vy2(?k+1-i))" using hi2 by simp
              finally have hphi_L_vi: "phi_L (vx2 i, vy2 i) = (vx2(?k+1-i), vy2(?k+1-i))" .
              \<comment> \<open>sigma(i,0) = (vx2(k+1-i), vy2(k+1-i)) for 1 \\<le> i \\<le> k-1.\<close>
              have "paste_sigma vx2 vy2 ?k ?n i 0 = (vx2(?k+1-i), vy2(?k+1-i))"
                unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def using hi1 hik by (by100 simp)
              with hphi_L_vi have "phi_L (vx2 i, vy2 i) = paste_sigma vx2 vy2 ?k ?n i 0" by simp
              moreover have "Suc i mod ?n = Suc i" using hik by simp
              ultimately show ?thesis using \<open>t = 0\<close> by simp
            qed
          qed
        qed
      qed
      \<comment> \<open>HELPER: phi\\_R at right-half boundary point gives sigma.
         For k \\<le> i < n-1: LEAST = i, cramer\\_on\\_triangle\\_edge.
         For i = n-1: LEAST = n-2, cramer\\_on\\_triangle\\_base\\_edge.
         Both give phi\\_R = sigma.\<close>
      have hphi_R_sigma: "\<And>i t. ?k \<le> i \<Longrightarrow> i < ?n \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          phi_R ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
        = paste_sigma vx2 vy2 ?k ?n i t"
      proof -
        fix i :: nat and t :: real assume hik: "?k \<le> i" and hi_lt: "i < ?n" and ht: "t \<in> I_set"
        \<comment> \<open>Right half: symmetric to left half. LEAST in right fan gives expected sector.
           For k \\<le> i < n-1: LEAST = i. For i = n-1: LEAST = n-2.
           Cramer + four-stage simp as for left half.\<close>
        show "phi_R ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
          = paste_sigma vx2 vy2 ?k ?n i t"
        proof (cases "t > 0")
          case True
          \<comment> \<open>t > 0: symmetric to hphi\\_L\\_sigma left half.
             Case k \\<le> i < n-1: LEAST = i, cramer\\_on\\_triangle\\_edge with (v\\_0, v\\_i, v\\_{i+1}).
             Case i = n-1: LEAST = n-2, cramer\\_on\\_triangle\\_base\\_edge with (v\\_0, v\\_{n-2}, v\\_{n-1}).\<close>
          have hk_lt_n_local: "?k < ?n" by simp
          have hSuc_len_R: "Suc (length u2) = ?k" by simp
          show ?thesis
          proof (cases "i < ?n - 1")
            case hilt: True
            \<comment> \<open>k \\<le> i < n-1: cramer\\_on\\_triangle\\_edge with (v\\_0, v\\_i, v\\_{i+1}).\<close>
            have hk_lt_nm1_local: "?k < ?n - 1" using hilt hik by linarith
            note hRLeast = right_fan_edge_sector[OF hn_ge3 hk_ge2 hk_lt_n_local hk_lt_nm1_local ht True hik hi_lt hfan_det_0 hilt]
            have hsi_lt: "Suc i < ?n" using hilt by linarith
            have hdd_R: "(vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0) \<noteq> 0"
            proof -
              have "1 \<le> i" using hik hk_ge2 by linarith
              from hfan_det_0[rule_format, OF hi_lt hsi_lt \<open>1 \<le> i\<close>]
              show ?thesis using hilt by linarith
            qed
            from cramer_on_triangle_edge[of "vx2 0" "vy2 0" "vx2 i" "vy2 i" "vx2(Suc i)" "vy2(Suc i)" t]
            have hsR: "((vy2(Suc i) - vy2 0) * ((1-t)*(vx2 i - vx2 0) + t*(vx2(Suc i) - vx2 0)) -
                        (vx2(Suc i) - vx2 0) * ((1-t)*(vy2 i - vy2 0) + t*(vy2(Suc i) - vy2 0))) /
                       ((vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0)) = 1 - t"
              and htpR: "((vx2 i - vx2 0) * ((1-t)*(vy2 i - vy2 0) + t*(vy2(Suc i) - vy2 0)) -
                          (vy2 i - vy2 0) * ((1-t)*(vx2 i - vx2 0) + t*(vx2(Suc i) - vx2 0))) /
                         ((vx2 i - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 i - vy2 0)*(vx2(Suc i) - vx2 0)) = t"
              using hdd_R using cramer_on_triangle_edge(1) cramer_on_triangle_edge(2) by (by5000 blast)+
            \<comment> \<open>Four-stage simp.\<close>
            show ?thesis
              apply (simp only: phi_R_def Let_def fst_conv snd_conv hRLeast Suc_1 diff_Suc_1 hSuc_len_R
                                paste_chain_sigma_x_def paste_chain_sigma_y_def)
              apply (insert hsR htpR hdd_R)
              apply (simp add: divide_simps)
              apply (simp add: algebra_simps)
              using hilt hik by (by5000 fastforce)
          next
            case hige: False
            hence "i = ?n - 1" using hi_lt by linarith
            \<comment> \<open>i = n-1: LEAST = n-2, cramer\\_on\\_triangle\\_base\\_edge.\<close>
            \<comment> \<open>i=n-1: LEAST=n-2. Point on edge from v\\_{n-1} to v\\_0 in triangle (v\\_0, v\\_{n-2}, v\\_{n-1}).
               Cramer gives s=0, t\\_par=1-t. Result: t*vx2 k + (1-t)*vx2 0 = sigma(n-1,t).\<close>
            \<comment> \<open>Use same four-stage simp approach.\<close>
            \<comment> \<open>Sub-case split: t < 1 (LEAST = n-2) vs t = 1 (vertex v\\_0).\<close>
            show ?thesis
            proof (cases "t = 1")
              case True
              \<comment> \<open>t=1: point is v\\_0. phi\\_R(v\\_0) = (vx2 k, vy2 k). sigma(n-1,1) = vx2 k.\<close>
              have "Suc (?n - 1) mod ?n = 0" using hn_ge3 by simp
              hence hp: "(1 - t) * vx2 (?n - 1) + t * vx2 (Suc (?n - 1) mod ?n) = vx2 0 \<and>
                         (1 - t) * vy2 (?n - 1) + t * vy2 (Suc (?n - 1) mod ?n) = vy2 0"
                using True by simp
              have "phi_R (vx2 0, vy2 0) = (vx2 ?k, vy2 ?k)"
                unfolding phi_R_def Let_def by simp
              moreover have "paste_sigma vx2 vy2 ?k ?n (?n - 1) 1 = (vx2 ?k, vy2 ?k)"
                unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def using hn_ge3 by simp
              ultimately show ?thesis using True hp \<open>i = ?n - 1\<close> by simp
            next
              case htn1: False
              hence "t < 1" using ht unfolding top1_unit_interval_def by (by100 auto)
              hence h1mt_pos: "1 - t > 0" by linarith
              \<comment> \<open>v \\<noteq> []: k < n-1, so LEAST = n-2 in right fan.\<close>
              have hk_lt_nm1: "?k < ?n - 1" using hk_lt_nm1 by simp
              have hnm2_ge_k: "?n - 2 \<ge> ?k" using hk_lt_nm1 by linarith
              have hnm2_lt: "?n - 2 < ?n - 1" using hn_ge3 by linarith
              \<comment> \<open>PR predicate at j = n-2:\<close>
              let ?PR_base = "\<lambda>j. ?k \<le> j \<and> j < ?n - 1 \<and>
                (vx2 j - vx2 0)*(snd ((1-t)*vx2(?n-1) + t*vx2(Suc(?n-1) mod ?n),
                                      (1-t)*vy2(?n-1) + t*vy2(Suc(?n-1) mod ?n)) - vy2 0)
                - (vy2 j - vy2 0)*(fst ((1-t)*vx2(?n-1) + t*vx2(Suc(?n-1) mod ?n),
                                        (1-t)*vy2(?n-1) + t*vy2(Suc(?n-1) mod ?n)) - vx2 0) \<ge> 0 \<and>
                (vx2(Suc j) - vx2 0)*(snd ((1-t)*vx2(?n-1) + t*vx2(Suc(?n-1) mod ?n),
                                            (1-t)*vy2(?n-1) + t*vy2(Suc(?n-1) mod ?n)) - vy2 0)
                - (vy2(Suc j) - vy2 0)*(fst ((1-t)*vx2(?n-1) + t*vx2(Suc(?n-1) mod ?n),
                                              (1-t)*vy2(?n-1) + t*vy2(Suc(?n-1) mod ?n)) - vx2 0) \<le> 0"
              \<comment> \<open>Simplify: Suc(n-1) mod n = 0, so fst p = (1-t)*vx2(n-1) + t*vx2 0,
                 fst p - vx2 0 = (1-t)*(vx2(n-1) - vx2 0). Similarly for snd.\<close>
              have hmod_nm1: "Suc (?n - 1) mod ?n = 0" using hn_ge3 by simp
              \<comment> \<open>The cross products simplify: cross(v\\_j, p) = (1-t)*cross(v\\_j, v\\_{n-1}).\<close>
              have hcross_j: "\<And>j. (vx2 j - vx2 0) * ((1-t)*(vy2(?n-1) - vy2 0))
                - (vy2 j - vy2 0) * ((1-t)*(vx2(?n-1) - vx2 0))
                = (1-t) * ((vx2 j - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2 j - vy2 0)*(vx2(?n-1) - vx2 0))"
                by (by100 algebra)
              \<comment> \<open>PR(n-2): lower cross \\<ge> 0, upper cross = 0.\<close>
              have hPR_nm2: "?k \<le> ?n - 2 \<and> ?n - 2 < ?n - 1 \<and>
                (1-t)*((vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0)) \<ge> 0 \<and>
                (1-t)*((vx2(Suc(?n-2)) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc(?n-2)) - vy2 0)*(vx2(?n-1) - vx2 0)) \<le> 0"
              proof -
                have "?n - 2 < ?n" using hn_ge3 by linarith
                have "?n - 1 < ?n" using hn_ge3 by linarith
                have "1 \<le> ?n - 2" using hn_ge3 by linarith
                have "?n - 2 < ?n - 1" using hn_ge3 by linarith
                from hfan_det_0[rule_format, OF \<open>?n - 2 < ?n\<close> \<open>?n - 1 < ?n\<close> \<open>1 \<le> ?n - 2\<close> \<open>?n - 2 < ?n - 1\<close>]
                have hfd: "(vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0) > 0" .
                hence hlower: "(1-t)*((vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0)) \<ge> 0"
                  using h1mt_pos by (by100 simp)
                have hSuc_nm2: "Suc (?n - 2) = ?n - 1" using hn_ge3 by linarith
                have "(vx2(?n-1) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-1) - vy2 0)*(vx2(?n-1) - vx2 0) = 0"
                  by (by100 algebra)
                hence hupper: "(1-t)*((vx2(Suc(?n-2)) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc(?n-2)) - vy2 0)*(vx2(?n-1) - vx2 0)) \<le> 0"
                  using hSuc_nm2 by simp
                from hnm2_ge_k hnm2_lt hlower hupper show ?thesis by (by100 blast)
              qed
              \<comment> \<open>Minimality: for k \\<le> j < n-2, upper cross > 0 (contradicts \\<le> 0).\<close>
              have hPR_min: "\<And>j. ?k \<le> j \<Longrightarrow> j < ?n - 1 \<Longrightarrow>
                (1-t)*((vx2(Suc j) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2(?n-1) - vx2 0)) \<le> 0 \<Longrightarrow>
                ?n - 2 \<le> j"
              proof -
                fix j assume hjk: "?k \<le> j" and hjn: "j < ?n - 1"
                  and hupper: "(1-t)*((vx2(Suc j) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2(?n-1) - vx2 0)) \<le> 0"
                show "?n - 2 \<le> j"
                proof (rule ccontr)
                  assume "\<not> ?n - 2 \<le> j" hence "j < ?n - 2" by linarith
                  hence "Suc j \<le> ?n - 2" by linarith
                  hence "Suc j < ?n - 1" by linarith
                  have "Suc j < ?n" using hn_ge3 \<open>Suc j < ?n - 1\<close> by simp
                  have "?n - 1 < ?n" using hn_ge3 by linarith
                  have "1 \<le> Suc j" using hjk hk_ge2 by linarith
                  from hfan_det_0[rule_format, OF \<open>Suc j < ?n\<close> \<open>?n - 1 < ?n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < ?n - 1\<close>]
                  have "(vx2(Suc j) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2(?n-1) - vx2 0) > 0" .
                  hence "(1-t)*((vx2(Suc j) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2(?n-1) - vx2 0)) > 0"
                    using h1mt_pos by (by100 simp)
                  with hupper show False by linarith
                qed
              qed
              \<comment> \<open>Connect PR facts to the LEAST in phi\\_R\\_def.\<close>
              \<comment> \<open>The LEAST operates on the full predicate with fst/snd of the pair.\<close>
              have hLeast_nm2: "(LEAST j. ?k \<le> j \<and> j < ?n - 1 \<and>
                (vx2 j - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2 j - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<ge> 0 \<and>
                (vx2(Suc j) - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2(Suc j) - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<le> 0)
                = ?n - 2"
              proof (rule Least_equality)
                \<comment> \<open>Predicate holds at n-2.\<close>
                have hsimp_x: "(1-t)*vx2(?n-1) + t*vx2 0 - vx2 0 = (1-t)*(vx2(?n-1) - vx2 0)" by (by100 algebra)
                have hsimp_y: "(1-t)*vy2(?n-1) + t*vy2 0 - vy2 0 = (1-t)*(vy2(?n-1) - vy2 0)" by (by100 algebra)
                have hlower_eq: "(vx2(?n-2) - vx2 0)*((1-t)*(vy2(?n-1) - vy2 0)) - (vy2(?n-2) - vy2 0)*((1-t)*(vx2(?n-1) - vx2 0))
                  = (1-t)*((vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0))"
                  by (by100 algebra)
                have hupper_eq: "(vx2(Suc(?n-2)) - vx2 0)*((1-t)*(vy2(?n-1) - vy2 0)) - (vy2(Suc(?n-2)) - vy2 0)*((1-t)*(vx2(?n-1) - vx2 0))
                  = (1-t)*((vx2(Suc(?n-2)) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc(?n-2)) - vy2 0)*(vx2(?n-1) - vx2 0))"
                  by (by100 algebra)
                from hPR_nm2 show "?k \<le> ?n - 2 \<and> ?n - 2 < ?n - 1 \<and>
                  (vx2(?n-2) - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2(?n-2) - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<ge> 0 \<and>
                  (vx2(Suc(?n-2)) - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2(Suc(?n-2)) - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<le> 0"
                  using hsimp_x hsimp_y hlower_eq hupper_eq by simp
              next
                \<comment> \<open>Minimality.\<close>
                fix j assume hj: "?k \<le> j \<and> j < ?n - 1 \<and>
                  (vx2 j - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2 j - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<ge> 0 \<and>
                  (vx2(Suc j) - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2(Suc j) - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<le> 0"
                have hsimp_x: "(1-t)*vx2(?n-1) + t*vx2 0 - vx2 0 = (1-t)*(vx2(?n-1) - vx2 0)" by (by100 algebra)
                have hsimp_y: "(1-t)*vy2(?n-1) + t*vy2 0 - vy2 0 = (1-t)*(vy2(?n-1) - vy2 0)" by (by100 algebra)
                from hj have hjk: "?k \<le> j" and hjn: "j < ?n - 1" by simp+
                from hj have "(vx2(Suc j) - vx2 0)*((1-t)*vy2(?n-1) + t*vy2 0 - vy2 0) - (vy2(Suc j) - vy2 0)*((1-t)*vx2(?n-1) + t*vx2 0 - vx2 0) \<le> 0"
                  by simp
                hence "(1-t)*((vx2(Suc j) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2(?n-1) - vx2 0)) \<le> 0"
                  using hsimp_x hsimp_y by (simp add: algebra_simps)
                from hPR_min[OF hjk hjn this] show "?n - 2 \<le> j" .
              qed
              \<comment> \<open>Cramer: s = 0, tp = 1-t. phi\\_R result = t*vx2 k + (1-t)*vx2 0 = sigma(n-1,t).\<close>
              have hSuc_nm2: "Suc (?n - 2) = ?n - 1" using hn_ge3 by linarith
              have hSuc_nm1_mod: "Suc (?n - 1) mod ?n = 0" using hn_ge3 by simp
              have hdd_base: "(vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0) \<noteq> 0"
              proof -
                have "?n - 2 < ?n" using hn_ge3 by linarith
                have "?n - 1 < ?n" using hn_ge3 by linarith
                have "1 \<le> ?n - 2" using hn_ge3 by linarith
                from hfan_det_0[rule_format, OF \<open>?n - 2 < ?n\<close> \<open>?n - 1 < ?n\<close> \<open>1 \<le> ?n - 2\<close>]
                show ?thesis using hn_ge3 by linarith
              qed
              \<comment> \<open>s numerator = (fy*dx - fx*dy) = (1-t)*(fy*fx - fx*fy) = 0.\<close>
              have hs_num: "((vy2(?n-1) - vy2 0)*((1-t)*(vx2(?n-1) - vx2 0)) - (vx2(?n-1) - vx2 0)*((1-t)*(vy2(?n-1) - vy2 0))) = 0"
                by (by100 algebra)
              \<comment> \<open>tp numerator = (ex*dy - ey*dx) = (1-t)*(ex*fy - ey*fx) = (1-t)*dd.\<close>
              have htp_num: "((vx2(?n-2) - vx2 0)*((1-t)*(vy2(?n-1) - vy2 0)) - (vy2(?n-2) - vy2 0)*((1-t)*(vx2(?n-1) - vx2 0)))
                = (1-t)*((vx2(?n-2) - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2(?n-2) - vy2 0)*(vx2(?n-1) - vx2 0))"
                by (by100 algebra)
              \<comment> \<open>Four-stage simp for the final equality.\<close>
              show ?thesis
                apply (simp only: \<open>i = ?n - 1\<close> phi_R_def Let_def fst_conv snd_conv
                       hLeast_nm2 hSuc_nm2 hSuc_nm1_mod hmod_nm1 hSuc_len_R
                       paste_chain_sigma_x_def paste_chain_sigma_y_def)
                apply (insert hs_num htp_num hdd_base)
                apply (simp add: divide_simps)
                by (simp add: algebra_simps)
            qed
          qed
        next
          case False hence "t = 0" using ht unfolding top1_unit_interval_def by (by100 auto)
          \<comment> \<open>t=0: p = v\\_i. Direct Cramer computation.
             For i=k: LEAST = k, dx=ex, s=1, tp=0, result = v\\_{k+1}.
             For i>k: LEAST = i-1, dx=fx, s=0, tp=1, result = v\\_{Suc i mod n}.\<close>
          show ?thesis
          proof (cases "i = ?k")
            case True
            \<comment> \<open>i=k: LEAST = k. At v\\_k: dx=ex (sector k). s=1, tp=0.\<close>
            have hk_lt_nm1: "?k < ?n - 1" using hk_lt_nm1 by simp
            let ?PR_vk = "\<lambda>j. ?k \<le> j \<and> j < ?n - 1 \<and>
              (vx2 j - vx2 0)*(vy2 ?k - vy2 0) - (vy2 j - vy2 0)*(vx2 ?k - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0) \<le> 0"
            have hPR_k: "?PR_vk ?k"
            proof -
              have h1: "?k \<le> ?k" by simp
              have h2: "?k < ?n - 1" using hk_lt_nm1 .
              have h3: "(vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) = 0"
                by (by100 algebra)
              hence h3': "(vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) \<ge> 0" by linarith
              have "Suc ?k < ?n" using hk_lt_nm1 by linarith
              have "?k < ?n" by simp
              have "1 \<le> ?k" using hk_ge2 by linarith
              from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> \<open>Suc ?k < ?n\<close> \<open>1 \<le> ?k\<close>]
              have hfd: "(vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0) > 0"
                using hk_lt_nm1 by simp
              have "(vx2(Suc ?k) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc ?k) - vy2 0)*(vx2 ?k - vx2 0)
                = -((vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0))"
                by (by100 algebra)
              hence h4: "(vx2(Suc ?k) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc ?k) - vy2 0)*(vx2 ?k - vx2 0) \<le> 0"
                using hfd by linarith
              from h1 h2 h3' h4 show ?thesis by (by100 blast)
            qed
            have hLeast_k: "(LEAST j. ?PR_vk j) = ?k"
            proof (rule Least_equality)
              show "?PR_vk ?k" using hPR_k .
            next
              fix j assume "?PR_vk j" thus "?k \<le> j" by simp
            qed
            \<comment> \<open>Cramer: dx = ex, dy = ey. s = dd/dd = 1, tp = 0.\<close>
            have hdd_k: "(vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0) \<noteq> 0"
            proof -
              have "Suc ?k < ?n" using hk_lt_nm1 by linarith
              have "?k < ?n" by simp
              have "1 \<le> ?k" using hk_ge2 by linarith
              from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> \<open>Suc ?k < ?n\<close> \<open>1 \<le> ?k\<close>]
              show ?thesis using hk_lt_nm1 by linarith
            qed
            have hs_k: "((vy2(Suc ?k) - vy2 0)*(vx2 ?k - vx2 0) - (vx2(Suc ?k) - vx2 0)*(vy2 ?k - vy2 0))
              = ((vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0))"
              by (by100 algebra)
            have htp_k: "((vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0)) = 0"
              by (by100 algebra)
            \<comment> \<open>phi\\_R(v\\_k) with LEAST = k: four-stage simp.\<close>
            have "phi_R (vx2 ?k, vy2 ?k) = (vx2(Suc ?k), vy2(Suc ?k))"
              unfolding phi_R_def Let_def
              using hLeast_k hs_k htp_k hdd_k
              by (simp add: divide_simps)
            moreover have "paste_sigma vx2 vy2 ?k ?n ?k 0 = (vx2(Suc ?k), vy2(Suc ?k))"
            proof -
              have "?k \<noteq> 0" using hk_ge2 by linarith
              have "?k \<noteq> ?n - 1" using hk_lt_nm1 by linarith
              have "\<not> (?k \<le> ?k - 1)" using hk_ge2 by linarith
              thus ?thesis
                unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def
                using \<open>?k \<noteq> 0\<close> \<open>?k \<noteq> ?n - 1\<close> by simp
            qed
            moreover have "Suc ?k mod ?n = Suc ?k" using hk_lt_nm1 by simp
            ultimately show ?thesis using True \<open>t = 0\<close> by simp
          next
            case hink: False
            hence hi_gt_k: "i > ?k" using hik by linarith
            \<comment> \<open>i > k: LEAST = i-1. Cramer at v\\_i with sector i-1.\<close>
            have hi_ge_k1: "i \<ge> ?k + 1" using hi_gt_k by linarith
            have him1_ge_k: "i - 1 \<ge> ?k" using hi_gt_k by linarith
            have him1_lt: "i - 1 < ?n - 1" using hi_lt hn_ge3 by simp
            let ?PR_vi = "\<lambda>j. ?k \<le> j \<and> j < ?n - 1 \<and>
              (vx2 j - vx2 0)*(vy2 i - vy2 0) - (vy2 j - vy2 0)*(vx2 i - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
            have hPR_im1: "?PR_vi (i - 1)"
            proof -
              have h1: "?k \<le> i - 1" using him1_ge_k .
              have h2: "i - 1 < ?n - 1" using him1_lt .
              have h3: "(vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0) \<ge> 0"
              proof -
                have "i - 1 < ?n" using hi_lt by simp
                have "i < ?n" using hi_lt .
                have "1 \<le> i - 1" using hi_gt_k hk_ge2 by linarith
                from hfan_det_0[rule_format, OF \<open>i - 1 < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> i - 1\<close>]
                show ?thesis using hi_gt_k by linarith
              qed
              have hSuc_im1: "Suc (i - 1) = i" using hi_gt_k by linarith
              have "(vx2 i - vx2 0)*(vy2 i - vy2 0) - (vy2 i - vy2 0)*(vx2 i - vx2 0) = 0"
                by (by100 algebra)
              hence h4: "(vx2(Suc(i-1)) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc(i-1)) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
                using hSuc_im1 by simp
              from h1 h2 h3 h4 show ?thesis by (by100 blast)
            qed
            have hPR_min: "\<And>j. ?PR_vi j \<Longrightarrow> i - 1 \<le> j"
            proof -
              fix j assume hj: "?PR_vi j"
              hence hjk: "?k \<le> j" and hjn: "j < ?n - 1" and
                hupper: "(vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) \<le> 0"
                by simp+
              show "i - 1 \<le> j"
              proof (rule ccontr)
                assume "\<not> i - 1 \<le> j" hence "j < i - 1" by linarith
                hence "Suc j < i" by linarith
                hence "Suc j < ?n" using hi_lt by simp
                have "i < ?n" using hi_lt .
                have "1 \<le> Suc j" using hjk hk_ge2 by linarith
                from hfan_det_0[rule_format, OF \<open>Suc j < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < i\<close>]
                have "(vx2(Suc j) - vx2 0)*(vy2 i - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 i - vx2 0) > 0" .
                with hupper show False by linarith
              qed
            qed
            have hLeast_im1: "(LEAST j. ?PR_vi j) = i - 1"
              using Least_equality[of ?PR_vi "i - 1"] hPR_im1 hPR_min by (by100 blast)
            \<comment> \<open>Cramer: dx = fx (since Suc(i-1) = i). s = 0, tp = 1.\<close>
            have hSuc_im1: "Suc (i - 1) = i" using hi_gt_k by linarith
            have hdd_vi: "(vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0) \<noteq> 0"
            proof -
              have "i - 1 < ?n" using hi_lt by simp
              have "i < ?n" using hi_lt .
              have "1 \<le> i - 1" using hi_gt_k hk_ge2 by linarith
              from hfan_det_0[rule_format, OF \<open>i - 1 < ?n\<close> \<open>i < ?n\<close> \<open>1 \<le> i - 1\<close>]
              show ?thesis using hi_gt_k by linarith
            qed
            have hs_vi: "((vy2 i - vy2 0)*(vx2 i - vx2 0) - (vx2 i - vx2 0)*(vy2 i - vy2 0)) = 0"
              by (by100 algebra)
            have htp_vi: "((vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0))
              = ((vx2(i-1) - vx2 0)*(vy2 i - vy2 0) - (vy2(i-1) - vy2 0)*(vx2 i - vx2 0))"
              by simp
            \<comment> \<open>phi\\_R(v\\_i) = v\\_{Suc i mod n} via four-stage simp.\<close>
            have "phi_R (vx2 i, vy2 i) = (vx2(Suc i mod ?n), vy2(Suc i mod ?n))"
              unfolding phi_R_def Let_def
              using hLeast_im1 hSuc_im1 hs_vi hdd_vi
              by (simp add: divide_simps)
            moreover have "paste_sigma vx2 vy2 ?k ?n i 0 = (vx2(Suc i mod ?n), vy2(Suc i mod ?n))"
            proof (cases "i = ?n - 1")
              case True
              hence "Suc i mod ?n = 0" using hn_ge3 by simp
              thus ?thesis using True
                unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by simp
            next
              case False
              hence "i \<noteq> 0" using hi_gt_k hk_ge2 by linarith
              have "\<not> (i \<le> ?k - 1)" using hi_gt_k by linarith
              have "Suc i mod ?n = Suc i" using False hi_lt by simp
              thus ?thesis using False \<open>i \<noteq> 0\<close> \<open>\<not> (i \<le> ?k - 1)\<close>
                unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by simp
            qed
            moreover have "Suc i mod ?n = Suc i mod ?n" by simp
            ultimately show ?thesis using \<open>t = 0\<close> by simp
          qed
        qed
      qed
      \<comment> \<open>HELPER: junction continuity. At diagonal points (cross\\_diag = 0),
         q2(phi\\_L) = q2(phi\\_R) via C7 for the a-pair.\<close>
      \<comment> \<open>VERTEX HELPER: phi\\_L at v\\_0 = v\\_0. At origin, dx=dy=0 so s=tp=0 and result = v\\_0.\<close>
      have hphi_L_v0: "phi_L (vx2 0, vy2 0) = (vx2 0, vy2 0)"
        unfolding phi_L_def Let_def by simp
      \<comment> \<open>VERTEX HELPER: phi\\_L at v\\_k. Needs LEAST evaluation at vertex v\\_k.\<close>
      \<comment> \<open>phi\\_R at v\\_0 also gives v\\_0 (same argument: dx=dy=0).\<close>
      \<comment> \<open>phi\\_R at v\\_0: dx=dy=0, so s=tp=0. Result: (1-0-0)*vx2 k + 0 + 0 = (vx2 k, vy2 k).\<close>
      have hphi_R_v0: "phi_R (vx2 0, vy2 0) = (vx2 ?k, vy2 ?k)"
        unfolding phi_R_def Let_def by simp
      \<comment> \<open>VERTEX HELPER: q2(phi\\_L(v\\_k)). phi\\_L at v\\_k: dx = vx2 k - vx2 0, dy = vy2 k - vy2 0.
         LEAST gives sector k-1 (last left sector). Cramer: s=0, tp=1.
         Result: 0*vx2 0 + 0*vx2 2 + 1*vx2 1 = vx2 1.\<close>
      \<comment> \<open>Try to evaluate phi\\_L(v\\_k) directly via four-stage simp.\<close>
      have hphi_L_vk_val: "phi_L (vx2 ?k, vy2 ?k) = (vx2 1, vy2 1)"
      proof -
        \<comment> \<open>Evaluate LEAST at v\\_k: sector k-1 satisfies the predicate, and it's the minimum.\<close>
        let ?PL_vk = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
            (vx2 j - vx2 0)*(vy2 ?k - vy2 0) - (vy2 j - vy2 0)*(vx2 ?k - vx2 0) \<ge> 0 \<and>
            (vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0) \<le> 0"
        have hPLvk_km1: "?PL_vk (?k - 1)"
        proof -
          have "1 \<le> ?k - 1" using hk_ge2 by linarith
          moreover have "?k - 1 < ?k" using hk_ge2 by linarith
          moreover have "(vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0) \<ge> 0"
          proof -
            have "?k - 1 < ?n" using hk_ge2 by simp
            have "?k < ?n" by simp
            have "1 \<le> ?k - 1" using hk_ge2 by linarith
            from hfan_det_0[rule_format, OF \<open>?k - 1 < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k - 1\<close>]
            show ?thesis using hk_ge2 by linarith
          qed
          moreover have "Suc (?k - 1) = ?k" using hk_ge2 by linarith
          hence "(vx2(Suc(?k-1)) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc(?k-1)) - vy2 0)*(vx2 ?k - vx2 0) = 0"
            by simp
          hence "(vx2(Suc(?k-1)) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc(?k-1)) - vy2 0)*(vx2 ?k - vx2 0) \<le> 0"
            by linarith
          ultimately show ?thesis by (by100 auto)
        qed
        \<comment> \<open>LEAST\\_vk = k-1.\<close>
        have hPLvk_min: "\<And>j. ?PL_vk j \<Longrightarrow> ?k - 1 \<le> j"
        proof -
          fix j assume hj: "?PL_vk j"
          hence hj1: "1 \<le> j" and hjk: "j < ?k" and
            hupper: "(vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0) \<le> 0"
            by simp+
          show "?k - 1 \<le> j"
          proof (rule ccontr)
            assume "\<not> ?k - 1 \<le> j" hence "j < ?k - 1" by linarith
            hence "Suc j \<le> ?k - 1" by linarith
            hence "Suc j < ?k" by linarith
            have "Suc j < ?n" using \<open>Suc j < ?k\<close> by simp
            have hk_lt2: "?k < ?n" by simp
            have "1 \<le> Suc j" using hj1 by linarith
            from hfan_det_0[rule_format, OF \<open>Suc j < ?n\<close> hk_lt2 \<open>1 \<le> Suc j\<close> \<open>Suc j < ?k\<close>]
            have "(vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0) > 0" .
            with hupper show False by linarith
          qed
        qed
        have hLeast_vk: "(LEAST j. ?PL_vk j) = ?k - 1"
          using Least_equality[of ?PL_vk "?k - 1"] hPLvk_km1 hPLvk_min by (by100 blast)
        \<comment> \<open>Connect LEAST to phi\\_L\\_def and evaluate Cramer at v\\_k.\<close>
        \<comment> \<open>Direct computation: phi\\_L(v\\_k) with LEAST = k-1.
           ex = vx2(k-1) - vx2 0, ey = vy2(k-1) - vy2 0.
           fx = vx2 k - vx2 0 = dx, fy = vy2 k - vy2 0 = dy.
           det = ex*fy - ey*fx > 0 (fan det for k-1, k).
           s = (fy*dx - fx*dy)/det = (fy*fx - fx*fy)/det = 0.
           tp = (ex*dy - ey*dx)/det = (ex*fy - ey*fx)/det = det/det = 1.
           Result: (1-0-1)*vx2 0 + 0*vx2(k+1-(k-1)) + 1*vx2(k-(k-1)) = vx2 1.\<close>
        have hSuc_k: "Suc (length u2) = ?k" by simp
        have hSuc_km1: "Suc (?k - 1) = ?k" using hk_ge2 by linarith
        \<comment> \<open>The phi\\_L let-chain with j = k-1.\<close>
        have "phi_L (vx2 ?k, vy2 ?k)
          = (let ex = vx2(?k-1) - vx2 0; ey = vy2(?k-1) - vy2 0;
                 fx = vx2 ?k - vx2 0; fy = vy2 ?k - vy2 0;
                 dd = ex*fy - ey*fx;
                 dx = vx2 ?k - vx2 0; dy = vy2 ?k - vy2 0;
                 s = (fy*dx - fx*dy)/dd; tp = (ex*dy - ey*dx)/dd in
             ((1-s-tp)*vx2 0 + s*vx2(?k+1-(?k-1)) + tp*vx2(?k-(?k-1)),
              (1-s-tp)*vy2 0 + s*vy2(?k+1-(?k-1)) + tp*vy2(?k-(?k-1))))"
          unfolding phi_L_def Let_def using hLeast_vk hSuc_km1 by simp
        also have "\<dots> = (let dd = (vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0);
                 s = ((vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) - (vx2 ?k - vx2 0)*(vy2 ?k - vy2 0))/dd;
                 tp = ((vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0))/dd in
             ((1-s-tp)*vx2 0 + s*vx2(?k+1-(?k-1)) + tp*vx2(?k-(?k-1)),
              (1-s-tp)*vy2 0 + s*vy2(?k+1-(?k-1)) + tp*vy2(?k-(?k-1))))"
          unfolding Let_def by simp
        \<comment> \<open>Now s = 0/dd = 0 and tp = dd/dd = 1.\<close>
        also have "\<dots> = (vx2(?k-(?k-1)), vy2(?k-(?k-1)))"
        proof -
          have "((vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) - (vx2 ?k - vx2 0)*(vy2 ?k - vy2 0)) = 0"
            by (by100 algebra)
          moreover have hdd_pos: "(vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0) \<noteq> 0"
          proof -
            have "?k - 1 < ?n" using hk_ge2 by simp
            have "?k < ?n" by simp
            have "1 \<le> ?k - 1" using hk_ge2 by linarith
            from hfan_det_0[rule_format, OF \<open>?k - 1 < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k - 1\<close>]
            show ?thesis using hk_ge2 by linarith
          qed
          ultimately show ?thesis unfolding Let_def using hdd_pos by simp
        qed
        also have "\<dots> = (vx2 1, vy2 1)" using hk_ge2 by simp
        finally show ?thesis .
      qed
      have hphi_L_vk: "q2 (phi_L (vx2 ?k, vy2 ?k)) = q2 (vx2 (Suc ?k mod ?n), vy2 (Suc ?k mod ?n))"
      proof -
        have "q2 (phi_L (vx2 ?k, vy2 ?k)) = q2 (vx2 1, vy2 1)" using hphi_L_vk_val by simp
        \<comment> \<open>q2(v\\_1) = q2(v\\_{k+1}) from C7 for a-pair at t=1.\<close>
        also have "q2 (vx2 1, vy2 1) = q2 (vx2 (Suc ?k mod ?n), vy2 (Suc ?k mod ?n))"
        proof -
          have h1_in: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
          have h0_lt: "(0::nat) < ?n" using hn_ge3 by linarith
          have hk_lt2: "?k < ?n" by simp
          have hfst: "fst (?w ! 0) = fst (?w ! ?k)" by simp
          from hC7_2[rule_format, OF h0_lt hk_lt2 hfst h1_in]
          show ?thesis by (by100 simp)
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>C7 vertex identifications from the a-pair.\<close>
      have hq_v0_vk: "q2 (vx2 0, vy2 0) = q2 (vx2 ?k, vy2 ?k)"
      proof -
        have h0_in: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h0_lt: "(0::nat) < ?n" using hn_ge3 by linarith
        have hk_lt2: "?k < ?n" by simp
        have hfst: "fst (?w ! 0) = fst (?w ! ?k)" by simp
        from hC7_2[rule_format, OF h0_lt hk_lt2 hfst h0_in]
        show ?thesis by (by100 simp)
      qed
      have hjunction: "\<And>i t. i \<ge> ?k \<Longrightarrow> i < ?n \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) = 0 \<Longrightarrow>
          q2 (phi_L ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))
        = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
      proof -
        fix i t assume hik2: "i \<ge> ?k" and hi_lt2: "i < ?n" and ht2: "t \<in> I_set"
            and hcd0: "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) = 0"
        \<comment> \<open>cross\\_diag = 0 only at i=k,t=0 or i=n-1,t=1 (or k < i < n-1 NEVER).\<close>
        \<comment> \<open>Cross\\_diag = 0 for right half only at i=k,t=0 and i=n-1,t=1.\<close>
        \<comment> \<open>Case i=n-1, t=1: p = v\\_0. phi\\_L(v\\_0) = v\\_0. sigma(n-1,1) = v\\_k. q2(v\\_0) = q2(v\\_k).\<close>
        \<comment> \<open>Case i=k, t=0: p = v\\_k. phi\\_L(v\\_k) = v\\_1 (needs LEAST). sigma(k,0) = v\\_{k+1}. q2(v\\_1) = q2(v\\_{k+1}).\<close>
        \<comment> \<open>Case split: cross\\_diag = 0 only at i=k,t=0 and i=n-1,t=1.\<close>
        show "q2 (phi_L ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))
          = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
        proof (cases "i = ?n - 1")
          case True
          \<comment> \<open>i = n-1: cross\\_diag = 0 implies t = 1 (since cross\\_diag = (1-t)*positive).\<close>
          have hsi_n: "Suc i mod ?n = 0" using True hi_lt2 by simp
          have hcd_eq: "cross_diag ((1-t)*vx2 i + t*vx2 0, (1-t)*vy2 i + t*vy2 0) = 0"
            using hcd0 hsi_n by simp
          \<comment> \<open>cross\\_diag = (1-t)*cross(v\\_k, v\\_{n-1}). For this to be 0: t = 1 (since cross > 0 from fan det).\<close>
          have "t = 1"
          proof -
            have hcd_val: "cross_diag ((1-t)*vx2 i + t*vx2 0, (1-t)*vy2 i + t*vy2 0)
              = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))"
            proof -
              have "cross_diag ((1-t)*vx2 i + t*vx2 0, (1-t)*vy2 i + t*vy2 0)
                = (vx2 ?k - vx2 0) * ((1-t)*vy2 i + t*vy2 0 - vy2 0)
                - (vy2 ?k - vy2 0) * ((1-t)*vx2 i + t*vx2 0 - vx2 0)"
                unfolding cross_diag_def by simp
              also have "\<dots> = (vx2 ?k - vx2 0) * ((1-t)*(vy2 i - vy2 0))
                - (vy2 ?k - vy2 0) * ((1-t)*(vx2 i - vx2 0))"
                by (by100 algebra)
              also have "\<dots> = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))"
                by (by100 algebra)
              finally show ?thesis .
            qed
            have "1 \<le> i" using hik2 hk_ge2 by linarith
            have hk_lt2: "?k < ?n" by simp
            from hfan_det_0[rule_format, OF hk_lt2 hi_lt2]
            have hcross_pos: "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0) > 0"
            proof -
              have "?k < i" using hk_lt_nm1 True by simp
              from hfan_det_0[rule_format, OF hk_lt2 hi_lt2 _ \<open>?k < i\<close>] show ?thesis by simp
            qed
            from hcd_eq hcd_val have h_prod0: "(1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) = 0" by linarith
            have "1 - t = 0"
            proof (rule ccontr)
              assume "1 - t \<noteq> 0"
              with h_prod0 have "((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) = 0"
                by (by100 simp)
              with hcross_pos show False by linarith
            qed
            thus "t = 1" by linarith
          qed
          \<comment> \<open>At t=1: p = v\\_0.\<close>
          have hpx: "(1 - 1) * vx2 i + 1 * vx2 0 = vx2 0" by simp
          have hpy: "(1 - 1) * vy2 i + 1 * vy2 0 = vy2 0" by simp
          have "q2 (phi_L (vx2 0, vy2 0)) = q2 (vx2 0, vy2 0)" using hphi_L_v0 by simp
          also have "\<dots> = q2 (vx2 ?k, vy2 ?k)" using hq_v0_vk .
          also have "q2 (vx2 ?k, vy2 ?k) = q2 (paste_sigma vx2 vy2 ?k ?n i 1)"
            unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def using True by simp
          finally show ?thesis using \<open>t = 1\<close> hsi_n hpx hpy by simp
        next
          case False
          \<comment> \<open>For k < i < n-1: cross\\_diag > 0 for all t, contradicting hcd0. So i = k.\<close>
          have "i = ?k"
          proof (rule ccontr)
            assume "i \<noteq> ?k" hence "?k < i" using hik2 by linarith
            hence "i < ?n - 1" using hi_lt2 False by linarith
            \<comment> \<open>cross\\_diag > 0 for k < i < n-1.\<close>
            from hcd_right[OF hik2 hi_lt2 ht2] have hcd_ge: "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) \<ge> 0" .
            \<comment> \<open>Need strict > 0. Both cross(v\\_k,v\\_i) > 0 and cross(v\\_k,v\\_{i+1}) > 0 from fan det.\<close>
            \<comment> \<open>cross\\_diag = (1-t)*pos + t*pos > 0 since at least one of (1-t), t is > 0.\<close>
            have "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)) > 0"
            proof -
              \<comment> \<open>Decompose cross\\_diag via bilinearity.\<close>
              have hsi_lt: "Suc i < ?n" using \<open>i < ?n - 1\<close> by linarith
              have hsi_mod: "Suc i mod ?n = Suc i" using hsi_lt by simp
              have hk_lt_n: "?k < ?n" by simp
              \<comment> \<open>Fan det: both cross products > 0.\<close>
              have "1 \<le> ?k" by simp
              from hfan_det_0[rule_format, OF hk_lt_n hi_lt2 \<open>1 \<le> ?k\<close> \<open>?k < i\<close>]
              have hcki: "(vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0) > 0" .
              from hfan_det_0[rule_format, OF hk_lt_n hsi_lt \<open>1 \<le> ?k\<close>]
              have hcksi: "(vx2 ?k - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i) - vx2 0) > 0"
                using \<open>?k < i\<close> by linarith
              \<comment> \<open>Bilinearity: cross\\_diag = (1-t)*hcki + t*hcksi.\<close>
              have hcd_decomp: "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
                = (vx2 ?k - vx2 0) * ((1-t)*vy2 i + t*vy2(Suc i mod ?n) - vy2 0)
                - (vy2 ?k - vy2 0) * ((1-t)*vx2 i + t*vx2(Suc i mod ?n) - vx2 0)"
                unfolding cross_diag_def by simp
              also have "\<dots> = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
                + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))"
                by (by100 algebra)
              finally have hcd_bilin: "cross_diag ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
                = (1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
                + t * ((vx2 ?k - vx2 0)*(vy2(Suc i mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i mod ?n) - vx2 0))" .
              have ht01: "t \<ge> 0 \<and> t \<le> 1" using ht2 unfolding top1_unit_interval_def by (by100 auto)
              \<comment> \<open>At least one of (1-t)*hcki, t*hcksi is > 0.\<close>
              show ?thesis
              proof (cases "t = 0")
                case True
                have "(1-0) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) > 0"
                  using hcki by simp
                thus ?thesis using hcd_bilin True hsi_mod by simp
              next
                case False2: False hence "t > 0" using ht01 by linarith
                have "t * ((vx2 ?k - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i) - vx2 0)) > 0"
                  using mult_pos_pos[OF \<open>t > 0\<close> hcksi] .
                moreover have "(1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0)) \<ge> 0"
                  using mult_nonneg_nonneg[of "1-t" "((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))"]
                  ht01 hcki by linarith
                ultimately have "(1-t) * ((vx2 ?k - vx2 0)*(vy2 i - vy2 0) - (vy2 ?k - vy2 0)*(vx2 i - vx2 0))
                  + t * ((vx2 ?k - vx2 0)*(vy2(Suc i) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc i) - vx2 0)) > 0"
                  by linarith
                thus ?thesis using hcd_bilin hsi_mod by simp
              qed
            qed
            with hcd0 show False by linarith
          qed
          \<comment> \<open>For k < i < n-1: cross\\_diag > 0 for all t, contradicting hcd0.\<close>
          \<comment> \<open>So i = k.\<close>
          \<comment> \<open>i = k: cross\\_diag = t * cross(v\\_k, v\\_{k+1}). For t > 0 this is > 0.\<close>
          \<comment> \<open>So cross\\_diag = 0 requires t = 0.\<close>
          have "t = 0"
          proof -
            have hk_lt_nm1: "?k < ?n - 1" using \<open>i = ?k\<close> False hi_lt2 by linarith
            have hsk_lt: "Suc ?k < ?n" using hk_lt_nm1 by linarith
            have hsk_mod: "Suc ?k mod ?n = Suc ?k" using hsk_lt by simp
            \<comment> \<open>cross\\_diag at edge (k,t): bilinearity gives (1-t)*0 + t*fan\\_det(k,k+1).\<close>
            have hcd_val: "cross_diag ((1-t)*vx2 ?k + t*vx2(Suc ?k mod ?n), (1-t)*vy2 ?k + t*vy2(Suc ?k mod ?n))
              = t * ((vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0))"
            proof -
              have "cross_diag ((1-t)*vx2 ?k + t*vx2(Suc ?k), (1-t)*vy2 ?k + t*vy2(Suc ?k))
                = (vx2 ?k - vx2 0)*((1-t)*vy2 ?k + t*vy2(Suc ?k) - vy2 0)
                - (vy2 ?k - vy2 0)*((1-t)*vx2 ?k + t*vx2(Suc ?k) - vx2 0)"
                unfolding cross_diag_def by simp
              also have "\<dots> = (1-t)*((vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0))
                + t*((vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0))"
                by (by100 algebra)
              also have "(vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) = 0"
                by (by100 algebra)
              finally show ?thesis using hsk_mod by simp
            qed
            \<comment> \<open>Fan det: cross(v\\_k, v\\_{k+1}) > 0.\<close>
            have "?k < ?n" by simp
            have "1 \<le> ?k" using hk_ge2 by linarith
            from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> hsk_lt \<open>1 \<le> ?k\<close>]
            have hcross_pos: "(vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0) > 0"
              using hk_lt_nm1 by simp
            \<comment> \<open>cross\\_diag = 0 and cross > 0 implies t = 0.\<close>
            from hcd0 \<open>i = ?k\<close> have "cross_diag ((1-t)*vx2 ?k + t*vx2(Suc ?k mod ?n), (1-t)*vy2 ?k + t*vy2(Suc ?k mod ?n)) = 0"
              by simp
            with hcd_val have "t * ((vx2 ?k - vx2 0)*(vy2(Suc ?k) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc ?k) - vx2 0)) = 0"
              by linarith
            with hcross_pos show "t = 0" by (by100 simp)
          qed
          \<comment> \<open>At t=0, i=k: p = v\\_k. phi\\_L(v\\_k) = v\\_1 (from hphi\\_L\\_vk\\_val).\<close>
          have "q2 (phi_L (vx2 ?k, vy2 ?k)) = q2 (vx2 (Suc ?k mod ?n), vy2 (Suc ?k mod ?n))"
            using hphi_L_vk .
          also have "\<dots> = q2 (paste_sigma vx2 vy2 ?k ?n ?k 0)"
            unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def
            using hk_ge2 \<open>i = ?k\<close> by (by100 simp)
          finally show ?thesis using \<open>i = ?k\<close> \<open>t = 0\<close> by simp
        qed
      qed
      have hg_bdy: "\<forall>i<?n. \<forall>t\<in>I_set.
          g ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))
        = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
      proof (intro allI impI ballI)
        fix i t assume hi: "i < ?n" and ht: "t \<in> I_set"
        let ?p = "((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
        show "g ?p = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
        proof (cases "i < ?k")
          case True \<comment> \<open>Left half.\<close>
          have "cross_diag ?p \<le> 0" using hcd_left[OF True ht] .
          hence "g ?p = q2 (phi_L ?p)" unfolding g_def by simp
          also have "phi_L ?p = paste_sigma vx2 vy2 ?k ?n i t"
            using hphi_L_sigma[OF True ht] .
          finally show ?thesis .
        next
          case False hence hik: "i \<ge> ?k" by linarith
          \<comment> \<open>Right half: cross\\_diag \\<ge> 0.\<close>
          have hcd: "cross_diag ?p \<ge> 0" using hcd_right[OF hik hi ht] .
          show ?thesis
          proof (cases "cross_diag ?p > 0")
            case True
            hence "g ?p = q2 (phi_R ?p)" unfolding g_def by simp
            also have "phi_R ?p = paste_sigma vx2 vy2 ?k ?n i t"
              using hphi_R_sigma[OF hik hi ht] .
            finally show ?thesis .
          next
            case False
            hence "cross_diag ?p = 0" using hcd by linarith
            hence "g ?p = q2 (phi_L ?p)" unfolding g_def by simp
            also have "q2 (phi_L ?p) = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
              using hjunction[OF hik hi ht \<open>cross_diag ?p = 0\<close>] .
            finally show ?thesis .
          qed
        qed
      qed
      \<comment> \<open>Provide witnesses: P = P2, q = g, vx = vx2, vy = vy2.\<close>
      show ?thesis
      proof (rule exI[of _ P2], rule exI[of _ g], rule exI[of _ vx2], rule exI[of _ vy2],
             intro conjI)
        show "top1_is_polygonal_region_on P2 (length ?w')" by (rule hC1')
        show "top1_quotient_map_on P2
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P2) Y TY g"
          sorry \<comment> \<open>C2: g is quotient map. Piecewise continuous surjection, compact to Hausdorff.\<close>
        show "\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> (vx2 i, vy2 i) \<noteq> (vx2 j, vy2 j)"
          by (rule hC3')
        show "\<forall>i<length ?w'. (vx2 i, vy2 i) \<in> P2" by (rule hC4')
        show "P2 = {(x, y) | x y. \<exists>coeffs. (\<forall>i<length ?w'. coeffs i \<ge> 0) \<and>
            (\<Sum>i<length ?w'. coeffs i) = 1 \<and> x = (\<Sum>i<length ?w'. coeffs i * vx2 i) \<and>
            y = (\<Sum>i<length ?w'. coeffs i * vy2 i)}" by (rule hC5')
        show "\<forall>i<length ?w'. \<forall>j<length ?w'. i \<noteq> j \<longrightarrow> Suc i mod length ?w' \<noteq> j \<longrightarrow>
            i \<noteq> Suc j mod length ?w' \<longrightarrow> (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
            ((1-s)*vx2 i+s*vx2(Suc i mod length ?w'),(1-s)*vy2 i+s*vy2(Suc i mod length ?w'))
            \<noteq> ((1-t)*vx2 j+t*vx2(Suc j mod length ?w'),(1-t)*vy2 j+t*vy2(Suc j mod length ?w')))"
          by (rule hC6')
        show "\<forall>i<length ?w'. \<forall>j<length ?w'. fst (?w'!i) = fst (?w'!j) \<longrightarrow> (\<forall>t\<in>I_set.
            g ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w'))
            = (if snd(?w'!i)=snd(?w'!j) then g ((1-t)*vx2 j+t*vx2(Suc j mod length ?w'),
            (1-t)*vy2 j+t*vy2(Suc j mod length ?w'))
            else g (t*vx2 j+(1-t)*vx2(Suc j mod length ?w'),
            t*vy2 j+(1-t)*vy2(Suc j mod length ?w'))))"
        proof -
          \<comment> \<open>Step 1: hg\\_bdy available from outer scope.\<close>
          \<comment> \<open>Step 2: paste\\_chain\\_boundary\\_C7 gives C7 for q2 o sigma.\<close>
          have hlen3: "length ?w \<ge> 3"
            using quotient_scheme_length_ge3[OF hq] .
          from paste_chain_boundary_C7[OF hlen3 hfresh_c hC7_2]
          have hC7_sigma: "\<forall>i<length ?w'. \<forall>j<length ?w'. fst (?w'!i) = fst (?w'!j) \<longrightarrow>
              (\<forall>t\<in>I_set. q2 (paste_sigma vx2 vy2 ?k ?n i t)
               = (if snd(?w'!i) = snd(?w'!j)
                  then q2 (paste_sigma vx2 vy2 ?k ?n j t)
                  else q2 (paste_sigma vx2 vy2 ?k ?n j (1-t))))" .
          \<comment> \<open>Step 3: Combine: g on edges satisfies C7 for w'.\<close>
          show ?thesis
          proof (intro allI impI ballI)
            fix i j t assume hi: "i < length ?w'" and hj: "j < length ?w'"
                and hlbl: "fst(?w'!i) = fst(?w'!j)" and ht: "t \<in> I_set"
            have hi': "i < ?n" using hi hlen_eq by simp
            have hj': "j < ?n" using hj hlen_eq by simp
            have hg_i: "g ((1-t)*vx2 i+t*vx2(Suc i mod ?n),(1-t)*vy2 i+t*vy2(Suc i mod ?n))
              = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
              using hg_bdy[rule_format, OF hi' ht] .
            have hg_j: "g ((1-t)*vx2 j+t*vx2(Suc j mod ?n),(1-t)*vy2 j+t*vy2(Suc j mod ?n))
              = q2 (paste_sigma vx2 vy2 ?k ?n j t)"
              using hg_bdy[rule_format, OF hj' ht] .
            have ht_1mt: "(1-t) \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
            have hg_j_1mt: "g (t*vx2 j+(1-t)*vx2(Suc j mod ?n),t*vy2 j+(1-t)*vy2(Suc j mod ?n))
              = q2 (paste_sigma vx2 vy2 ?k ?n j (1-t))"
            proof -
              have "g ((1-(1-t))*vx2 j+(1-t)*vx2(Suc j mod ?n),(1-(1-t))*vy2 j+(1-t)*vy2(Suc j mod ?n))
                = q2 (paste_sigma vx2 vy2 ?k ?n j (1-t))"
                using hg_bdy[rule_format, OF hj' ht_1mt] .
              moreover have "(1-(1-t)) = t" by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
            from hC7_sigma[rule_format, OF hi hj hlbl ht]
            have "q2 (paste_sigma vx2 vy2 ?k ?n i t)
              = (if snd(?w'!i) = snd(?w'!j) then q2 (paste_sigma vx2 vy2 ?k ?n j t)
                 else q2 (paste_sigma vx2 vy2 ?k ?n j (1-t)))" .
            with hg_i hg_j hg_j_1mt hlen_eq show
              "g ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w'))
              = (if snd(?w'!i)=snd(?w'!j)
                 then g ((1-t)*vx2 j+t*vx2(Suc j mod length ?w'),(1-t)*vy2 j+t*vy2(Suc j mod length ?w'))
                 else g (t*vx2 j+(1-t)*vx2(Suc j mod length ?w'),t*vy2 j+(1-t)*vy2(Suc j mod length ?w')))"
              by (by5000 auto)
          qed
        qed
        \<comment> \<open>REUSABLE HELPERS for C8/C9 proofs (shared across multiple cases).\<close>
        have hsigma_in_P2: "\<And>i t. i < ?n \<Longrightarrow> t \<in> I_set \<Longrightarrow> paste_sigma vx2 vy2 ?k ?n i t \<in> P2"
        proof -
          fix i :: nat and t :: real assume hi: "i < ?n" and ht: "t \<in> I_set"
          \<comment> \<open>sigma(i,t) = (1-s)*v\\_a + s*v\\_b for some vertices a,b and parameter s.
             Show this is in P2 via hv2\\_in and P2 being a convex hull.\<close>
          have ht01: "t \<ge> 0 \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
          show "paste_sigma vx2 vy2 ?k ?n i t \<in> P2"
          proof (cases "i = 0 \<or> i = ?n - 1")
            case True
            \<comment> \<open>sigma = (1-t)*v\\_0 + t*v\\_k.\<close>
            have "paste_sigma vx2 vy2 ?k ?n i t = ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k)"
              using True unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by (by100 simp)
            moreover have "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<in> P2"
            proof -
              have "0 < ?n" using hn_ge3 by (by100 simp)
              have "?k < ?n" by (by100 simp)
              from polygonal_region_convex_combo[OF hP2 hn_ge3
                     hv2_in[rule_format, OF \<open>0 < ?n\<close>] hv2_in[rule_format, OF \<open>?k < ?n\<close>]]
                   ht01 show ?thesis by (by100 force)
            qed
            ultimately show ?thesis by (by100 simp)
          next
            case False hence hi0: "i \<noteq> 0" and hinm1: "i \<noteq> ?n - 1" by (by100 simp)+
            show ?thesis
            proof (cases "i \<le> ?k - 1")
              case True
              \<comment> \<open>sigma = t*v\\_{k-i} + (1-t)*v\\_{k+1-i}. Use convex combo with param 1-t.\<close>
              have "?k - i \<le> ?k" by (by100 simp)
              hence "?k - i < ?n" using hk_lt_nm1 by (by100 linarith)
              have "?k + 1 - i \<le> ?k" using True hi0 by (by100 linarith)
              hence "?k + 1 - i < ?n" using hk_lt_nm1 by (by100 linarith)
              have hva: "(vx2(?k-i), vy2(?k-i)) \<in> P2" using hv2_in[rule_format, OF \<open>?k-i < ?n\<close>] .
              have hvb: "(vx2(?k+1-i), vy2(?k+1-i)) \<in> P2" using hv2_in[rule_format, OF \<open>?k+1-i < ?n\<close>] .
              \<comment> \<open>Sigma = t*v\\_{k-i} + (1-t)*v\\_{k+1-i}. Use convex combo with reversed vertices and param 1-t.\<close>
              from polygonal_region_convex_combo[OF hP2 hn_ge3 hvb hva] ht01
              have "((1-t)*vx2(?k+1-i) + t*vx2(?k-i), (1-t)*vy2(?k+1-i) + t*vy2(?k-i)) \<in> P2"
                by (by100 force)
              moreover have "paste_sigma vx2 vy2 ?k ?n i t =
                (t*vx2(?k-i) + (1-t)*vx2(?k+1-i), t*vy2(?k-i) + (1-t)*vy2(?k+1-i))"
                using hi0 hinm1 True unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by (by100 simp)
              ultimately have "(t*vx2(?k-i) + (1-t)*vx2(?k+1-i), t*vy2(?k-i) + (1-t)*vy2(?k+1-i)) \<in> P2"
              proof -
                have hP2_mem: "((1-t)*vx2(?k+1-i) + t*vx2(?k-i), (1-t)*vy2(?k+1-i) + t*vy2(?k-i)) \<in> P2" by fact
                have hx: "(1-t)*vx2(?k+1-i) + t*vx2(?k-i) = t*vx2(?k-i) + (1-t)*vx2(?k+1-i)" by (by100 algebra)
                have hy: "(1-t)*vy2(?k+1-i) + t*vy2(?k-i) = t*vy2(?k-i) + (1-t)*vy2(?k+1-i)" by (by100 algebra)
                have "(t*vx2(?k-i) + (1-t)*vx2(?k+1-i), t*vy2(?k-i) + (1-t)*vy2(?k+1-i)) \<in> P2"
                  using hP2_mem hx hy by (by100 metis)
                thus ?thesis using \<open>paste_sigma vx2 vy2 ?k ?n i t =
                  (t*vx2(?k-i) + (1-t)*vx2(?k+1-i), t*vy2(?k-i) + (1-t)*vy2(?k+1-i))\<close>
                  by (by100 simp)
              qed
              thus ?thesis using \<open>paste_sigma vx2 vy2 ?k ?n i t =
                (t*vx2(?k-i) + (1-t)*vx2(?k+1-i), t*vy2(?k-i) + (1-t)*vy2(?k+1-i))\<close>
                by (by100 simp)
            next
              case False
              \<comment> \<open>sigma = (1-t)*v\\_{i+1} + t*v\\_{Suc(i+1) mod n}. Direct convex combo.\<close>
              have "i + 1 < ?n" using hinm1 hi by (by100 linarith)
              have "Suc(i+1) mod ?n < ?n" using hn_ge3 by (by100 simp)
              have hva: "(vx2(i+1), vy2(i+1)) \<in> P2" using hv2_in[rule_format, OF \<open>i+1 < ?n\<close>] .
              have hvb: "(vx2(Suc(i+1) mod ?n), vy2(Suc(i+1) mod ?n)) \<in> P2"
                using hv2_in[rule_format, OF \<open>Suc(i+1) mod ?n < ?n\<close>] .
              from polygonal_region_convex_combo[OF hP2 hn_ge3 hva hvb] ht01
              have "((1-t)*vx2(i+1) + t*vx2(Suc(i+1) mod ?n), (1-t)*vy2(i+1) + t*vy2(Suc(i+1) mod ?n)) \<in> P2"
                by (by100 force)
              moreover have "paste_sigma vx2 vy2 ?k ?n i t =
                ((1-t)*vx2(i+1) + t*vx2(Suc(i+1) mod ?n), (1-t)*vy2(i+1) + t*vy2(Suc(i+1) mod ?n))"
                using hi0 hinm1 False unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by (by100 simp)
              ultimately show ?thesis by (by100 simp)
            qed
          qed
        qed
        \<comment> \<open>Helper: cross\\_diag at vertex j = -fan\\_det(j,k), proved via commutativity.
           Used in hdiag\\_not\\_on\\_edge to determine cross\\_diag signs.\<close>
        have hcross_diag_neg_fan: "\<And>j. j < ?n \<Longrightarrow> 1 \<le> j \<Longrightarrow> j < ?k \<Longrightarrow>
          cross_diag (vx2 j, vy2 j) < 0"
        proof -
          fix j :: nat assume hj: "j < ?n" and hj1: "1 \<le> j" and hjk: "j < ?k"
          have "?k < ?n" by (by100 simp)
          from hfan_det_0[rule_format, OF hj \<open>?k < ?n\<close> hj1 hjk]
          have hfd: "(vx2 j - vx2 0)*(vy2 ?k - vy2 0) - (vy2 j - vy2 0)*(vx2 ?k - vx2 0) > 0" .
          have hcd_val: "cross_diag (vx2 j, vy2 j) =
            (vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)"
            unfolding cross_diag_def by (by100 simp)
          \<comment> \<open>cross\\_diag + fan\\_det = (cb - bc) + (ad - da) = 0 by commutativity.\<close>
          have h1: "(vx2 ?k - vx2 0)*(vy2 j - vy2 0) = (vy2 j - vy2 0)*(vx2 ?k - vx2 0)"
            by (rule mult.commute)
          have h2: "(vy2 ?k - vy2 0)*(vx2 j - vx2 0) = (vx2 j - vx2 0)*(vy2 ?k - vy2 0)"
            by (rule mult.commute)
          from hcd_val h1 h2 hfd show "cross_diag (vx2 j, vy2 j) < 0" by (by100 linarith)
        qed
        have hcross_diag_pos_fan: "\<And>j. j < ?n \<Longrightarrow> ?k < j \<Longrightarrow>
          cross_diag (vx2 j, vy2 j) > 0"
        proof -
          fix j :: nat assume hj: "j < ?n" and hkj: "?k < j"
          have "?k < ?n" by (by100 simp)
          have "1 \<le> ?k" using hk_ge2 by (by100 linarith)
          from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> hj \<open>1 \<le> ?k\<close> hkj]
          have hfd: "(vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0) > 0" .
          have hcd_val: "cross_diag (vx2 j, vy2 j) =
            (vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)"
            unfolding cross_diag_def by (by100 simp)
          from hcd_val hfd show "cross_diag (vx2 j, vy2 j) > 0" by (by100 linarith)
        qed
        have hdiag_not_on_edge: "\<And>t. t \<in> {0<..<(1::real)} \<Longrightarrow>
            \<forall>i'<?n. \<forall>t'\<in>I_set. ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<noteq>
              ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
        proof -
          fix t :: real assume ht_int: "t \<in> {0<..<(1::real)}"
          have ht_gt: "t > 0" and ht_lt: "t < 1" using ht_int by (by100 simp)+
          have hcd_diag: "cross_diag ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) = 0"
          proof -
            have "(vx2 ?k - vx2 0) * ((1-t)*vy2 0 + t*vy2 ?k - vy2 0) -
              (vy2 ?k - vy2 0) * ((1-t)*vx2 0 + t*vx2 ?k - vx2 0) = 0"
              by (by100 algebra)
            thus ?thesis unfolding cross_diag_def by (by100 simp)
          qed
          have hcd_v0: "cross_diag (vx2 0, vy2 0) = 0" unfolding cross_diag_def by (by100 simp)
          have hcd_vk: "cross_diag (vx2 ?k, vy2 ?k) = 0"
          proof -
            have "(vx2 ?k - vx2 0) * (vy2 ?k - vy2 0) - (vy2 ?k - vy2 0) * (vx2 ?k - vx2 0) = 0"
              by (by100 algebra)
            thus ?thesis unfolding cross_diag_def by (by100 simp)
          qed
          \<comment> \<open>Diagonal point \\<noteq> v\\_0 and \\<noteq> v\\_k.\<close>
          have hne_v0: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<noteq> (vx2 0, vy2 0)"
          proof
            assume heq_v0: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) = (vx2 0, vy2 0)"
            hence "(1-t)*vx2 0 + t*vx2 ?k = vx2 0" "(1-t)*vy2 0 + t*vy2 ?k = vy2 0" by (by100 simp)+
            hence heq_x: "(1-t)*vx2 0 + t*vx2 ?k - vx2 0 = 0" and
                  heq_y: "(1-t)*vy2 0 + t*vy2 ?k - vy2 0 = 0" by (by100 simp)+
            have "t * (vx2 ?k - vx2 0) = 0" using heq_x by (by100 algebra)
            moreover have "t * (vy2 ?k - vy2 0) = 0" using heq_y by (by100 algebra)
            ultimately have "vx2 ?k = vx2 0" "vy2 ?k = vy2 0" using ht_gt by (by100 force)+
            moreover have "(vx2 0, vy2 0) \<noteq> (vx2 ?k, vy2 ?k)"
              using hC3_2[rule_format] hk_ge2 hn_ge3 by (by100 force)
            ultimately show False by (by100 simp)
          qed
          have hne_vk: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<noteq> (vx2 ?k, vy2 ?k)"
          proof
            assume heq_vk: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) = (vx2 ?k, vy2 ?k)"
            hence heq_x2: "(1-t)*vx2 0 + t*vx2 ?k - vx2 ?k = 0" and
                  heq_y2: "(1-t)*vy2 0 + t*vy2 ?k - vy2 ?k = 0" by (by100 simp)+
            have hx2: "(1-t) * (vx2 0 - vx2 ?k) = 0" using heq_x2 by (by100 algebra)
            have hy2: "(1-t) * (vy2 0 - vy2 ?k) = 0" using heq_y2 by (by100 algebra)
            from hx2 ht_lt have "vx2 0 = vx2 ?k" by (by100 force)
            moreover from hy2 ht_lt have "vy2 0 = vy2 ?k" by (by100 force)
            moreover have "(vx2 0, vy2 0) \<noteq> (vx2 ?k, vy2 ?k)"
              using hC3_2[rule_format] hk_ge2 hn_ge3 by (by100 force)
            ultimately show False by (by100 simp)
          qed
          show "\<forall>i'<?n. \<forall>t'\<in>I_set. ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<noteq>
            ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
          proof (cases "?k < ?n - 1")
            case hk_lt: True
            show ?thesis
            proof (intro allI impI ballI)
              fix i' :: nat and t' :: real assume "i' < ?n" and "t' \<in> I_set"
              show "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) \<noteq>
                ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
              proof
                assume heq: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) =
                  ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
                \<comment> \<open>cross\\_diag of the edge point = 0.\<close>
                have hcd_ep: "cross_diag ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n),
                  (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n)) = 0"
                  using hcd_diag heq by (by100 simp)
                \<comment> \<open>cd vertex signs: v\\_0, v\\_k = 0; 1..k-1 < 0; k+1..n-1 > 0.\<close>
                have hSuc: "Suc i' mod ?n < ?n" by (by100 simp)
                \<comment> \<open>Edge point = v\\_0 or v\\_k (from cd sign analysis).\<close>
                \<comment> \<open>cd(v\\_{i'}) and cd(v\\_{Suc i' mod n}) determine the edge cd.\<close>
                have hcd_i': "cross_diag (vx2 i', vy2 i') = 0 \<or>
                  cross_diag (vx2 i', vy2 i') < 0 \<or> cross_diag (vx2 i', vy2 i') > 0"
                  by (by100 linarith)
                have hcd_si': "cross_diag (vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0 \<or>
                  cross_diag (vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0 \<or>
                  cross_diag (vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                  by (by100 linarith)
                \<comment> \<open>cd is affine: cd(edge(i',t')) = (1-t')cd(v\\_{i'}) + t'cd(v\\_{Suc i'}).\<close>
                have hcd_aff: "cross_diag ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n),
                  (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n)) =
                  (1-t')*cross_diag(vx2 i', vy2 i') +
                  t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n))"
                proof -
                  let ?a = "vx2 ?k - vx2 0" and ?b = "vy2 ?k - vy2 0"
                  have lhs: "cross_diag ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n),
                    (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n)) =
                    ?a * ((1-t')*vy2 i' + t'*vy2(Suc i' mod ?n) - vy2 0) -
                    ?b * ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n) - vx2 0)"
                    unfolding cross_diag_def by (by100 simp)
                  have rhs: "(1-t')*cross_diag(vx2 i', vy2 i') +
                    t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) =
                    (1-t')*(?a * (vy2 i' - vy2 0) - ?b * (vx2 i' - vx2 0)) +
                    t'*(?a * (vy2(Suc i' mod ?n) - vy2 0) - ?b * (vx2(Suc i' mod ?n) - vx2 0))"
                    unfolding cross_diag_def by (by100 simp)
                  show ?thesis
                    unfolding lhs rhs by (by100 algebra)
                qed
                have ht'_ge: "t' \<ge> 0" and ht'_le: "t' \<le> 1"
                  using \<open>t' \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 auto)+
                \<comment> \<open>From hcd\\_ep = 0 and hcd\\_aff: (1-t')*A + t'*B = 0 with t'\\<in>[0,1].
                   Case: both A,B same sign \\<noteq> 0 \\<to> impossible.
                   Case: one = 0, other \\<noteq> 0 \\<to> t'=0 or 1 \\<to> edge point is vertex.\<close>
                have "((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))
                  = (vx2 0, vy2 0) \<or>
                  ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))
                  = (vx2 ?k, vy2 ?k)"
                proof -
                  from hcd_ep hcd_aff
                  have hsum0: "(1-t')*cross_diag(vx2 i', vy2 i') +
                    t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0"
                    by (by100 linarith)
                  \<comment> \<open>cd(v\\_j) = 0 iff j = 0 or j = k (when k < n-1).\<close>
                  have hcd0_iff: "\<And>j. j < ?n \<Longrightarrow> cross_diag(vx2 j, vy2 j) = 0 \<Longrightarrow> j = 0 \<or> j = ?k"
                  proof -
                    fix j :: nat assume hj: "j < ?n" and hcd0: "cross_diag(vx2 j, vy2 j) = 0"
                    show "j = 0 \<or> j = ?k"
                    proof (rule ccontr)
                      assume "\<not> (j = 0 \<or> j = ?k)"
                      hence hj0: "j \<noteq> 0" and hjk: "j \<noteq> ?k" by (by100 simp)+
                      have "1 \<le> j" using hj0 by (by100 linarith)
                      show False
                      proof (cases "j < ?k")
                        case True
                        from hcross_diag_neg_fan[OF hj \<open>1 \<le> j\<close> True]
                        show False using hcd0 by (by100 linarith)
                      next
                        case False hence "?k < j" using hjk by (by100 linarith)
                        from hcross_diag_pos_fan[OF hj \<open>?k < j\<close>]
                        show False using hcd0 by (by100 linarith)
                      qed
                    qed
                  qed
                  \<comment> \<open>If cd(v\\_{i'}) \\<noteq> 0 and cd(v\\_{Suc i'}) \\<noteq> 0 with same sign: sum \\<noteq> 0.\<close>
                  \<comment> \<open>If different signs: sum = 0 at some t' \\<in> (0,1), but then edge point is NOT a vertex.\<close>
                  \<comment> \<open>The only resolution: one endpoint has cd = 0, forcing t'=0 or 1.\<close>
                  show ?thesis
                  proof (cases "cross_diag(vx2 i', vy2 i') = 0")
                    case True
                    hence "i' = 0 \<or> i' = ?k" using hcd0_iff \<open>i' < ?n\<close> by (by100 blast)
                    from hsum0 True have "t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0"
                      by (by100 simp)
                    show ?thesis
                    proof (cases "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0")
                      case True2: True
                      hence "Suc i' mod ?n = 0 \<or> Suc i' mod ?n = ?k" using hcd0_iff hSuc by (by100 blast)
                      \<comment> \<open>Both endpoints have cd = 0: both are v\\_0 or v\\_k. But consecutive vertices
                         \\<to> would need i'=0,Suc i'=k or i'=k,Suc i'=0 or... contradicts k \\<ge> 2.\<close>
                      \<comment> \<open>Both endpoints cd=0: i' \\<in> \\{0,k\\} and Suc i' mod n \\<in> \\{0,k\\}.
                         Consecutive vertices both in \\{0,k\\} with k \\<ge> 2 and k < n-1: impossible.\<close>
                      have False
                      proof -
                        from \<open>i' = 0 \<or> i' = ?k\<close> \<open>Suc i' mod ?n = 0 \<or> Suc i' mod ?n = ?k\<close>
                        show False
                        proof (elim disjE)
                          assume "i' = 0" "Suc i' mod ?n = 0"
                          hence "Suc 0 mod ?n = 0" by (by100 simp)
                          hence "(1::nat) = 0" using hn_ge3 by (by100 simp)
                          thus False by (by100 simp)
                        next
                          assume "i' = 0" "Suc i' mod ?n = ?k"
                          hence "1 = ?k" using hn_ge3 by (by100 simp)
                          with hk_ge2 show False by (by100 linarith)
                        next
                          assume "i' = ?k" "Suc i' mod ?n = 0"
                          hence "Suc ?k mod ?n = 0" by (by100 simp)
                          have "?k < ?n" by (by100 simp)
                          hence "Suc ?k \<le> ?n" by (by100 linarith)
                          have "Suc ?k > 0" by (by100 simp)
                          from \<open>Suc ?k mod ?n = 0\<close> have "?n dvd Suc ?k"
                            by (by100 auto)
                          with \<open>Suc ?k \<le> ?n\<close> \<open>Suc ?k > 0\<close> have "Suc ?k = ?n"
                            using Suc_leI dvd_imp_le le_antisym by (by100 blast)
                          hence "?k = ?n - 1" by (by100 linarith)
                          with hk_lt show False by (by100 linarith)
                        next
                          assume "i' = ?k" "Suc i' mod ?n = ?k"
                          hence "Suc ?k mod ?n = ?k" by (by100 simp)
                          have "?k < ?n" by (by100 simp)
                          hence "Suc ?k \<le> ?n" by (by100 linarith)
                          show False
                          proof (cases "Suc ?k < ?n")
                            case True3: True
                            hence "Suc ?k mod ?n = Suc ?k" by (by100 simp)
                            with \<open>Suc ?k mod ?n = ?k\<close> show False by (by100 linarith)
                          next
                            case False3: False
                            with \<open>Suc ?k \<le> ?n\<close> have "Suc ?k = ?n" by (by100 linarith)
                            hence "Suc ?k mod ?n = 0" by (by100 simp)
                            with \<open>Suc ?k mod ?n = ?k\<close> have "?k = 0" by (by100 simp)
                            with hk_ge2 show False by (by100 linarith)
                          qed
                        qed
                      qed
                      thus ?thesis by (by100 blast)
                    next
                      case False2: False
                      \<comment> \<open>cd(Suc i') \\<noteq> 0 so t' = 0 from t'*nonzero = 0.\<close>
                      from \<open>t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0\<close> False2
                      have "t' = 0" by (by100 force)
                      hence "((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))
                        = (vx2 i', vy2 i')" by (by100 simp)
                      with \<open>i' = 0 \<or> i' = ?k\<close> show ?thesis by (by100 auto)
                    qed
                  next
                    case False
                    show ?thesis
                    proof (cases "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0")
                      case True2: True
                      hence "Suc i' mod ?n = 0 \<or> Suc i' mod ?n = ?k" using hcd0_iff hSuc by (by100 blast)
                      from hsum0 True2 have "(1-t')*cross_diag(vx2 i', vy2 i') = 0"
                        by (by100 simp)
                      with False have "1-t' = 0" by (by100 force)
                      hence "t' = 1" by (by100 linarith)
                      hence "((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))
                        = (vx2(Suc i' mod ?n), vy2(Suc i' mod ?n))" by (by100 simp)
                      with \<open>Suc i' mod ?n = 0 \<or> Suc i' mod ?n = ?k\<close> show ?thesis by (by100 auto)
                    next
                      case False2: False
                      \<comment> \<open>Both cd \\<noteq> 0. Same sign \\<to> sum \\<noteq> 0. Different signs: possible but still sum \\<noteq> 0
                         because convex combination of same-sign nonzeros is nonzero.\<close>
                      \<comment> \<open>Actually: if cd(v\\_{i'}) < 0 and cd(v\\_{Suc i'}) < 0: both < 0, sum < 0 \\<noteq> 0.
                         Similarly both > 0. Mixed signs: can be 0 but then the point is interior, not vertex.\<close>
                      \<comment> \<open>But mixed signs can only happen if one is left (cd<0) and other is right (cd>0).
                         In a convex polygon, consecutive vertices cannot jump from left to right
                         without passing through 0 (v\\_0 or v\\_k). Since k<n-1 and k\\<ge>2, the only
                         transition edges are 0 (v\\_0 to v\\_1) and k-1 (v\\_{k-1} to v\\_k) and k (v\\_k to v\\_{k+1})
                         and n-1 (v\\_{n-1} to v\\_0). But all transition edges have one endpoint at v\\_0 or v\\_k (cd=0),
                         which contradicts both cd \\<noteq> 0.\<close>
                      from False False2 show ?thesis
                      proof -
                        have "cross_diag(vx2 i', vy2 i') < 0 \<or> cross_diag(vx2 i', vy2 i') > 0"
                          using False by (by100 linarith)
                        moreover have "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0 \<or>
                          cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                          using False2 by (by100 linarith)
                        ultimately show ?thesis
                        proof (elim disjE)
                          \<comment> \<open>Case: both < 0. Sum < 0 \\<noteq> 0.\<close>
                          assume "cross_diag(vx2 i', vy2 i') < 0"
                            "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0"
                          hence "(1-t')*cross_diag(vx2 i', vy2 i') +
                            t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0"
                          proof -
                            have "(1-t')*cross_diag(vx2 i', vy2 i') \<le> 0"
                              using mult_nonneg_nonpos[of "1-t'" "cross_diag(vx2 i', vy2 i')"]
                                ht'_le \<open>cross_diag(vx2 i', vy2 i') < 0\<close> by (by100 linarith)
                            moreover have "t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) \<le> 0"
                              using mult_nonneg_nonpos[of "t'" "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n))"]
                                ht'_ge \<open>cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0\<close> by (by100 linarith)
                            moreover have "(1-t')*cross_diag(vx2 i', vy2 i') \<noteq> 0 \<or>
                              t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) \<noteq> 0"
                              using \<open>cross_diag(vx2 i', vy2 i') < 0\<close>
                                \<open>cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0\<close>
                                ht'_ge ht'_le by (by100 force)
                            ultimately show ?thesis by (by100 linarith)
                          qed
                          with hsum0 have False by (by100 linarith)
                          thus ?thesis by (by100 blast)
                        next
                          \<comment> \<open>Case: both > 0. Sum > 0 \\<noteq> 0.\<close>
                          assume "cross_diag(vx2 i', vy2 i') > 0"
                            "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                          hence "(1-t')*cross_diag(vx2 i', vy2 i') +
                            t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                          proof -
                            have "(1-t')*cross_diag(vx2 i', vy2 i') \<ge> 0"
                              using mult_nonneg_nonneg[of "1-t'" "cross_diag(vx2 i', vy2 i')"]
                                ht'_le \<open>cross_diag(vx2 i', vy2 i') > 0\<close> by (by100 linarith)
                            moreover have "t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) \<ge> 0"
                              using mult_nonneg_nonneg[of "t'" "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n))"]
                                ht'_ge \<open>cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0\<close> by (by100 linarith)
                            moreover have "(1-t')*cross_diag(vx2 i', vy2 i') \<noteq> 0 \<or>
                              t'*cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) \<noteq> 0"
                              using \<open>cross_diag(vx2 i', vy2 i') > 0\<close>
                                \<open>cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0\<close>
                                ht'_ge ht'_le by (by100 force)
                            ultimately show ?thesis by (by100 linarith)
                          qed
                          with hsum0 have False by (by100 linarith)
                          thus ?thesis by (by100 blast)
                        next
                          \<comment> \<open>Mixed: cd(i') < 0, cd(Suc i') > 0. But then i' \\<in> left, Suc i' \\<in> right.
                             Consecutive vertices can't jump left-to-right without passing through v\\_0 or v\\_k.
                             In polygon order: left vertices are 1..k-1, right vertices are k+1..n-1.
                             The only transition is at vertex k (between left and right side).
                             If i' < k and Suc i' > k: then i' = k-1 and Suc i' = k. But cd(k)=0, contradicting cd>0.\<close>
                          assume hA: "cross_diag(vx2 i', vy2 i') < 0"
                            and hB: "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                          \<comment> \<open>i' \\<in> {1..k-1} from cd < 0.\<close>
                          have "i' \<noteq> 0"
                          proof assume "i' = 0" hence "cross_diag(vx2 i', vy2 i') = 0"
                            using hcd_v0 by (by100 simp)
                            with hA show False by (by100 linarith) qed
                          have "i' \<noteq> ?k"
                          proof assume "i' = ?k" hence "cross_diag(vx2 i', vy2 i') = 0"
                            using hcd_vk by (by100 simp)
                            with hA show False by (by100 linarith) qed
                          have "1 \<le> i'" using \<open>i' \<noteq> 0\<close> by (by100 linarith)
                          have "i' < ?k"
                          proof (rule ccontr)
                            assume "\<not> (i' < ?k)"
                            hence "?k < i'" using \<open>i' \<noteq> ?k\<close> by (by100 linarith)
                            from hcross_diag_pos_fan[OF \<open>i' < ?n\<close> \<open>?k < i'\<close>]
                            show False using hA by (by100 linarith)
                          qed
                          \<comment> \<open>Suc i' mod n = Suc i' since i' < k < n-1.\<close>
                          have "Suc i' < ?n" using \<open>i' < ?k\<close> hk_lt by (by100 linarith)
                          hence "Suc i' mod ?n = Suc i'" by (by100 simp)
                          hence "Suc i' \<le> ?k" using \<open>i' < ?k\<close> by (by100 linarith)
                          show ?thesis
                          proof (cases "Suc i' = ?k")
                            case True3: True
                            hence "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0"
                              using \<open>Suc i' mod ?n = Suc i'\<close> hcd_vk by (by100 simp)
                            with hB have False by (by100 linarith)
                            thus ?thesis by (by100 blast)
                          next
                            case False3: False
                            hence "Suc i' < ?k" using \<open>Suc i' \<le> ?k\<close> by (by100 linarith)
                            have "1 \<le> Suc i'" by (by100 linarith)
                            from hcross_diag_neg_fan[OF hSuc[unfolded \<open>Suc i' mod ?n = Suc i'\<close>]
                              \<open>1 \<le> Suc i'\<close> \<open>Suc i' < ?k\<close>]
                            have "cross_diag(vx2(Suc i'), vy2(Suc i')) < 0" .
                            hence "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0"
                              using \<open>Suc i' mod ?n = Suc i'\<close> by (by100 simp)
                            with hB have False by (by100 linarith)
                            thus ?thesis by (by100 blast)
                          qed
                        next
                          \<comment> \<open>Mixed: cd(i') > 0, cd(Suc i') < 0. Similar: i' is right, Suc i' is left.
                             Transition at n-1 to 0 goes right-to-left through v\\_0 (cd=0).\<close>
                          assume hA: "cross_diag(vx2 i', vy2 i') > 0"
                            and hB: "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) < 0"
                          have "i' \<noteq> 0"
                          proof assume "i' = 0" hence "cross_diag(vx2 i', vy2 i') = 0"
                            using hcd_v0 by (by100 simp)
                            with hA show False by (by100 linarith) qed
                          have "i' \<noteq> ?k"
                          proof assume "i' = ?k" hence "cross_diag(vx2 i', vy2 i') = 0"
                            using hcd_vk by (by100 simp)
                            with hA show False by (by100 linarith) qed
                          have "?k < i'"
                          proof (rule ccontr)
                            assume "\<not> (?k < i')"
                            hence "i' \<le> ?k" by (by100 linarith)
                            hence "i' < ?k" using \<open>i' \<noteq> ?k\<close> by (by100 linarith)
                            have "1 \<le> i'" using \<open>i' \<noteq> 0\<close> by (by100 linarith)
                            from hcross_diag_neg_fan[OF \<open>i' < ?n\<close> \<open>1 \<le> i'\<close> \<open>i' < ?k\<close>]
                            show False using hA by (by100 linarith)
                          qed
                          \<comment> \<open>Suc i' mod n: if i' < n-1 then Suc i', otherwise 0.\<close>
                          show ?thesis
                          proof (cases "i' = ?n - 1")
                            case True3: True
                            hence "Suc i' mod ?n = 0" using hn_ge3 by (by100 simp)
                            hence "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) = 0"
                              using hcd_v0 by (by100 simp)
                            with hB have False by (by100 linarith)
                            thus ?thesis by (by100 blast)
                          next
                            case False3: False
                            hence "Suc i' mod ?n = Suc i'" using \<open>i' < ?n\<close> by (by100 simp)
                            have "?k < Suc i'" using \<open>?k < i'\<close> by (by100 linarith)
                            have "Suc i' < ?n" using \<open>i' < ?n\<close> False3 by (by100 linarith)
                            from hcross_diag_pos_fan[OF \<open>Suc i' < ?n\<close> \<open>?k < Suc i'\<close>]
                            have "cross_diag(vx2(Suc i'), vy2(Suc i')) > 0" .
                            hence "cross_diag(vx2(Suc i' mod ?n), vy2(Suc i' mod ?n)) > 0"
                              using \<open>Suc i' mod ?n = Suc i'\<close> by (by100 simp)
                            with hB have False by (by100 linarith)
                            thus ?thesis by (by100 blast)
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
                \<comment> \<open>But diagonal point is neither v\\_0 nor v\\_k.\<close>
                thus False using heq hne_v0 hne_vk by (by100 auto)
              qed
            qed
          next
            case hk_eq: False
            hence "?k = ?n - 1" using hk_ge2 by (by100 simp)
            show ?thesis sorry \<comment> \<open>k = n-1: diagonal IS edge n-1. Needs C9 restructuring.\<close>
          qed
        qed
        have hnonc_sigma_on_edge: "\<And>i t. i < ?n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> ?n - 1 \<Longrightarrow> t \<in> {0<..<(1::real)} \<Longrightarrow>
            \<exists>i'<?n. \<exists>t'\<in>{0<..<(1::real)}. paste_sigma vx2 vy2 ?k ?n i t =
              ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
        proof -
          fix i :: nat and t :: real
          assume hi: "i < ?n" and hi0: "i \<noteq> 0" and hinm1: "i \<noteq> ?n - 1" and ht: "t \<in> {0<..<(1::real)}"
          show "\<exists>i'<?n. \<exists>t'\<in>{0<..<(1::real)}. paste_sigma vx2 vy2 ?k ?n i t =
              ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
          proof (cases "i \<le> ?k - 1")
            case True
            \<comment> \<open>1 \\<le> i \\<le> k-1: sigma(i,t) = t*v\\_{k-i} + (1-t)*v\\_{k+1-i} = old edge (k-i) at param (1-t).\<close>
            have "paste_chain_sigma_x vx2 ?k ?n i t = t*vx2(?k-i) + (1-t)*vx2(?k+1-i)"
              using hi0 hinm1 True unfolding paste_chain_sigma_x_def by (by100 simp)
            moreover have "paste_chain_sigma_y vy2 ?k ?n i t = t*vy2(?k-i) + (1-t)*vy2(?k+1-i)"
              using hi0 hinm1 True unfolding paste_chain_sigma_y_def by (by100 simp)
            moreover have "?k - i < ?n" using True hi by (by100 simp)
            moreover have "Suc (?k - i) mod ?n = ?k + 1 - i"
            proof -
              have "i \<le> ?k" using True by (by100 simp)
              have "?k - i < ?n - 1" using True hi hinm1 hi0 hk_lt_nm1 by (by100 simp)
              hence "Suc (?k - i) < ?n" by (by100 simp)
              hence "Suc (?k - i) mod ?n = Suc (?k - i)" by (by100 simp)
              also have "Suc (?k - i) = ?k + 1 - i" using \<open>i \<le> ?k\<close> by (by100 simp)
              finally show ?thesis .
            qed
            moreover have "(1-t) \<in> {0<..<(1::real)}" using open_unit_interval_one_minus[OF ht] .
            ultimately have hsig_eq: "paste_sigma vx2 vy2 ?k ?n i t =
                ((1-(1-t))*vx2(?k-i) + (1-t)*vx2(?k+1-i), (1-(1-t))*vy2(?k-i) + (1-t)*vy2(?k+1-i))"
              by (by100 simp)
            have hsuc_eq: "?k + 1 - i = Suc (?k - i) mod ?n"
              using \<open>Suc (?k - i) mod ?n = ?k + 1 - i\<close> by (by100 simp)
            show ?thesis
            proof (rule exI[of _ "?k - i"], rule conjI)
              show "?k - i < ?n" using \<open>?k - i < ?n\<close> .
            next
              show "\<exists>t'\<in>{0<..<(1::real)}. paste_sigma vx2 vy2 ?k ?n i t =
                ((1-t')*vx2(?k-i) + t'*vx2(Suc(?k-i) mod ?n), (1-t')*vy2(?k-i) + t'*vy2(Suc(?k-i) mod ?n))"
              proof (rule bexI[of _ "1-t"])
                show "paste_sigma vx2 vy2 ?k ?n i t =
                  ((1-(1-t))*vx2(?k-i) + (1-t)*vx2(Suc(?k-i) mod ?n),
                   (1-(1-t))*vy2(?k-i) + (1-t)*vy2(Suc(?k-i) mod ?n))"
                  using hsig_eq hsuc_eq by (by100 simp)
              next
                show "(1-t) \<in> {0<..<(1::real)}" using open_unit_interval_one_minus[OF ht] .
              qed
            qed
          next
            case False
            hence "i \<ge> ?k" using hi0 by (by100 simp)
            \<comment> \<open>k \\<le> i < n-1: sigma(i,t) = (1-t)*v\\_{i+1} + t*v\\_{Suc(i+1) mod n} = old edge (i+1) at param t.\<close>
            have hsig_x: "paste_chain_sigma_x vx2 ?k ?n i t = (1-t)*vx2(i+1) + t*vx2(Suc(i+1) mod ?n)"
              using hi0 hinm1 False unfolding paste_chain_sigma_x_def by (by100 simp)
            have hsig_y: "paste_chain_sigma_y vy2 ?k ?n i t = (1-t)*vy2(i+1) + t*vy2(Suc(i+1) mod ?n)"
              using hi0 hinm1 False unfolding paste_chain_sigma_y_def by (by100 simp)
            have hi1: "i + 1 < ?n" using hinm1 hi by (by100 simp)
            show ?thesis
              apply (rule exI[of _ "i + 1"])
              apply (rule conjI, rule hi1)
              apply (rule bexI[of _ t])
              using hsig_x hsig_y ht by simp_all
          qed
        qed
        \<comment> \<open>Stronger version: t' is also in (0,1) (not just I\\_set).\<close>
        have hnonc_sigma_on_edge_int: "\<And>i t. i < ?n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> ?n - 1 \<Longrightarrow> t \<in> {0<..<(1::real)} \<Longrightarrow>
            \<exists>i'<?n. \<exists>t'\<in>{0<..<(1::real)}. paste_sigma vx2 vy2 ?k ?n i t =
              ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
        proof -
          fix i :: nat and t :: real
          assume hi: "i < ?n" and hi0: "i \<noteq> 0" and hinm1: "i \<noteq> ?n - 1" and ht: "t \<in> {0<..<(1::real)}"
          from hnonc_sigma_on_edge[OF hi hi0 hinm1 ht] show
            "\<exists>i'<?n. \<exists>t'\<in>{0<..<(1::real)}. paste_sigma vx2 vy2 ?k ?n i t =
              ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))" .
        qed
        \<comment> \<open>Full sigma dictionary: non-c-edge i returns old index, rev\\_flag, label, sign, i\\_old formula.\<close>
        have hnonc_sigma_dict: "\<And>i t. i < ?n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> ?n - 1 \<Longrightarrow> t \<in> {0<..<(1::real)} \<Longrightarrow>
          \<exists>i_old rev_flag. i_old < ?n \<and>
            (if rev_flag then 1 - t else t) \<in> {0<..<(1::real)} \<and>
            paste_sigma vx2 vy2 ?k ?n i t =
              ((1-(if rev_flag then 1-t else t))*vx2 i_old +
               (if rev_flag then 1-t else t)*vx2(Suc i_old mod ?n),
               (1-(if rev_flag then 1-t else t))*vy2 i_old +
               (if rev_flag then 1-t else t)*vy2(Suc i_old mod ?n)) \<and>
            fst (?w' ! i) = fst (?w ! i_old) \<and>
            (snd (?w' ! i) = snd (?w ! i_old)) = (\<not> rev_flag) \<and>
            i_old = (if rev_flag then ?k - i else Suc i) \<and>
            (if rev_flag then i \<le> ?k - 1 else i \<ge> ?k)"
        proof -
          fix i :: nat and t :: real
          assume hi: "i < ?n" and hi0: "i \<noteq> 0" and hinm1: "i \<noteq> ?n - 1" and ht: "t \<in> {0<..<(1::real)}"
          have hdata: "\<exists>i_old rev_flag.
            i_old < ?n \<and>
            (if rev_flag then 1 - t else t) \<in> {0<..<(1::real)} \<and>
            paste_chain_sigma_x vx2 ?k ?n i t =
              (1 - (if rev_flag then 1 - t else t)) * vx2 i_old +
              (if rev_flag then 1 - t else t) * vx2 (Suc i_old mod ?n) \<and>
            paste_chain_sigma_y vy2 ?k ?n i t =
              (1 - (if rev_flag then 1 - t else t)) * vy2 i_old +
              (if rev_flag then 1 - t else t) * vy2 (Suc i_old mod ?n) \<and>
            fst (?w' ! i) = fst (?w ! i_old) \<and>
            (snd (?w' ! i) = snd (?w ! i_old)) = (\<not> rev_flag) \<and>
            i_old = (if rev_flag then ?k - i else Suc i) \<and>
            (if rev_flag then i \<le> ?k - 1 else i \<ge> ?k)"
          proof (cases "i \<le> ?k - 1")
            case True
            have hki: "?k - i < ?n" using True hi by (by100 simp)
            have h1mt: "(1-t) \<in> {0<..<(1::real)}" using open_unit_interval_one_minus[OF ht] .
            have hsx: "paste_chain_sigma_x vx2 ?k ?n i t = t*vx2(?k-i) + (1-t)*vx2(?k+1-i)"
              using hi0 hinm1 True unfolding paste_chain_sigma_x_def by (by100 simp)
            have hsy: "paste_chain_sigma_y vy2 ?k ?n i t = t*vy2(?k-i) + (1-t)*vy2(?k+1-i)"
              using hi0 hinm1 True unfolding paste_chain_sigma_y_def by (by100 simp)
            have hSuc_mod: "Suc (?k - i) mod ?n = ?k + 1 - i"
            proof -
              have "i \<le> ?k" using True by (by100 simp)
              have "?k - i < ?n - 1" using True hi hinm1 hi0 hk_lt_nm1 by (by100 simp)
              hence "Suc (?k - i) < ?n" by (by100 simp)
              hence "Suc (?k - i) mod ?n = Suc (?k - i)" by (by100 simp)
              also have "Suc (?k - i) = ?k + 1 - i" using \<open>i \<le> ?k\<close> by (by100 simp)
              finally show ?thesis .
            qed
            \<comment> \<open>Label/sign: w'!i = inv(u2!(|u2|-i)), w!(k-i) = u2!(|u2|-i).\<close>
            have hi1: "1 \<le> i" using hi0 by (by100 simp)
            have hik: "i \<le> length u2" using True by (by100 simp)
            have hw'i: "?w' ! i = top1_inverse_edge (u2 ! (length u2 - i))"
            proof -
              have him1: "i - 1 < length u2" using hi1 hik by (by100 linarith)
              have "?w' ! i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
                using hi1 by (by100 simp)
              also have "\<dots> = rev (map top1_inverse_edge u2) ! (i - 1)"
                using him1 nth_append[of "rev (map top1_inverse_edge u2)" "v @ [(c, True)]" "i - 1"]
                by (by100 simp)
              also have "\<dots> = (map top1_inverse_edge u2) ! (length u2 - 1 - (i - 1))"
                using rev_nth[of "i - 1" "map top1_inverse_edge u2"] him1 by (by100 simp)
              also have "length u2 - 1 - (i - 1) = length u2 - i" using hi1 him1 by (by100 linarith)
              also have "(map top1_inverse_edge u2) ! (length u2 - i) =
                top1_inverse_edge (u2 ! (length u2 - i))"
                using hi1 hik by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            have hw_ki: "?w ! (?k - i) = u2 ! (length u2 - i)"
            proof -
              have hki_ge1: "?k - i \<ge> 1" using hi1 True by (by100 linarith)
              have hki_lt: "?k - i < Suc (length u2)" using hi1 hik by (by100 linarith)
              have "?w ! (?k - i) = ((a, True) # u2 @ [(a, True)] @ v) ! (?k - i)" by (by100 simp)
              also have "\<dots> = ((a, True) # u2) ! (?k - i)"
                using nth_append[of "(a,True) # u2" "[(a,True)] @ v" "?k - i"] hki_lt
                by (by100 simp)
              also have "\<dots> = u2 ! (?k - i - 1)" using hki_ge1 by (by100 simp)
              also have "?k - i - 1 = length u2 - i" using hi1 by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            have hlbl: "fst (?w' ! i) = fst (?w ! (?k - i))"
              using hw'i hw_ki unfolding top1_inverse_edge_def by (by100 simp)
            have hsign: "snd (?w' ! i) \<noteq> snd (?w ! (?k - i))"
              using hw'i hw_ki unfolding top1_inverse_edge_def by (by100 simp)
            show ?thesis
              apply (rule exI[of _ "?k - i"], rule exI[of _ True])
              using hki h1mt hsx hsy hSuc_mod hlbl hsign True by (by5000 simp)
          next
            case False hence hige: "i \<ge> ?k" using hi0 by (by100 simp)
            have hsi: "Suc i < ?n" using hinm1 hi by (by100 simp)
            have hsx: "paste_chain_sigma_x vx2 ?k ?n i t = (1-t)*vx2(Suc i) + t*vx2(Suc(Suc i) mod ?n)"
              using hi0 hinm1 False unfolding paste_chain_sigma_x_def by (by100 simp)
            have hsy: "paste_chain_sigma_y vy2 ?k ?n i t = (1-t)*vy2(Suc i) + t*vy2(Suc(Suc i) mod ?n)"
              using hi0 hinm1 False unfolding paste_chain_sigma_y_def by (by100 simp)
            \<comment> \<open>Label/sign: w'!i = v!(i-1-|u2|), w!(Suc i) = v!(i-1-|u2|).\<close>
            have him1_ge: "i - 1 \<ge> length u2" using hige by (by100 linarith)
            have hile: "i \<le> length u2 + length v"
            proof -
              have "i \<le> ?n - 2" using hi hinm1 by (by100 linarith)
              thus ?thesis by (by100 simp)
            qed
            hence him1_lt: "i - 1 < length u2 + length v" using hi0 by (by100 linarith)
            have him1_v: "i - 1 - length u2 < length v" using him1_lt him1_ge by (by100 linarith)
            have hw'i: "?w' ! i = v ! (i - 1 - length u2)"
            proof -
              have "?w' ! i = (rev (map top1_inverse_edge u2) @ v @ [(c, True)]) ! (i - 1)"
                using hi0 by (by100 simp)
              also have "\<dots> = (v @ [(c, True)]) ! (i - 1 - length u2)"
                using him1_ge nth_append[of "rev (map top1_inverse_edge u2)" "v @ [(c, True)]" "i - 1"]
                by (by100 simp)
              also have "\<dots> = v ! (i - 1 - length u2)"
                using him1_v nth_append[of v "[(c, True)]" "i - 1 - length u2"] by (by100 simp)
              finally show ?thesis .
            qed
            have hw_si: "?w ! Suc i = v ! (i - 1 - length u2)"
            proof -
              have hsi_ge: "Suc i \<ge> Suc (Suc (length u2))" using hige by (by100 linarith)
              have "?w ! Suc i = ([(a,True)] @ u2 @ [(a,True)] @ v) ! Suc i" by (by100 simp)
              also have "\<dots> = v ! (Suc i - Suc (Suc (length u2)))"
                using hsi_ge nth_append[of "[(a,True)] @ u2 @ [(a,True)]" v "Suc i"]
                by (by100 simp)
              moreover have "Suc i - Suc (Suc (length u2)) = i - 1 - length u2"
                using hige by (by100 linarith)
              ultimately show ?thesis by (by100 simp)
            qed
            have hlbl: "fst (?w' ! i) = fst (?w ! Suc i)" using hw'i hw_si by (by100 simp)
            have hsign: "snd (?w' ! i) = snd (?w ! Suc i)" using hw'i hw_si by (by100 simp)
            show ?thesis
              apply (rule exI[of _ "Suc i"], rule exI[of _ False])
              using hsi ht hsx hsy hlbl hsign hige by (by5000 simp)
          qed
          then obtain i_old rev_flag where
            h1: "i_old < ?n" and
            h2: "(if rev_flag then 1 - t else t) \<in> {0<..<(1::real)}" and
            h3x: "paste_chain_sigma_x vx2 ?k ?n i t =
              (1 - (if rev_flag then 1 - t else t)) * vx2 i_old +
              (if rev_flag then 1 - t else t) * vx2 (Suc i_old mod ?n)" and
            h3y: "paste_chain_sigma_y vy2 ?k ?n i t =
              (1 - (if rev_flag then 1 - t else t)) * vy2 i_old +
              (if rev_flag then 1 - t else t) * vy2 (Suc i_old mod ?n)" and
            h4: "fst (?w' ! i) = fst (?w ! i_old)" and
            h5: "(snd (?w' ! i) = snd (?w ! i_old)) = (\<not> rev_flag)" and
            h6: "i_old = (if rev_flag then ?k - i else Suc i)" and
            h7: "(if rev_flag then i \<le> ?k - 1 else i \<ge> ?k)"
            by (by5000 blast)
          \<comment> \<open>Convert sigma\\_x/y to paste\\_sigma pair.\<close>
          have h3: "paste_sigma vx2 vy2 ?k ?n i t =
            ((1-(if rev_flag then 1-t else t))*vx2 i_old +
             (if rev_flag then 1-t else t)*vx2(Suc i_old mod ?n),
             (1-(if rev_flag then 1-t else t))*vy2 i_old +
             (if rev_flag then 1-t else t)*vy2(Suc i_old mod ?n))"
            using h3x h3y unfolding paste_chain_sigma_x_def[symmetric] paste_chain_sigma_y_def[symmetric]
            by (by100 simp)
          show "\<exists>i_old rev_flag. i_old < ?n \<and>
            (if rev_flag then 1 - t else t) \<in> {0<..<(1::real)} \<and>
            paste_sigma vx2 vy2 ?k ?n i t =
              ((1-(if rev_flag then 1-t else t))*vx2 i_old +
               (if rev_flag then 1-t else t)*vx2(Suc i_old mod ?n),
               (1-(if rev_flag then 1-t else t))*vy2 i_old +
               (if rev_flag then 1-t else t)*vy2(Suc i_old mod ?n)) \<and>
            fst (?w' ! i) = fst (?w ! i_old) \<and>
            (snd (?w' ! i) = snd (?w ! i_old)) = (\<not> rev_flag) \<and>
            i_old = (if rev_flag then ?k - i else Suc i) \<and>
            (if rev_flag then i \<le> ?k - 1 else i \<ge> ?k)"
            using h1 h2 h3 h4 h5 h6 h7 by (by5000 blast)
        qed
        show "\<forall>p\<in>P2. (\<forall>i<length ?w'. \<forall>t\<in>I_set.
            p \<noteq> ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w')))
            \<longrightarrow> (\<forall>p'\<in>P2. g p = g p' \<longrightarrow> p = p')"
        proof (intro ballI impI allI)
          fix p p' assume hp: "p \<in> P2" and hp': "p' \<in> P2"
              and hint: "\<forall>i<length ?w'. \<forall>t\<in>I_set.
                p \<noteq> ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w'))"
              and heq: "g p = g p'"
          \<comment> \<open>C8 proof: g injective on target interior. Cases by cross\\_diag sign.\<close>
          have haffine_nonneg: "\<And>p A B C :: real. p \<in> P2 \<Longrightarrow>
              (\<forall>l<?n. A + B * vx2 l + C * vy2 l \<ge> 0) \<Longrightarrow>
              A + B * fst p + C * snd p \<ge> 0"
          proof -
            fix p :: "real \<times> real" and A B C :: real
            assume hp_in: "p \<in> P2"
            assume hvertex: "\<forall>l<?n. A + B * vx2 l + C * vy2 l \<ge> 0"
            from hp_in[unfolded hC5_2]
            obtain coeffs where hc_nn: "\<forall>i<?n. coeffs i \<ge> 0"
              and hc_sum: "(\<Sum>i<?n. coeffs i) = 1"
              and hx_fst: "fst p = (\<Sum>i<?n. coeffs i * vx2 i)"
              and hx_snd: "snd p = (\<Sum>i<?n. coeffs i * vy2 i)"
              by (by5000 auto)
            have hsd1: "A * (\<Sum>i<?n. coeffs i) = (\<Sum>i<?n. A * coeffs i)"
              by (rule sum_distrib_left)
            have hsd2: "B * (\<Sum>i<?n. coeffs i * vx2 i) = (\<Sum>i<?n. B * (coeffs i * vx2 i))"
              by (rule sum_distrib_left)
            have hsd3: "C * (\<Sum>i<?n. coeffs i * vy2 i) = (\<Sum>i<?n. C * (coeffs i * vy2 i))"
              by (rule sum_distrib_left)
            have "A * (\<Sum>i<?n. coeffs i) + B * (\<Sum>i<?n. coeffs i * vx2 i) + C * (\<Sum>i<?n. coeffs i * vy2 i)
              = (\<Sum>i<?n. A * coeffs i) + (\<Sum>i<?n. B * (coeffs i * vx2 i)) + (\<Sum>i<?n. C * (coeffs i * vy2 i))"
              using hsd1 hsd2 hsd3 by (by100 simp)
            also have "\<dots> = (\<Sum>i<?n. A * coeffs i + B * (coeffs i * vx2 i) + C * (coeffs i * vy2 i))"
              by (simp only: sum.distrib[symmetric])
            also have "\<dots> = (\<Sum>i<?n. coeffs i * (A + B * vx2 i + C * vy2 i))"
              by (rule sum.cong, simp, by100 algebra)
            finally have hsum_expand: "A * (\<Sum>i<?n. coeffs i) + B * (\<Sum>i<?n. coeffs i * vx2 i) + C * (\<Sum>i<?n. coeffs i * vy2 i)
              = (\<Sum>i<?n. coeffs i * (A + B * vx2 i + C * vy2 i))" .
            have "A + B * fst p + C * snd p =
              (\<Sum>i<?n. coeffs i * (A + B * vx2 i + C * vy2 i))"
              using hc_sum hx_fst hx_snd hsum_expand by (by100 simp)
            also have "\<dots> \<ge> 0"
            proof (rule sum_nonneg)
              fix i assume "i \<in> {..<?n}"
              hence "i < ?n" by (by100 simp)
              hence "coeffs i \<ge> 0" using hc_nn by (by100 blast)
              moreover have "A + B * vx2 i + C * vy2 i \<ge> 0" using hvertex \<open>i < ?n\<close> by (by100 blast)
              ultimately show "coeffs i * (A + B * vx2 i + C * vy2 i) \<ge> 0"
                using mult_nonneg_nonneg by (by100 blast)
            qed
            finally show "A + B * fst p + C * snd p \<ge> 0" .
          qed
          have hphi_L_in_P2: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x \<le> 0 \<Longrightarrow> phi_L x \<in> P2"
          proof -
            fix x assume hx: "x \<in> P2" and hcd: "cross_diag x \<le> 0"
            \<comment> \<open>Step 1: cross\\_1(x) \\<ge> 0 from haffine\\_nonneg.\<close>
            have hcross1_ge: "(vx2 1 - vx2 0)*(snd x - vy2 0) - (vy2 1 - vy2 0)*(fst x - vx2 0) \<ge> 0"
            proof -
              \<comment> \<open>Express cross\\_1 as A + B*X + C*Y:
                 cross\\_1(X,Y) = (vx2 1 - vx2 0)*(Y - vy2 0) - (vy2 1 - vy2 0)*(X - vx2 0)
                 = -(vx2 1 - vx2 0)*vy2 0 + (vy2 1 - vy2 0)*vx2 0 + (-(vy2 1 - vy2 0))*X + (vx2 1 - vx2 0)*Y
                 = A + B*X + C*Y where
                 A = (vy2 1 - vy2 0)*vx2 0 - (vx2 1 - vx2 0)*vy2 0
                 B = -(vy2 1 - vy2 0), C = (vx2 1 - vx2 0)\<close>
              let ?A = "(vy2 1 - vy2 0)*vx2 0 - (vx2 1 - vx2 0)*vy2 0"
              let ?B = "-(vy2 1 - vy2 0)" let ?C = "vx2 1 - vx2 0"
              have hrewrite: "(vx2 1 - vx2 0)*(snd x - vy2 0) - (vy2 1 - vy2 0)*(fst x - vx2 0)
                = ?A + ?B * fst x + ?C * snd x" by (by100 algebra)
              have "\<forall>l<?n. ?A + ?B * vx2 l + ?C * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval: "?A + ?B * vx2 l + ?C * vy2 l =
                  (vx2 1 - vx2 0)*(vy2 l - vy2 0) - (vy2 1 - vy2 0)*(vx2 l - vx2 0)"
                  by (by100 algebra)
                show "?A + ?B * vx2 l + ?C * vy2 l \<ge> 0"
                proof (cases "l = 0")
                  case True thus ?thesis unfolding hval by (by100 simp)
                next
                  case False hence hl1: "1 \<le> l" by (by100 linarith)
                  show ?thesis
                  proof (cases "l = 1")
                    case True thus ?thesis unfolding hval by (by100 simp)
                  next
                    case False hence hl2: "l \<ge> 2" using hl1 by (by100 linarith)
                    have "1 < l" using hl2 by (by100 linarith)
                    have h1_lt_n: "(1::nat) < ?n" using hn_ge3 by (by100 linarith)
                    have h1le1: "(1::nat) \<le> 1" by simp
                    from hfan_det_0[rule_format, OF h1_lt_n hl h1le1 \<open>1 < l\<close>]
                    show ?thesis unfolding hval by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this] show ?thesis unfolding hrewrite .
            qed
            \<comment> \<open>cross\\_k(x) \\<le> 0 from hcd.\<close>
            have hcrossk_le: "(vx2 ?k - vx2 0)*(snd x - vy2 0) - (vy2 ?k - vy2 0)*(fst x - vx2 0) \<le> 0"
              using hcd unfolding cross_diag_def by (by100 simp)
            \<comment> \<open>Step 1b: Sector existence via discrete IVT.\<close>
            let ?PL = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc j) - vy2 0)*(fst x - vx2 0) \<le> 0"
            have hex: "\<exists>j. ?PL j"
            proof -
              \<comment> \<open>Discrete IVT: find first j \\<ge> 1 where cross\\_{j+1} \\<le> 0.\<close>
              define f where "f j = (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0)" for j
              have hf1: "f 1 \<ge> 0" using hcross1_ge unfolding f_def .
              have hfk: "f ?k \<le> 0" using hcrossk_le unfolding f_def .
              \<comment> \<open>By strong induction: \\<exists>j \\<ge> 1. j < k \\<and> f j \\<ge> 0 \\<and> f(Suc j) \\<le> 0.\<close>
              have hivt: "\<forall>m. 1 \<le> m \<longrightarrow> m < ?k \<longrightarrow> f m \<ge> 0 \<longrightarrow>
                  (\<exists>j. m \<le> j \<and> j < ?k \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0)"
              proof (intro allI impI)
                fix m assume hm1: "1 \<le> m" and hmk: "m < ?k" and hfm: "f m \<ge> 0"
                show "\<exists>j. m \<le> j \<and> j < ?k \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0"
                  using hmk hfm
                proof (induction "?k - m" arbitrary: m)
                  case 0 thus ?case by linarith
                next
                  case (Suc d)
                  show ?case
                  proof (cases "f (Suc m) \<le> 0")
                    case True
                    show ?thesis
                      apply (rule exI[of _ m])
                      using True Suc.prems by (by100 blast)
                  next
                    case False hence hfSm_pos: "f (Suc m) > 0" by linarith
                    hence hfSm: "f (Suc m) \<ge> 0" by linarith
                    have "Suc m \<le> ?k" using Suc.prems Suc.hyps by linarith
                    moreover have "Suc m \<noteq> ?k"
                    proof
                      assume "Suc m = ?k"
                      hence "f (Suc m) \<le> 0" using hfk by (by100 simp)
                      with hfSm_pos show False by linarith
                    qed
                    ultimately have "Suc m < ?k" by linarith
                    have "d = ?k - Suc m" using Suc.hyps by linarith
                    from Suc.hyps(1)[OF \<open>d = ?k - Suc m\<close> \<open>Suc m < ?k\<close> hfSm]
                    obtain j where hj: "Suc m \<le> j" "j < ?k" "f j \<ge> 0" "f (Suc j) \<le> 0" by blast
                    hence "m \<le> j" by linarith
                    with hj show ?thesis by (by100 blast)
                  qed
                qed
              qed
              have h1ltk: "1 < ?k" using hk_ge2 by linarith
              from hivt[rule_format, OF le_refl h1ltk hf1]
              obtain j where hj: "1 \<le> j" "j < ?k" "f j \<ge> 0" "f (Suc j) \<le> 0"
                by (by100 blast)
              thus ?thesis unfolding f_def by (by100 blast)
            qed
            from LeastI_ex[OF this]
            have hPL: "?PL (LEAST j. ?PL j)" .
            let ?j = "LEAST j. ?PL j"
            have hj1: "1 \<le> ?j" using hPL by (by100 blast)
            have hjk: "?j < ?k" using hPL by (by100 blast)
            have hcross_ge: "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0) \<ge> 0"
              using hPL by (by100 blast)
            have hcross_le: "(vx2(Suc ?j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) \<le> 0"
              using hPL by (by100 blast)
            \<comment> \<open>Step 2: det > 0 from fan determinant.\<close>
            have hk_lt_n_local: "?k < ?n" using hk_lt_nm1 by (by100 linarith)
            have hj_lt: "?j < ?n" using hjk hk_lt_n_local by (by100 linarith)
            have hsj_lt: "Suc ?j < ?n" using hjk hk_lt_nm1 by (by100 linarith)
            let ?det = "(vx2 ?j - vx2 0) * (vy2(Suc ?j) - vy2 0)
              - (vy2 ?j - vy2 0) * (vx2(Suc ?j) - vx2 0)"
            have hdet_pos: "?det > 0"
              using hfan_det_0[rule_format, OF hj_lt hsj_lt hj1 lessI] .
            \<comment> \<open>Step 3: Cramer coords are non-negative.\<close>
            let ?s_num = "(vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) - (vx2(Suc ?j) - vx2 0)*(snd x - vy2 0)"
            let ?tp_num = "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0)"
            let ?s = "?s_num / ?det"
            let ?tp = "?tp_num / ?det"
            have hs_num_nn: "?s_num \<ge> 0" using hcross_le by linarith
            have htp_num_nn: "?tp_num \<ge> 0" using hcross_ge by linarith
            have hs_ge0: "?s \<ge> 0"
              using hs_num_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            have htp_ge0: "?tp \<ge> 0"
              using htp_num_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            have h1stp_ge0: "1 - ?s - ?tp \<ge> 0"
            proof -
              \<comment> \<open>1-s-tp = (det - s\\_num - tp\\_num)/det = F(x)/det where
                 F(x) = cross(v\\_j - x, v\\_{j+1} - x) is affine and \\<ge> 0 at all vertices.\<close>
              have hnum_eq: "?det - ?s_num - ?tp_num =
                (vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)"
                by (by100 algebra)
              \<comment> \<open>Express as A + B*X + C*Y.\<close>
              let ?Aj = "vx2 ?j * vy2(Suc ?j) - vy2 ?j * vx2(Suc ?j)"
              let ?Bj = "vy2 ?j - vy2(Suc ?j)" let ?Cj = "vx2(Suc ?j) - vx2 ?j"
              have hF_form: "(vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)
                = ?Aj + ?Bj * fst x + ?Cj * snd x" by (by100 algebra)
              have "\<forall>l<?n. ?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval: "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                  (vx2 ?j - vx2 l)*(vy2(Suc ?j) - vy2 l) - (vy2 ?j - vy2 l)*(vx2(Suc ?j) - vx2 l)"
                  by (by100 algebra)
                \<comment> \<open>= -cross(v\\_l - v\\_j, v\\_{j+1} - v\\_j). From C11: this is > 0 for l \\<noteq> j, j+1.\<close>
                show "?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
                proof (cases "l = ?j")
                  case True thus ?thesis unfolding hval by (by100 simp)
                next
                  case False
                  show ?thesis
                  proof (cases "l = Suc ?j")
                    case True thus ?thesis unfolding hval by (by100 simp)
                  next
                    case False2: False
                    have hsj_mod: "Suc ?j mod ?n = Suc ?j" using hsj_lt by (by100 simp)
                    have hl_ne_sj_mod: "l \<noteq> Suc ?j mod ?n" using False2 hsj_mod by (by100 simp)
                    from hC11_2[rule_format, OF hj_lt hl False hl_ne_sj_mod]
                    have "(vx2 l - vx2 ?j) * (vy2(Suc ?j mod ?n) - vy2 ?j)
                      - (vy2 l - vy2 ?j) * (vx2(Suc ?j mod ?n) - vx2 ?j) < 0" .
                    hence "(vx2 l - vx2 ?j) * (vy2(Suc ?j) - vy2 ?j)
                      - (vy2 l - vy2 ?j) * (vx2(Suc ?j) - vx2 ?j) < 0"
                      using hsj_mod by (by100 simp)
                    \<comment> \<open>cross(v\\_l - v\\_j, v\\_{j+1} - v\\_j) < 0, so F(v\\_l) = -cross > 0.\<close>
                    moreover have "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                      -((vx2 l - vx2 ?j) * (vy2(Suc ?j) - vy2 ?j)
                      - (vy2 l - vy2 ?j) * (vx2(Suc ?j) - vx2 ?j))"
                      unfolding hval by (by100 algebra)
                    ultimately show ?thesis by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this]
              have hF_ge0: "?Aj + ?Bj * fst x + ?Cj * snd x \<ge> 0" .
              hence hnum_ge0: "?det - ?s_num - ?tp_num \<ge> 0"
                using hnum_eq hF_form by linarith
              \<comment> \<open>Multiply approach: (1-s-tp)*det = det - s\\_num - tp\\_num \\<ge> 0, and det > 0.\<close>
              have hne: "?det \<noteq> 0" using hdet_pos by linarith
              have hs_cancel: "?s * ?det = ?s_num" using hne by (by100 simp)
              have htp_cancel: "?tp * ?det = ?tp_num" using hne by (by100 simp)
              have "(1 - ?s - ?tp) * ?det = ?det - ?s * ?det - ?tp * ?det"
                by (by100 algebra)
              hence "(1 - ?s - ?tp) * ?det = ?det - ?s_num - ?tp_num"
                using hs_cancel htp_cancel by linarith
              hence h_prod_nn: "(1 - ?s - ?tp) * ?det \<ge> 0" using hnum_ge0 by linarith
              show ?thesis
              proof (rule ccontr)
                assume "\<not> (1 - ?s - ?tp \<ge> 0)"
                hence "1 - ?s - ?tp < 0" by linarith
                hence "(1 - ?s - ?tp) * ?det < 0" using hdet_pos
                  using mult_neg_pos by (by100 blast)
                with h_prod_nn show False by linarith
              qed
            qed
            \<comment> \<open>Step 4: phi\\_L(x) is a convex combination of 3 vertices \\<in> P2.\<close>
            have hphi_eq: "phi_L x = ((1-?s-?tp)*vx2 0 + ?s*vx2(?k+1-?j) + ?tp*vx2(?k-?j),
                                       (1-?s-?tp)*vy2 0 + ?s*vy2(?k+1-?j) + ?tp*vy2(?k-?j))"
              unfolding phi_L_def Let_def by (by100 simp)
            \<comment> \<open>Step 5: Vertex indices valid and in P2.\<close>
            have hA_lt: "?k + 1 - ?j < ?n" using hjk hk_lt_n_local hj1 by (by100 linarith)
            have hB_lt: "?k - ?j < ?n" using hjk hk_lt_n_local by (by100 linarith)
            \<comment> \<open>Step 6: Convex combination of P2 vertices is in P2.\<close>
            \<comment> \<open>Need: 0, k+1-j, k-j are distinct indices < n.\<close>
            have hA_ne_0: "?k + 1 - ?j \<noteq> (0::nat)" using hjk hj1 hk_ge2 by (by100 linarith)
            have hB_ne_0: "?k - ?j \<noteq> (0::nat)" using hjk hj1 by (by100 linarith)
            have hA_ne_B: "?k + 1 - ?j \<noteq> ?k - ?j" using hj1 hjk by (by100 linarith)
            have h0_lt: "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
            show "phi_L x \<in> P2"
            proof -
              \<comment> \<open>Extract vertex P2 memberships as barycentric coords.\<close>
              have hv0: "(vx2 0, vy2 0) \<in> P2" using hv2_in h0_lt by (by100 blast)
              have hvA: "(vx2 (?k+1-?j), vy2 (?k+1-?j)) \<in> P2" using hv2_in hA_lt by (by100 blast)
              have hvB: "(vx2 (?k-?j), vy2 (?k-?j)) \<in> P2" using hv2_in hB_lt by (by100 blast)
              from hv0[unfolded hC5_2] obtain c0 where
                hc0: "\<forall>i<?n. c0 i \<ge> 0" "(\<Sum>i<?n. c0 i) = 1"
                     "vx2 0 = (\<Sum>i<?n. c0 i * vx2 i)" "vy2 0 = (\<Sum>i<?n. c0 i * vy2 i)"
                by (by5000 auto)
              from hvA[unfolded hC5_2] obtain cA where
                hcA: "\<forall>i<?n. cA i \<ge> 0" "(\<Sum>i<?n. cA i) = 1"
                     "vx2(?k+1-?j) = (\<Sum>i<?n. cA i * vx2 i)" "vy2(?k+1-?j) = (\<Sum>i<?n. cA i * vy2 i)"
                by (by5000 auto)
              from hvB[unfolded hC5_2] obtain cB where
                hcB: "\<forall>i<?n. cB i \<ge> 0" "(\<Sum>i<?n. cB i) = 1"
                     "vx2(?k-?j) = (\<Sum>i<?n. cB i * vx2 i)" "vy2(?k-?j) = (\<Sum>i<?n. cB i * vy2 i)"
                by (by5000 auto)
              \<comment> \<open>Combined coefficient: cc = (1-s-tp)*c0 + s*cA + tp*cB.\<close>
              define cc where "cc i = (1-?s-?tp) * c0 i + ?s * cA i + ?tp * cB i" for i
              \<comment> \<open>All coefficients \\<ge> 0.\<close>
              have hcc_nn: "\<forall>i<?n. cc i \<ge> 0"
              proof (intro allI impI)
                fix i :: nat assume hi: "i < ?n"
                have "(1-?s-?tp) * c0 i \<ge> 0"
                  using h1stp_ge0 hc0(1) hi mult_nonneg_nonneg by (by100 blast)
                moreover have "?s * cA i \<ge> 0"
                  using hs_ge0 hcA(1) hi mult_nonneg_nonneg by (by100 blast)
                moreover have "?tp * cB i \<ge> 0"
                  using htp_ge0 hcB(1) hi mult_nonneg_nonneg by (by100 blast)
                ultimately show "cc i \<ge> 0" unfolding cc_def by linarith
              qed
              \<comment> \<open>Sum = 1 via sum.distrib + sum\\_distrib\\_left + substitution.\<close>
              have hcc_sum: "(\<Sum>i<?n. cc i) = 1"
              proof -
                have "(\<Sum>i<?n. cc i) = (\<Sum>i<?n. (1-?s-?tp) * c0 i + ?s * cA i + ?tp * cB i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp) * c0 i + ?s * cA i) + (\<Sum>i<?n. ?tp * cB i)"
                  by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp) * c0 i + ?s * cA i)
                  = (\<Sum>i<?n. (1-?s-?tp) * c0 i) + (\<Sum>i<?n. ?s * cA i)" by (rule sum.distrib)
                finally have hd: "(\<Sum>i<?n. cc i) =
                  (\<Sum>i<?n. (1-?s-?tp) * c0 i) + (\<Sum>i<?n. ?s * cA i) + (\<Sum>i<?n. ?tp * cB i)" by linarith
                have "(\<Sum>i<?n. (1-?s-?tp) * c0 i) = (1-?s-?tp) * (\<Sum>i<?n. c0 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s * cA i) = ?s * (\<Sum>i<?n. cA i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp * cB i) = ?tp * (\<Sum>i<?n. cB i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have hd2: "(\<Sum>i<?n. cc i) =
                  (1-?s-?tp)*(\<Sum>i<?n. c0 i) + ?s*(\<Sum>i<?n. cA i) + ?tp*(\<Sum>i<?n. cB i)"
                  using hd by linarith
                have "(1-?s-?tp)*(\<Sum>i<?n. c0 i) = (1-?s-?tp)"
                  by (simp only: hc0(2) mult_1_right)
                moreover have "?s*(\<Sum>i<?n. cA i) = ?s"
                  by (simp only: hcA(2) mult_1_right)
                moreover have "?tp*(\<Sum>i<?n. cB i) = ?tp"
                  by (simp only: hcB(2) mult_1_right)
                ultimately show ?thesis using hd2 by linarith
              qed
              \<comment> \<open>Coordinate sums via same technique.\<close>
              have hcc_x: "fst (phi_L x) = (\<Sum>i<?n. cc i * vx2 i)"
              proof -
                have "(\<Sum>i<?n. cc i * vx2 i)
                  = (\<Sum>i<?n. ((1-?s-?tp)*c0 i + ?s*cA i + ?tp*cB i) * vx2 i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i) + ?s*(cA i*vx2 i) + ?tp*(cB i*vx2 i))"
                  by (rule sum.cong, simp, by100 algebra)
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i) + ?s*(cA i*vx2 i))
                  + (\<Sum>i<?n. ?tp*(cB i*vx2 i))" by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i) + ?s*(cA i*vx2 i))
                  = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i)) + (\<Sum>i<?n. ?s*(cA i*vx2 i))"
                  by (rule sum.distrib)
                finally have hxd: "(\<Sum>i<?n. cc i * vx2 i)
                  = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i)) + (\<Sum>i<?n. ?s*(cA i*vx2 i))
                  + (\<Sum>i<?n. ?tp*(cB i*vx2 i))" by linarith
                have "(\<Sum>i<?n. (1-?s-?tp)*(c0 i*vx2 i)) = (1-?s-?tp)*(\<Sum>i<?n. c0 i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s*(cA i*vx2 i)) = ?s*(\<Sum>i<?n. cA i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp*(cB i*vx2 i)) = ?tp*(\<Sum>i<?n. cB i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have "(\<Sum>i<?n. cc i * vx2 i)
                  = (1-?s-?tp)*(\<Sum>i<?n. c0 i*vx2 i) + ?s*(\<Sum>i<?n. cA i*vx2 i) + ?tp*(\<Sum>i<?n. cB i*vx2 i)"
                  using hxd by linarith
                also have "\<dots> = (1-?s-?tp)*vx2 0 + ?s*vx2(?k+1-?j) + ?tp*vx2(?k-?j)"
                  by (simp only: hc0(3)[symmetric] hcA(3)[symmetric] hcB(3)[symmetric])
                finally show ?thesis using hphi_eq by (simp only: fst_conv snd_conv)
              qed
              have hcc_y: "snd (phi_L x) = (\<Sum>i<?n. cc i * vy2 i)"
              proof -
                have "(\<Sum>i<?n. cc i * vy2 i)
                  = (\<Sum>i<?n. ((1-?s-?tp)*c0 i + ?s*cA i + ?tp*cB i) * vy2 i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i) + ?s*(cA i*vy2 i) + ?tp*(cB i*vy2 i))"
                  by (rule sum.cong, simp, by100 algebra)
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i) + ?s*(cA i*vy2 i))
                  + (\<Sum>i<?n. ?tp*(cB i*vy2 i))" by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i) + ?s*(cA i*vy2 i))
                  = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i)) + (\<Sum>i<?n. ?s*(cA i*vy2 i))"
                  by (rule sum.distrib)
                finally have hyd: "(\<Sum>i<?n. cc i * vy2 i)
                  = (\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i)) + (\<Sum>i<?n. ?s*(cA i*vy2 i))
                  + (\<Sum>i<?n. ?tp*(cB i*vy2 i))" by linarith
                have "(\<Sum>i<?n. (1-?s-?tp)*(c0 i*vy2 i)) = (1-?s-?tp)*(\<Sum>i<?n. c0 i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s*(cA i*vy2 i)) = ?s*(\<Sum>i<?n. cA i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp*(cB i*vy2 i)) = ?tp*(\<Sum>i<?n. cB i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have "(\<Sum>i<?n. cc i * vy2 i)
                  = (1-?s-?tp)*(\<Sum>i<?n. c0 i*vy2 i) + ?s*(\<Sum>i<?n. cA i*vy2 i) + ?tp*(\<Sum>i<?n. cB i*vy2 i)"
                  using hyd by linarith
                also have "\<dots> = (1-?s-?tp)*vy2 0 + ?s*vy2(?k+1-?j) + ?tp*vy2(?k-?j)"
                  by (simp only: hc0(4)[symmetric] hcA(4)[symmetric] hcB(4)[symmetric])
                finally show ?thesis using hphi_eq by (simp only: fst_conv snd_conv)
              qed
              \<comment> \<open>Show P2 membership using hC5\\_2 (which uses ?n, matching our sums).\<close>
              have "\<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> fst (phi_L x) = (\<Sum>i<?n. coeffs i * vx2 i)
                \<and> snd (phi_L x) = (\<Sum>i<?n. coeffs i * vy2 i)"
                apply (rule exI[of _ cc])
                using hcc_nn hcc_sum hcc_x hcc_y by (by100 blast)
              thus ?thesis unfolding hC5_2 by (by5000 auto)
            qed
          qed
          have hphi_R_in_P2: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x > 0 \<Longrightarrow> phi_R x \<in> P2"
          proof -
            fix x assume hx: "x \<in> P2" and hcd: "cross_diag x > 0"
            \<comment> \<open>Step 1: cross\\_k(x) \\<ge> 0 from hcd.\<close>
            have hcrossk_ge: "(vx2 ?k - vx2 0)*(snd x - vy2 0) - (vy2 ?k - vy2 0)*(fst x - vx2 0) \<ge> 0"
              using hcd unfolding cross_diag_def by linarith
            \<comment> \<open>cross\\_{n-1}(x) \\<le> 0: cross(v\\_{n-1}-v\\_0, v\\_l-v\\_0) \\<le> 0 at all vertices.\<close>
            have hcrossnm1_le: "(vx2(?n-1) - vx2 0)*(snd x - vy2 0) - (vy2(?n-1) - vy2 0)*(fst x - vx2 0) \<le> 0"
            proof -
              let ?A = "(vy2 0 - vy2(?n-1))*vx2 0 - (vx2 0 - vx2(?n-1))*vy2 0"
              let ?B = "-(vy2 0 - vy2(?n-1))" let ?C = "vx2 0 - vx2(?n-1)"
              have hrewrite: "-((vx2(?n-1) - vx2 0)*(snd x - vy2 0) - (vy2(?n-1) - vy2 0)*(fst x - vx2 0))
                = ?A + ?B * fst x + ?C * snd x" by (by100 algebra)
              have "\<forall>l<?n. ?A + ?B * vx2 l + ?C * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval: "?A + ?B * vx2 l + ?C * vy2 l =
                  -((vx2(?n-1) - vx2 0)*(vy2 l - vy2 0) - (vy2(?n-1) - vy2 0)*(vx2 l - vx2 0))"
                  by (by100 algebra)
                show "?A + ?B * vx2 l + ?C * vy2 l \<ge> 0"
                proof (cases "l = 0")
                  case True thus ?thesis unfolding hval by (by100 simp)
                next
                  case False hence hl1: "1 \<le> l" by (by100 linarith)
                  show ?thesis
                  proof (cases "l = ?n - 1")
                    case True thus ?thesis unfolding hval by (by100 simp)
                  next
                    case False2: False hence hl_lt: "l < ?n - 1" using hl by (by100 linarith)
                    have hnm1_lt: "?n - 1 < ?n" using hn_ge3 by (by100 linarith)
                    from hfan_det_0[rule_format, OF hl hnm1_lt hl1 hl_lt]
                    have hpos: "(vx2 l - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2 l - vy2 0)*(vx2(?n-1) - vx2 0) > 0" .
                    have hanti: "(vx2(?n-1) - vx2 0)*(vy2 l - vy2 0) - (vy2(?n-1) - vy2 0)*(vx2 l - vx2 0) =
                      -((vx2 l - vx2 0)*(vy2(?n-1) - vy2 0) - (vy2 l - vy2 0)*(vx2(?n-1) - vx2 0))"
                      by (by100 algebra)
                    show ?thesis unfolding hval using hpos hanti by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this] show ?thesis using hrewrite by linarith
            qed
            \<comment> \<open>Step 2: Sector existence via discrete IVT (k \\<le> j < n-1).\<close>
            let ?PR = "\<lambda>j. ?k \<le> j \<and> j < ?n - 1 \<and>
              (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc j) - vy2 0)*(fst x - vx2 0) \<le> 0"
            have hex: "\<exists>j. ?PR j"
            proof -
              define f where "f j = (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0)" for j
              have hfk: "f ?k \<ge> 0" using hcrossk_ge unfolding f_def .
              have hfnm1: "f (?n - 1) \<le> 0" using hcrossnm1_le unfolding f_def .
              have hk_lt_nm1_local: "?k < ?n - 1" using hk_lt_nm1 by (by100 linarith)
              have hivt: "\<forall>m. ?k \<le> m \<longrightarrow> m < ?n - 1 \<longrightarrow> f m \<ge> 0 \<longrightarrow>
                  (\<exists>j. m \<le> j \<and> j < ?n - 1 \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0)"
              proof (intro allI impI)
                fix m assume hm1: "?k \<le> m" and hmk: "m < ?n - 1" and hfm: "f m \<ge> 0"
                show "\<exists>j. m \<le> j \<and> j < ?n - 1 \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0"
                  using hmk hfm
                proof (induction "?n - 1 - m" arbitrary: m)
                  case 0 thus ?case by linarith
                next
                  case (Suc d)
                  show ?case
                  proof (cases "f (Suc m) \<le> 0")
                    case True
                    show ?thesis
                      apply (rule exI[of _ m])
                      using True Suc.prems by (by100 blast)
                  next
                    case False hence hfSm_pos: "f (Suc m) > 0" by linarith
                    hence hfSm: "f (Suc m) \<ge> 0" by linarith
                    have "Suc m \<le> ?n - 1" using Suc.prems Suc.hyps by linarith
                    moreover have "Suc m \<noteq> ?n - 1"
                    proof
                      assume "Suc m = ?n - 1"
                      hence "f (Suc m) \<le> 0" using hfnm1 by (by100 simp)
                      with hfSm_pos show False by linarith
                    qed
                    ultimately have "Suc m < ?n - 1" by linarith
                    have "d = ?n - 1 - Suc m" using Suc.hyps by linarith
                    from Suc.hyps(1)[OF \<open>d = ?n - 1 - Suc m\<close> \<open>Suc m < ?n - 1\<close> hfSm]
                    obtain j where hj: "Suc m \<le> j" "j < ?n - 1" "f j \<ge> 0" "f (Suc j) \<le> 0" by blast
                    hence "m \<le> j" by linarith
                    with hj show ?thesis by (by100 blast)
                  qed
                qed
              qed
              from hivt[rule_format, OF le_refl hk_lt_nm1_local hfk]
              obtain j where hj: "?k \<le> j" "j < ?n - 1" "f j \<ge> 0" "f (Suc j) \<le> 0" by (by100 blast)
              thus ?thesis unfolding f_def by (by100 blast)
            qed
            from LeastI_ex[OF this]
            have hPR: "?PR (LEAST j. ?PR j)" .
            let ?j = "LEAST j. ?PR j"
            have hjk: "?k \<le> ?j" using hPR by (by100 blast)
            have hjnm1: "?j < ?n - 1" using hPR by (by100 blast)
            have hcross_ge: "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0) \<ge> 0"
              using hPR by (by100 blast)
            have hcross_le: "(vx2(Suc ?j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) \<le> 0"
              using hPR by (by100 blast)
            \<comment> \<open>Step 3: det > 0, Cramer non-negativity.\<close>
            have hk_lt_n_local: "?k < ?n" using hk_lt_nm1 by (by100 linarith)
            have hj_lt: "?j < ?n" using hjnm1 by (by100 linarith)
            have hj1: "1 \<le> ?j" using hjk hk_ge2 by (by100 linarith)
            have hsj_lt: "Suc ?j < ?n" using hjnm1 by (by100 linarith)
            let ?det = "(vx2 ?j - vx2 0) * (vy2(Suc ?j) - vy2 0) - (vy2 ?j - vy2 0) * (vx2(Suc ?j) - vx2 0)"
            have hdet_pos: "?det > 0"
              using hfan_det_0[rule_format, OF hj_lt hsj_lt hj1 lessI] .
            let ?s_num = "(vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) - (vx2(Suc ?j) - vx2 0)*(snd x - vy2 0)"
            let ?tp_num = "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0)"
            let ?s = "?s_num / ?det"
            let ?tp = "?tp_num / ?det"
            have hs_num_nn: "?s_num \<ge> 0" using hcross_le by linarith
            have htp_num_nn: "?tp_num \<ge> 0" using hcross_ge by linarith
            have hs_ge0: "?s \<ge> 0" using hs_num_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            have htp_ge0: "?tp \<ge> 0" using htp_num_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            \<comment> \<open>1-s-tp \\<ge> 0 via C11 affine argument.\<close>
            have h1stp_ge0: "1 - ?s - ?tp \<ge> 0"
            proof -
              have hnum_eq: "?det - ?s_num - ?tp_num =
                (vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)"
                by (by100 algebra)
              let ?Aj = "vx2 ?j * vy2(Suc ?j) - vy2 ?j * vx2(Suc ?j)"
              let ?Bj = "vy2 ?j - vy2(Suc ?j)" let ?Cj = "vx2(Suc ?j) - vx2 ?j"
              have hF_form: "(vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)
                = ?Aj + ?Bj * fst x + ?Cj * snd x" by (by100 algebra)
              have "\<forall>l<?n. ?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval: "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                  (vx2 ?j - vx2 l)*(vy2(Suc ?j) - vy2 l) - (vy2 ?j - vy2 l)*(vx2(Suc ?j) - vx2 l)"
                  by (by100 algebra)
                show "?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
                proof (cases "l = ?j")
                  case True thus ?thesis unfolding hval by (by100 simp)
                next
                  case False show ?thesis
                  proof (cases "l = Suc ?j")
                    case True thus ?thesis unfolding hval by (by100 simp)
                  next
                    case False2: False
                    have hsj_mod: "Suc ?j mod ?n = Suc ?j" using hsj_lt by (by100 simp)
                    have hl_ne_sj_mod: "l \<noteq> Suc ?j mod ?n" using False2 hsj_mod by (by100 simp)
                    from hC11_2[rule_format, OF hj_lt hl False hl_ne_sj_mod]
                    have "(vx2 l - vx2 ?j) * (vy2(Suc ?j mod ?n) - vy2 ?j)
                      - (vy2 l - vy2 ?j) * (vx2(Suc ?j mod ?n) - vx2 ?j) < 0" .
                    hence "(vx2 l - vx2 ?j) * (vy2(Suc ?j) - vy2 ?j)
                      - (vy2 l - vy2 ?j) * (vx2(Suc ?j) - vx2 ?j) < 0"
                      using hsj_mod by (by100 simp)
                    moreover have "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                      -((vx2 l - vx2 ?j) * (vy2(Suc ?j) - vy2 ?j) - (vy2 l - vy2 ?j) * (vx2(Suc ?j) - vx2 ?j))"
                      unfolding hval by (by100 algebra)
                    ultimately show ?thesis by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this]
              have hF_ge0: "?Aj + ?Bj * fst x + ?Cj * snd x \<ge> 0" .
              hence hnum_ge0: "?det - ?s_num - ?tp_num \<ge> 0" using hnum_eq hF_form by linarith
              have hne: "?det \<noteq> 0" using hdet_pos by linarith
              have hs_cancel: "?s * ?det = ?s_num" using hne by (by100 simp)
              have htp_cancel: "?tp * ?det = ?tp_num" using hne by (by100 simp)
              have "(1 - ?s - ?tp) * ?det = ?det - ?s * ?det - ?tp * ?det" by (by100 algebra)
              hence "(1 - ?s - ?tp) * ?det = ?det - ?s_num - ?tp_num"
                using hs_cancel htp_cancel by linarith
              hence h_prod_nn: "(1 - ?s - ?tp) * ?det \<ge> 0" using hnum_ge0 by linarith
              show ?thesis
              proof (rule ccontr)
                assume "\<not> (1 - ?s - ?tp \<ge> 0)"
                hence "1 - ?s - ?tp < 0" by linarith
                hence "(1 - ?s - ?tp) * ?det < 0" using hdet_pos
                  using mult_neg_pos by (by100 blast)
                with h_prod_nn show False by linarith
              qed
            qed
            \<comment> \<open>Step 4: phi\\_R(x) unfolding and vertex indices.\<close>
            have hphi_eq: "phi_R x = ((1-?s-?tp)*vx2 ?k + ?s*vx2(Suc ?j) + ?tp*vx2(Suc(Suc ?j) mod ?n),
                                       (1-?s-?tp)*vy2 ?k + ?s*vy2(Suc ?j) + ?tp*vy2(Suc(Suc ?j) mod ?n))"
              unfolding phi_R_def Let_def by (by100 simp)
            have hA_lt: "Suc ?j < ?n" using hsj_lt .
            have hB_lt: "Suc(Suc ?j) mod ?n < ?n" by (by100 simp)
            \<comment> \<open>Step 5: P2 membership via convex combination of vertex memberships.\<close>
            show "phi_R x \<in> P2"
            proof -
              have hvK: "(vx2 ?k, vy2 ?k) \<in> P2" using hv2_in hk_lt_n_local by (by100 blast)
              have hvA: "(vx2(Suc ?j), vy2(Suc ?j)) \<in> P2" using hv2_in hA_lt by (by100 blast)
              have hvB: "(vx2(Suc(Suc ?j) mod ?n), vy2(Suc(Suc ?j) mod ?n)) \<in> P2"
                using hv2_in hB_lt by (by100 blast)
              from hvK[unfolded hC5_2] obtain cK where
                hcK: "\<forall>i<?n. cK i \<ge> 0" "(\<Sum>i<?n. cK i) = 1"
                     "vx2 ?k = (\<Sum>i<?n. cK i * vx2 i)" "vy2 ?k = (\<Sum>i<?n. cK i * vy2 i)"
                by (by5000 auto)
              from hvA[unfolded hC5_2] obtain cA where
                hcA: "\<forall>i<?n. cA i \<ge> 0" "(\<Sum>i<?n. cA i) = 1"
                     "vx2(Suc ?j) = (\<Sum>i<?n. cA i * vx2 i)" "vy2(Suc ?j) = (\<Sum>i<?n. cA i * vy2 i)"
                by (by5000 auto)
              from hvB[unfolded hC5_2] obtain cB where
                hcB: "\<forall>i<?n. cB i \<ge> 0" "(\<Sum>i<?n. cB i) = 1"
                     "vx2(Suc(Suc ?j) mod ?n) = (\<Sum>i<?n. cB i * vx2 i)"
                     "vy2(Suc(Suc ?j) mod ?n) = (\<Sum>i<?n. cB i * vy2 i)"
                by (by5000 auto)
              define cc where "cc i = (1-?s-?tp) * cK i + ?s * cA i + ?tp * cB i" for i
              have hcc_nn: "\<forall>i<?n. cc i \<ge> 0"
              proof (intro allI impI)
                fix i :: nat assume hi: "i < ?n"
                have "(1-?s-?tp) * cK i \<ge> 0"
                  using h1stp_ge0 hcK(1) hi mult_nonneg_nonneg by (by100 blast)
                moreover have "?s * cA i \<ge> 0"
                  using hs_ge0 hcA(1) hi mult_nonneg_nonneg by (by100 blast)
                moreover have "?tp * cB i \<ge> 0"
                  using htp_ge0 hcB(1) hi mult_nonneg_nonneg by (by100 blast)
                ultimately show "cc i \<ge> 0" unfolding cc_def by linarith
              qed
              have hcc_sum: "(\<Sum>i<?n. cc i) = 1"
              proof -
                have "(\<Sum>i<?n. cc i) = (\<Sum>i<?n. (1-?s-?tp) * cK i + ?s * cA i + ?tp * cB i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp) * cK i + ?s * cA i) + (\<Sum>i<?n. ?tp * cB i)"
                  by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp) * cK i + ?s * cA i)
                  = (\<Sum>i<?n. (1-?s-?tp) * cK i) + (\<Sum>i<?n. ?s * cA i)" by (rule sum.distrib)
                finally have hd: "(\<Sum>i<?n. cc i) =
                  (\<Sum>i<?n. (1-?s-?tp) * cK i) + (\<Sum>i<?n. ?s * cA i) + (\<Sum>i<?n. ?tp * cB i)" by linarith
                have "(\<Sum>i<?n. (1-?s-?tp) * cK i) = (1-?s-?tp) * (\<Sum>i<?n. cK i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s * cA i) = ?s * (\<Sum>i<?n. cA i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp * cB i) = ?tp * (\<Sum>i<?n. cB i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have hd2: "(\<Sum>i<?n. cc i) =
                  (1-?s-?tp)*(\<Sum>i<?n. cK i) + ?s*(\<Sum>i<?n. cA i) + ?tp*(\<Sum>i<?n. cB i)"
                  using hd by linarith
                have "(1-?s-?tp)*(\<Sum>i<?n. cK i) = (1-?s-?tp)" by (simp only: hcK(2) mult_1_right)
                moreover have "?s*(\<Sum>i<?n. cA i) = ?s" by (simp only: hcA(2) mult_1_right)
                moreover have "?tp*(\<Sum>i<?n. cB i) = ?tp" by (simp only: hcB(2) mult_1_right)
                ultimately show ?thesis using hd2 by linarith
              qed
              have hcc_x: "fst (phi_R x) = (\<Sum>i<?n. cc i * vx2 i)"
              proof -
                have "(\<Sum>i<?n. cc i * vx2 i) = (\<Sum>i<?n. ((1-?s-?tp)*cK i + ?s*cA i + ?tp*cB i) * vx2 i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i) + ?s*(cA i*vx2 i) + ?tp*(cB i*vx2 i))"
                  by (rule sum.cong, simp, by100 algebra)
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i) + ?s*(cA i*vx2 i)) + (\<Sum>i<?n. ?tp*(cB i*vx2 i))"
                  by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i) + ?s*(cA i*vx2 i))
                  = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i)) + (\<Sum>i<?n. ?s*(cA i*vx2 i))" by (rule sum.distrib)
                finally have hxd: "(\<Sum>i<?n. cc i * vx2 i) =
                  (\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i)) + (\<Sum>i<?n. ?s*(cA i*vx2 i)) + (\<Sum>i<?n. ?tp*(cB i*vx2 i))"
                  by linarith
                have "(\<Sum>i<?n. (1-?s-?tp)*(cK i*vx2 i)) = (1-?s-?tp)*(\<Sum>i<?n. cK i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s*(cA i*vx2 i)) = ?s*(\<Sum>i<?n. cA i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp*(cB i*vx2 i)) = ?tp*(\<Sum>i<?n. cB i*vx2 i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have "(\<Sum>i<?n. cc i * vx2 i) =
                  (1-?s-?tp)*(\<Sum>i<?n. cK i*vx2 i) + ?s*(\<Sum>i<?n. cA i*vx2 i) + ?tp*(\<Sum>i<?n. cB i*vx2 i)"
                  using hxd by linarith
                also have "\<dots> = (1-?s-?tp)*vx2 ?k + ?s*vx2(Suc ?j) + ?tp*vx2(Suc(Suc ?j) mod ?n)"
                  by (simp only: hcK(3)[symmetric] hcA(3)[symmetric] hcB(3)[symmetric])
                finally show ?thesis using hphi_eq by (simp only: fst_conv snd_conv)
              qed
              have hcc_y: "snd (phi_R x) = (\<Sum>i<?n. cc i * vy2 i)"
              proof -
                have "(\<Sum>i<?n. cc i * vy2 i) = (\<Sum>i<?n. ((1-?s-?tp)*cK i + ?s*cA i + ?tp*cB i) * vy2 i)"
                  unfolding cc_def ..
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i) + ?s*(cA i*vy2 i) + ?tp*(cB i*vy2 i))"
                  by (rule sum.cong, simp, by100 algebra)
                also have "\<dots> = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i) + ?s*(cA i*vy2 i)) + (\<Sum>i<?n. ?tp*(cB i*vy2 i))"
                  by (rule sum.distrib)
                also have "(\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i) + ?s*(cA i*vy2 i))
                  = (\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i)) + (\<Sum>i<?n. ?s*(cA i*vy2 i))" by (rule sum.distrib)
                finally have hyd: "(\<Sum>i<?n. cc i * vy2 i) =
                  (\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i)) + (\<Sum>i<?n. ?s*(cA i*vy2 i)) + (\<Sum>i<?n. ?tp*(cB i*vy2 i))"
                  by linarith
                have "(\<Sum>i<?n. (1-?s-?tp)*(cK i*vy2 i)) = (1-?s-?tp)*(\<Sum>i<?n. cK i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?s*(cA i*vy2 i)) = ?s*(\<Sum>i<?n. cA i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                moreover have "(\<Sum>i<?n. ?tp*(cB i*vy2 i)) = ?tp*(\<Sum>i<?n. cB i*vy2 i)"
                  by (rule sum_distrib_left[symmetric])
                ultimately have "(\<Sum>i<?n. cc i * vy2 i) =
                  (1-?s-?tp)*(\<Sum>i<?n. cK i*vy2 i) + ?s*(\<Sum>i<?n. cA i*vy2 i) + ?tp*(\<Sum>i<?n. cB i*vy2 i)"
                  using hyd by linarith
                also have "\<dots> = (1-?s-?tp)*vy2 ?k + ?s*vy2(Suc ?j) + ?tp*vy2(Suc(Suc ?j) mod ?n)"
                  by (simp only: hcK(4)[symmetric] hcA(4)[symmetric] hcB(4)[symmetric])
                finally show ?thesis using hphi_eq by (simp only: fst_conv snd_conv)
              qed
              have "\<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> fst (phi_R x) = (\<Sum>i<?n. coeffs i * vx2 i)
                \<and> snd (phi_R x) = (\<Sum>i<?n. coeffs i * vy2 i)"
                apply (rule exI[of _ cc])
                using hcc_nn hcc_sum hcc_x hcc_y by (by100 blast)
              thus ?thesis unfolding hC5_2 by (by5000 auto)
            qed
          qed
          \<comment> \<open>SHARED: phi\\_L Cramer decomposition. For any x \\<in> P2 with cross\\_diag \\<le> 0,
             phi\\_L(x) decomposes as (1-s-tp)*v\\_0 + s*v\\_{k+1-j} + tp*v\\_{k-j} with s,tp,1-s-tp \\<ge> 0.
             Also: s=0 \\<longleftrightarrow> cross\\_{j+1}(x)=0, tp=0 \\<longleftrightarrow> cross\\_j(x)=0, 1-s-tp=0 \\<longleftrightarrow> F(x)=0.\<close>
          have hphi_L_decomp: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x \<le> 0 \<Longrightarrow>
              \<exists>j s tp. 1 \<le> j \<and> j < ?k \<and> s \<ge> 0 \<and> tp \<ge> 0 \<and> 1 - s - tp \<ge> 0 \<and>
              phi_L x = ((1-s-tp)*vx2 0 + s*vx2(?k+1-j) + tp*vx2(?k-j),
                         (1-s-tp)*vy2 0 + s*vy2(?k+1-j) + tp*vy2(?k-j)) \<and>
              (s = 0 \<longrightarrow> (vx2(Suc j) - vx2 0)*(snd x - vy2 0) = (vy2(Suc j) - vy2 0)*(fst x - vx2 0)) \<and>
              (tp = 0 \<longrightarrow> (vx2 j - vx2 0)*(snd x - vy2 0) = (vy2 j - vy2 0)*(fst x - vx2 0)) \<and>
              (1 - s - tp = 0 \<longrightarrow> (\<exists>t'\<in>I_set. x = ((1-t')*vx2 j + t'*vx2(Suc j),
                                                     (1-t')*vy2 j + t'*vy2(Suc j))))"
          proof -
            fix x assume hx: "x \<in> P2" and hcd: "cross_diag x \<le> 0"
            \<comment> \<open>Sector existence (same as phi\\_L\\_in\\_P2, using haffine\\_nonneg + IVT).\<close>
            have hcross1_ge_d: "(vx2 1 - vx2 0)*(snd x - vy2 0) - (vy2 1 - vy2 0)*(fst x - vx2 0) \<ge> 0"
            proof -
              let ?Ad = "(vy2 1 - vy2 0)*vx2 0 - (vx2 1 - vx2 0)*vy2 0"
              let ?Bd = "-(vy2 1 - vy2 0)" let ?Cd = "vx2 1 - vx2 0"
              have hrew: "(vx2 1 - vx2 0)*(snd x - vy2 0) - (vy2 1 - vy2 0)*(fst x - vx2 0)
                = ?Ad + ?Bd * fst x + ?Cd * snd x" by (by100 algebra)
              have hval_d1: "\<And>l. ?Ad + ?Bd * vx2 l + ?Cd * vy2 l =
                (vx2 1 - vx2 0)*(vy2 l - vy2 0) - (vy2 1 - vy2 0)*(vx2 l - vx2 0)"
                by (by100 algebra)
              have "\<forall>l<?n. ?Ad + ?Bd * vx2 l + ?Cd * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                show "?Ad + ?Bd * vx2 l + ?Cd * vy2 l \<ge> 0"
                proof (cases "l = 0")
                  case True thus ?thesis unfolding hval_d1 by (by100 simp)
                next
                  case hli: False show ?thesis
                  proof (cases "l = 1")
                    case True thus ?thesis unfolding hval_d1 by (by100 simp)
                  next
                    case False hence "1 < l" using hli by (by100 linarith)
                    have "(1::nat) < ?n" using hn_ge3 by (by100 linarith)
                    from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> hl le_refl \<open>1 < l\<close>]
                    show ?thesis unfolding hval_d1 by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this] show ?thesis unfolding hrew .
            qed
            have hcrossk_le_d: "(vx2 ?k - vx2 0)*(snd x - vy2 0) - (vy2 ?k - vy2 0)*(fst x - vx2 0) \<le> 0"
              using hcd unfolding cross_diag_def by (by100 simp)
            have hex_d: "\<exists>j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc j) - vy2 0)*(fst x - vx2 0) \<le> 0"
            proof -
              define f where "f j = (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0)" for j
              have hf1: "f 1 \<ge> 0" using hcross1_ge_d unfolding f_def .
              have hfk: "f ?k \<le> 0" using hcrossk_le_d unfolding f_def .
              have h1ltk: "1 < ?k" using hk_ge2 by linarith
              have "\<forall>m. 1 \<le> m \<longrightarrow> m < ?k \<longrightarrow> f m \<ge> 0 \<longrightarrow>
                  (\<exists>j. m \<le> j \<and> j < ?k \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0)"
              proof (intro allI impI)
                fix m assume "1 \<le> m" and hmk: "m < ?k" and hfm: "f m \<ge> 0"
                show "\<exists>j. m \<le> j \<and> j < ?k \<and> f j \<ge> 0 \<and> f (Suc j) \<le> 0"
                  using hmk hfm
                proof (induction "?k - m" arbitrary: m)
                  case 0 thus ?case by linarith
                next
                  case (Suc d)
                  show ?case
                  proof (cases "f (Suc m) \<le> 0")
                    case True show ?thesis
                      apply (rule exI[of _ m]) using True Suc.prems by (by100 blast)
                  next
                    case False hence "f (Suc m) > 0" by linarith
                    hence "f (Suc m) \<ge> 0" by linarith
                    have "Suc m \<le> ?k" using Suc.prems Suc.hyps by linarith
                    moreover have "Suc m \<noteq> ?k"
                    proof assume "Suc m = ?k" hence "f (Suc m) \<le> 0" using hfk by (by100 simp)
                      with \<open>f (Suc m) > 0\<close> show False by linarith qed
                    ultimately have "Suc m < ?k" by linarith
                    have "d = ?k - Suc m" using Suc.hyps by linarith
                    from Suc.hyps(1)[OF this \<open>Suc m < ?k\<close> \<open>f (Suc m) \<ge> 0\<close>]
                    obtain j where hj: "Suc m \<le> j" "j < ?k" "f j \<ge> 0" "f (Suc j) \<le> 0" by blast
                    hence "m \<le> j" by linarith
                    with hj show ?thesis by (by100 blast)
                  qed
                qed
              qed
              from this[rule_format, OF le_refl h1ltk hf1]
              obtain j where "1 \<le> j" "j < ?k" "f j \<ge> 0" "f (Suc j) \<le> 0" by (by100 blast)
              thus ?thesis unfolding f_def by (by100 blast)
            qed
            then obtain jj where hjj: "1 \<le> jj" "jj < ?k"
              "(vx2 jj - vx2 0)*(snd x - vy2 0) - (vy2 jj - vy2 0)*(fst x - vx2 0) \<ge> 0"
              "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) - (vy2(Suc jj) - vy2 0)*(fst x - vx2 0) \<le> 0"
              by (by100 blast)
            \<comment> \<open>The LEAST sector has the same properties.\<close>
            let ?PL = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc j) - vy2 0)*(fst x - vx2 0) \<le> 0"
            from hex_d have "\<exists>j. ?PL j" by (by100 blast)
            from LeastI_ex[OF this] have hPL: "?PL (LEAST j. ?PL j)" .
            let ?j = "LEAST j. ?PL j"
            have hj1: "1 \<le> ?j" and hjk: "?j < ?k"
              and hcross_ge: "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0) \<ge> 0"
              and hcross_le: "(vx2(Suc ?j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) \<le> 0"
              using hPL by (by100 blast)+
            \<comment> \<open>Cramer coordinates.\<close>
            have hk_lt_n: "?k < ?n" using hk_lt_nm1 by (by100 linarith)
            have hj_lt: "?j < ?n" using hjk hk_lt_n by (by100 linarith)
            have hsj_lt: "Suc ?j < ?n" using hjk hk_lt_nm1 by (by100 linarith)
            let ?det = "(vx2 ?j - vx2 0)*(vy2(Suc ?j) - vy2 0) - (vy2 ?j - vy2 0)*(vx2(Suc ?j) - vx2 0)"
            have hdet_pos: "?det > 0"
              using hfan_det_0[rule_format, OF hj_lt hsj_lt hj1 lessI] .
            have hne: "?det \<noteq> 0" using hdet_pos by linarith
            let ?s_num = "(vy2(Suc ?j) - vy2 0)*(fst x - vx2 0) - (vx2(Suc ?j) - vx2 0)*(snd x - vy2 0)"
            let ?tp_num = "(vx2 ?j - vx2 0)*(snd x - vy2 0) - (vy2 ?j - vy2 0)*(fst x - vx2 0)"
            let ?s = "?s_num / ?det" let ?tp = "?tp_num / ?det"
            have hs_nn: "?s_num \<ge> 0" using hcross_le by linarith
            have htp_nn: "?tp_num \<ge> 0" using hcross_ge by linarith
            have hs_ge0: "?s \<ge> 0" using hs_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            have htp_ge0: "?tp \<ge> 0" using htp_nn hdet_pos divide_nonneg_nonneg by (by100 fastforce)
            \<comment> \<open>1-s-tp \\<ge> 0: from C11 affine argument (same as phi\\_L\\_in\\_P2).\<close>
            have h1stp_ge0: "1 - ?s - ?tp \<ge> 0"
            proof -
              let ?Aj = "vx2 ?j * vy2(Suc ?j) - vy2 ?j * vx2(Suc ?j)"
              let ?Bj = "vy2 ?j - vy2(Suc ?j)" let ?Cj = "vx2(Suc ?j) - vx2 ?j"
              have hnum_eq: "?det - ?s_num - ?tp_num =
                (vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)"
                by (by100 algebra)
              have hF_form: "\<And>px py :: real. (vx2 ?j - px)*(vy2(Suc ?j) - py) - (vy2 ?j - py)*(vx2(Suc ?j) - px)
                = ?Aj + ?Bj * px + ?Cj * py" by (by100 algebra)
              have "\<forall>l<?n. ?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval_j: "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                  (vx2 ?j - vx2 l)*(vy2(Suc ?j) - vy2 l) - (vy2 ?j - vy2 l)*(vx2(Suc ?j) - vx2 l)"
                  by (by100 algebra)
                show "?Aj + ?Bj * vx2 l + ?Cj * vy2 l \<ge> 0"
                proof (cases "l = ?j")
                  case True thus ?thesis unfolding hval_j by (by100 simp)
                next
                  case False show ?thesis
                  proof (cases "l = Suc ?j")
                    case True thus ?thesis unfolding hval_j by (by100 simp)
                  next
                    case False2: False
                    have hsj_mod: "Suc ?j mod ?n = Suc ?j" using hsj_lt by (by100 simp)
                    have hl_ne_sj_mod: "l \<noteq> Suc ?j mod ?n" using False2 hsj_mod by simp
                    from hC11_2[rule_format, OF hj_lt hl False hl_ne_sj_mod]
                    have "(vx2 l - vx2 ?j)*(vy2(Suc ?j) - vy2 ?j) - (vy2 l - vy2 ?j)*(vx2(Suc ?j) - vx2 ?j) < 0"
                      using hsj_mod by (by100 simp)
                    moreover have "?Aj + ?Bj * vx2 l + ?Cj * vy2 l =
                      -((vx2 l - vx2 ?j)*(vy2(Suc ?j) - vy2 ?j) - (vy2 l - vy2 ?j)*(vx2(Suc ?j) - vx2 ?j))"
                      unfolding hval_j by (by100 algebra)
                    ultimately show ?thesis by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hx this]
              have hF_ge0: "?Aj + ?Bj * fst x + ?Cj * snd x \<ge> 0" .
              have hF_eq_cross: "?Aj + ?Bj * fst x + ?Cj * snd x =
                (vx2 ?j - fst x)*(vy2(Suc ?j) - snd x) - (vy2 ?j - snd x)*(vx2(Suc ?j) - fst x)"
                using hF_form by simp
              hence hnum_ge0: "?det - ?s_num - ?tp_num \<ge> 0"
                using hF_ge0 hnum_eq by linarith
              have hs_cancel: "?s * ?det = ?s_num" using hne by (by100 simp)
              have htp_cancel: "?tp * ?det = ?tp_num" using hne by (by100 simp)
              have "(1 - ?s - ?tp) * ?det = ?det - ?s * ?det - ?tp * ?det" by (by100 algebra)
              hence "(1 - ?s - ?tp) * ?det = ?det - ?s_num - ?tp_num"
                using hs_cancel htp_cancel by linarith
              hence "(1 - ?s - ?tp) * ?det \<ge> 0" using hnum_ge0 by linarith
              show ?thesis
              proof (rule ccontr)
                assume "\<not> ?thesis" hence "1 - ?s - ?tp < 0" by linarith
                hence "(1 - ?s - ?tp) * ?det < 0" using hdet_pos mult_neg_pos by (by100 blast)
                with \<open>(1 - ?s - ?tp) * ?det \<ge> 0\<close> show False by linarith
              qed
            qed
            \<comment> \<open>phi\\_L equality from definition.\<close>
            have hphi_eq: "phi_L x = ((1-?s-?tp)*vx2 0 + ?s*vx2(?k+1-?j) + ?tp*vx2(?k-?j),
                                       (1-?s-?tp)*vy2 0 + ?s*vy2(?k+1-?j) + ?tp*vy2(?k-?j))"
              unfolding phi_L_def Let_def by (by100 simp)
            \<comment> \<open>Cramer connections.\<close>
            have hs0: "?s = 0 \<longrightarrow> (vx2(Suc ?j) - vx2 0)*(snd x - vy2 0) = (vy2(Suc ?j) - vy2 0)*(fst x - vx2 0)"
            proof
              assume "?s = 0" hence "?s_num = 0" using hne by (by100 simp)
              thus "(vx2(Suc ?j) - vx2 0)*(snd x - vy2 0) = (vy2(Suc ?j) - vy2 0)*(fst x - vx2 0)"
                by linarith
            qed
            have htp0: "?tp = 0 \<longrightarrow> (vx2 ?j - vx2 0)*(snd x - vy2 0) = (vy2 ?j - vy2 0)*(fst x - vx2 0)"
            proof
              assume "?tp = 0" hence "?tp_num = 0" using hne by (by100 simp)
              thus "(vx2 ?j - vx2 0)*(snd x - vy2 0) = (vy2 ?j - vy2 0)*(fst x - vx2 0)"
                by linarith
            qed
            have h1stp0: "1 - ?s - ?tp = 0 \<longrightarrow> (\<exists>t'\<in>I_set. x = ((1-t')*vx2 ?j + t'*vx2(Suc ?j),
                                                               (1-t')*vy2 ?j + t'*vy2(Suc ?j)))"
              sorry \<comment> \<open>F(x)=0 + x \\<in> P2 + C11 affine sum \\<to> x on edge j. Needs sum algebra.
                 KEY: cross(v\\_j-x,v\\_{j+1}-x)=0 + P2 barycentrics + C11 at each vertex
                 \\<to> only v\\_j, v\\_{j+1} have nonzero barycentrics \\<to> x on edge j.\<close>
            \<comment> \<open>Package as existential.\<close>
            show "\<exists>j s tp. 1 \<le> j \<and> j < ?k \<and> s \<ge> 0 \<and> tp \<ge> 0 \<and> 1 - s - tp \<ge> 0 \<and>
              phi_L x = ((1-s-tp)*vx2 0 + s*vx2(?k+1-j) + tp*vx2(?k-j),
                         (1-s-tp)*vy2 0 + s*vy2(?k+1-j) + tp*vy2(?k-j)) \<and>
              (s = 0 \<longrightarrow> (vx2(Suc j) - vx2 0)*(snd x - vy2 0) = (vy2(Suc j) - vy2 0)*(fst x - vx2 0)) \<and>
              (tp = 0 \<longrightarrow> (vx2 j - vx2 0)*(snd x - vy2 0) = (vy2 j - vy2 0)*(fst x - vx2 0)) \<and>
              (1 - s - tp = 0 \<longrightarrow> (\<exists>t'\<in>I_set. x = ((1-t')*vx2 j + t'*vx2(Suc j),
                                                     (1-t')*vy2 j + t'*vy2(Suc j))))"
              apply (rule exI[of _ ?j], rule exI[of _ ?s], rule exI[of _ ?tp])
              using hj1 hjk hs_ge0 htp_ge0 h1stp_ge0 hphi_eq hs0 htp0 h1stp0 by (by5000 blast)
          qed
          have hphi_L_int: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x < 0 \<Longrightarrow>
              (\<forall>i'<length ?w'. \<forall>t'\<in>I_set.
                x \<noteq> ((1-t')*vx2 i'+t'*vx2(Suc i' mod length ?w'),(1-t')*vy2 i'+t'*vy2(Suc i' mod length ?w'))) \<Longrightarrow>
              (\<forall>i<?n. \<forall>t\<in>I_set.
                phi_L x \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))"
          proof (intro allI impI ballI)
            fix x assume hx: "x \<in> P2" and hcdx: "cross_diag x < 0"
              and hint_x: "\<forall>i'<length ?w'. \<forall>t'\<in>I_set.
                x \<noteq> ((1-t')*vx2 i'+t'*vx2(Suc i' mod length ?w'),(1-t')*vy2 i'+t'*vy2(Suc i' mod length ?w'))"
            fix i :: nat and t :: real assume hi: "i < ?n" and ht: "t \<in> I_set"
            \<comment> \<open>C11 argument: phi\\_L(x) is a convex combination of v\\_0, v\\_A, v\\_B
               with at least 2 coefficients > 0 (from cross\\_diag < 0).
               Cross product linearity + C11 \\<to> phi\\_L(x) strictly on interior side of each edge.\<close>
            show "phi_L x \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
            proof
              assume heq: "phi_L x = ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
              \<comment> \<open>Get the phi\\_L decomposition: phi\\_L(x) = (1-s-tp)*v\\_0 + s*v\\_A + tp*v\\_B
                 with A = k+1-j, B = k-j from the LEAST sector.\<close>
              \<comment> \<open>Cross product at edge (i, i+1): cross(phi\\_L(x) - v\\_i, v\\_{i+1} - v\\_i) = 0
                 (phi\\_L(x) is on the line through v\\_i and v\\_{i+1}).
                 But by linearity and C11: this cross product is strictly < 0.
                 Contradiction.\<close>
              \<comment> \<open>The cross product of a point on the edge equals 0:\<close>
              have hfst: "fst (phi_L x) = (1-t)*vx2 i + t*vx2(Suc i mod ?n)" using heq by (by100 simp)
              have hsnd: "snd (phi_L x) = (1-t)*vy2 i + t*vy2(Suc i mod ?n)" using heq by (by100 simp)
              have hedge_cross: "(fst (phi_L x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_L x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = 0"
                using hfst hsnd by (by100 algebra)
              \<comment> \<open>phi\\_L(x) \\<in> P2, so use haffine\\_nonneg to show the cross product \\<le> 0 or \\<ge> 0.
                 Actually, C11 says all NON-ENDPOINT vertices are on the strict interior side.
                 So the cross product evaluated at phi\\_L(x) = affine combo of vertices gives < 0.\<close>
              \<comment> \<open>Use haffine\\_nonneg with F(p) = -(cross(p - v\\_i, v\\_{i+1} - v\\_i)):
                 F is affine, F(v\\_l) > 0 for l \\<noteq> i, Suc i mod n (from C11), F(v\\_i) = F(v\\_{Suc i}) = 0.
                 So F(phi\\_L(x)) \\<ge> 0, i.e., cross \\<le> 0. But we also need strict < 0.\<close>
              have hphi_in: "phi_L x \<in> P2" using hphi_L_in_P2[OF hx less_imp_le[OF hcdx]] .
              \<comment> \<open>Apply haffine\\_nonneg with NEGATED cross product to get \\<le> 0:\<close>
              let ?Ai = "vx2 i * vy2(Suc i mod ?n) - vy2 i * vx2(Suc i mod ?n)"
              let ?Bi = "vy2 i - vy2(Suc i mod ?n)" let ?Ci = "vx2(Suc i mod ?n) - vx2 i"
              have hF_form: "\<And>px py :: real. -(px - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                + (py - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = ?Ai + ?Bi * px + ?Ci * py"
                by (by100 algebra)
              have "\<forall>l<?n. ?Ai + ?Bi * vx2 l + ?Ci * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                have hval: "?Ai + ?Bi * vx2 l + ?Ci * vy2 l =
                  -((vx2 l - vx2 i) * (vy2(Suc i mod ?n) - vy2 i) - (vy2 l - vy2 i) * (vx2(Suc i mod ?n) - vx2 i))"
                  by (by100 algebra)
                show "?Ai + ?Bi * vx2 l + ?Ci * vy2 l \<ge> 0"
                proof (cases "l = i")
                  case True thus ?thesis unfolding hval by (by100 simp)
                next
                  case False show ?thesis
                  proof (cases "l = Suc i mod ?n")
                    case True thus ?thesis unfolding hval by (by100 simp)
                  next
                    case False2: False
                    from hC11_2[rule_format, OF hi hl False False2]
                    show ?thesis unfolding hval by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hphi_in this]
              have "?Ai + ?Bi * fst (phi_L x) + ?Ci * snd (phi_L x) \<ge> 0" .
              hence hedge_le: "(fst (phi_L x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_L x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) \<le> 0"
                using hF_form[of "fst (phi_L x)" "snd (phi_L x)"] by linarith
              \<comment> \<open>Combined: cross = 0 and cross \\<le> 0. Need strict < 0 for contradiction.
                 Strict follows from phi\\_L(x) having at least one vertex with strict C11 contribution.
                 This requires phi\\_L(x) not being v\\_i or v\\_{Suc i}, which follows from
                 cross\\_diag < 0 \\<to> x not a vertex \\<to> phi\\_L(x) not on edge endpoints.\<close>
              \<comment> \<open>From cross = 0: phi\\_L(x) is on the line through edge (i, i+1).
                 From cross \\<le> 0 (the other direction): phi\\_L(x) is on or below the edge.
                 Actually we have exactly cross = 0, which is consistent. But we need to show
                 phi\\_L(x) can't be on this edge at all. The haffine argument shows cross \\<le> 0
                 (and we have cross = 0). The issue is that haffine\\_nonneg gives \\<ge> 0 (not strict).
                 Need to strengthen to strict using the fact that at least some vertex contribution
                 is strictly positive.\<close>
              \<comment> \<open>For strict: need at least one l with coefficient > 0 AND C11(l,i) < 0.
                 phi\\_L(x) = convex combo of P2 vertices. At least one coefficient is > 0 (since
                 coefficients sum to 1). If that vertex l has l \\<noteq> i and l \\<noteq> Suc i mod n,
                 then C11(l,i) < 0 and coefficient > 0, giving strict contribution.\<close>
              \<comment> \<open>For now: use the fact that phi\\_L(x) is a specific convex combination of
                 v\\_0, v\\_A, v\\_B with at least 2 coefficients > 0 (from cross\\_diag < 0).\<close>
              \<comment> \<open>From hedge\\_cross = 0 + phi\\_L decomposition + C11:
                 At most 2 of {0, A, B} can be edge endpoints {i, Suc i}.
                 At least 1 has C11 < 0 and coefficient \\<ge> 0. For sum=0: coefficient=0.
                 Then trace back through Cramer to get contradiction.\<close>
              \<comment> \<open>phi\\_L(x) = (1-s-tp)*v\\_0 + s*v\\_A + tp*v\\_B. Cross product at edge = 0.
                 By linearity: (1-s-tp)*C11(0,i) + s*C11(A,i) + tp*C11(B,i) = 0.
                 All terms \\<le> 0 (coeff \\<ge> 0, C11 \\<le> 0). So each term = 0.
                 For non-endpoint vertex: C11 < 0, so coefficient = 0.\<close>
              \<comment> \<open>At least 1 of {0, A, B} \\<notin> {i, Suc i mod n} (3 distinct vs 2 endpoints).
                 Its coefficient = 0. Trace back: either cross\\_diag = 0 (contradicts < 0)
                 or x is on a target edge (contradicts hint\\_x).\<close>
              \<comment> \<open>Use phi\\_L decomposition: phi\\_L(x) = (1-s-tp)*v\\_0 + s*v\\_A + tp*v\\_B.\<close>
              from hphi_L_decomp[OF hx less_imp_le[OF hcdx]]
              obtain jj ss ttp where hjj1: "1 \<le> jj" and hjjk: "jj < ?k"
                and hss: "ss \<ge> 0" and htp2: "ttp \<ge> 0" and h1st2: "1 - ss - ttp \<ge> 0"
                and hphi_dec: "phi_L x = ((1-ss-ttp)*vx2 0 + ss*vx2(?k+1-jj) + ttp*vx2(?k-jj),
                                           (1-ss-ttp)*vy2 0 + ss*vy2(?k+1-jj) + ttp*vy2(?k-jj))"
                and hs0_imp: "ss = 0 \<longrightarrow> (vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)"
                and htp0_imp: "ttp = 0 \<longrightarrow> (vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)"
                and h1st0_imp: "1 - ss - ttp = 0 \<longrightarrow>
                  (\<exists>t'\<in>I_set. x = ((1-t')*vx2 jj + t'*vx2(Suc jj), (1-t')*vy2 jj + t'*vy2(Suc jj)))"
                by (by5000 blast)
              \<comment> \<open>Cross product linearity: expand hedge\\_cross using phi\\_L decomposition.\<close>
              let ?c0 = "(vx2 0 - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2 0 - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              let ?cA = "(vx2(?k+1-jj) - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2(?k+1-jj) - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              let ?cB = "(vx2(?k-jj) - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2(?k-jj) - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              have hlin: "(fst (phi_L x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_L x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = (1-ss-ttp)*?c0 + ss*?cA + ttp*?cB"
              proof -
                have hf: "fst (phi_L x) = (1-ss-ttp)*vx2 0 + ss*vx2(?k+1-jj) + ttp*vx2(?k-jj)"
                  using hphi_dec by (by100 simp)
                have hs: "snd (phi_L x) = (1-ss-ttp)*vy2 0 + ss*vy2(?k+1-jj) + ttp*vy2(?k-jj)"
                  using hphi_dec by (by100 simp)
                show ?thesis using hf hs by (by100 algebra)
              qed
              \<comment> \<open>From C11: ?c0, ?cA, ?cB \\<le> 0. Combined with hedge\\_cross = 0.\<close>
              have hc0_le: "?c0 \<le> 0"
              proof (cases "(0::nat) = i")
                case True thus ?thesis by (by100 simp)
              next
                case hne0: False show ?thesis
                proof (cases "(0::nat) = Suc i mod ?n")
                  case True
                  hence hvx0: "vx2(Suc i mod ?n) = vx2 0" and hvy0: "vy2(Suc i mod ?n) = vy2 0" by simp+
                  show ?thesis by (simp only: hvx0 hvy0, by100 simp)
                next
                  case False
                  have h0_lt2: "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
                  from hC11_2[rule_format, OF hi h0_lt2 hne0 False]
                  show ?thesis by linarith
                qed
              qed
              have hA_lt2: "?k + 1 - jj < ?n" using hjjk hk_lt_nm1 hjj1 by (by100 linarith)
              have hcA_le: "?cA \<le> 0"
              proof (cases "?k+1-jj = i")
                case True thus ?thesis by (by100 simp)
              next
                case hneA: False show ?thesis
                proof (cases "?k+1-jj = Suc i mod ?n")
                  case True
                  hence hvx: "vx2(Suc i mod ?n) = vx2(?k+1-jj)" and hvy: "vy2(Suc i mod ?n) = vy2(?k+1-jj)" by simp+
                  show ?thesis by (simp only: hvx hvy, by100 simp)
                next
                  case False
                  from hC11_2[rule_format, OF hi hA_lt2 hneA False]
                  show ?thesis by linarith
                qed
              qed
              have hB_lt2: "?k - jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
              have hcB_le: "?cB \<le> 0"
              proof (cases "?k-jj = i")
                case True thus ?thesis by (by100 simp)
              next
                case hneB: False show ?thesis
                proof (cases "?k-jj = Suc i mod ?n")
                  case True
                  hence hvx: "vx2(Suc i mod ?n) = vx2(?k-jj)" and hvy: "vy2(Suc i mod ?n) = vy2(?k-jj)" by simp+
                  show ?thesis by (simp only: hvx hvy, by100 simp)
                next
                  case False
                  from hC11_2[rule_format, OF hi hB_lt2 hneB False]
                  show ?thesis by linarith
                qed
              qed
              \<comment> \<open>Sum of non-positive terms = 0 \\<to> each term = 0.\<close>
              have hsum0: "(1-ss-ttp)*?c0 + ss*?cA + ttp*?cB = 0" using hedge_cross hlin by linarith
              have hterm0_le: "(1-ss-ttp)*?c0 \<le> 0" using h1st2 hc0_le
                mult_nonneg_nonneg[of "1-ss-ttp" "-?c0"] by linarith
              have htermA_le: "ss*?cA \<le> 0" using hss hcA_le
                mult_nonneg_nonneg[of ss "-?cA"] by linarith
              have htermB_le: "ttp*?cB \<le> 0" using htp2 hcB_le
                mult_nonneg_nonneg[of ttp "-?cB"] by linarith
              have ht0: "(1-ss-ttp)*?c0 = 0" using hsum0 hterm0_le htermA_le htermB_le by linarith
              have htA: "ss*?cA = 0" using hsum0 hterm0_le htermA_le htermB_le by linarith
              have htB: "ttp*?cB = 0" using hsum0 hterm0_le htermA_le htermB_le by linarith
              \<comment> \<open>At most 2 of {0, A, B} can be {i, Suc i}. So at least 1 has strict C11 < 0.
                 For that vertex: coefficient = 0. Then trace back to contradiction.\<close>
              \<comment> \<open>At least one of {0, k+1-jj, k-jj} is NOT {i, Suc i mod n}.
                 So at least one of ht0/htA/htB has coefficient = 0 with C11 < 0.\<close>
              \<comment> \<open>Case analysis: which coefficient is forced to 0?\<close>
              \<comment> \<open>Case 1: 0 is not an endpoint AND c0 < 0 \\<to> 1-ss-ttp = 0 \\<to> x on edge jj \\<to> \\<bot>.\<close>
              \<comment> \<open>Case 2: A is not endpoint AND cA < 0 \\<to> ss = 0 \\<to> cross\\_{jj+1}(x) = 0.\<close>
              \<comment> \<open>Case 3: B is not endpoint AND cB < 0 \\<to> ttp = 0 \\<to> cross\\_jj(x) = 0.\<close>
              show False
              proof -
                \<comment> \<open>The three vertices {0, k+1-jj, k-jj} are distinct.\<close>
                have hA_ne_0: "?k + 1 - jj \<noteq> (0::nat)" using hjjk hjj1 hk_ge2 by (by100 linarith)
                have hB_ne_0: "?k - jj \<noteq> (0::nat)" using hjjk hjj1 by (by100 linarith)
                have hA_ne_B: "?k + 1 - jj \<noteq> ?k - jj" using hjj1 hjjk by (by100 linarith)
                \<comment> \<open>At most 2 of {0, A, B} can be {i, Suc i mod n}. Since |{0,A,B}|=3 > 2:\<close>
                have "\<not> ((0::nat) = i \<or> 0 = Suc i mod ?n) \<or>
                      \<not> (?k+1-jj = i \<or> ?k+1-jj = Suc i mod ?n) \<or>
                      \<not> (?k-jj = i \<or> ?k-jj = Suc i mod ?n)"
                proof (rule ccontr)
                  assume "\<not> ?thesis"
                  hence h0in: "(0::nat) = i \<or> 0 = Suc i mod ?n"
                    and hAin: "?k+1-jj = i \<or> ?k+1-jj = Suc i mod ?n"
                    and hBin: "?k-jj = i \<or> ?k-jj = Suc i mod ?n" by (by100 simp)+
                  \<comment> \<open>{i, Suc i mod n} has at most 2 elements, but {0, A, B} has 3 distinct.\<close>
                  from h0in hAin hBin hA_ne_0 hB_ne_0 hA_ne_B
                  show False by (by100 auto)
                qed
                thus ?thesis
                proof (elim disjE)
                  assume h_case0: "\<not> ((0::nat) = i \<or> 0 = Suc i mod ?n)"
                  hence "?c0 < 0"
                  proof -
                    have "0 \<noteq> i" "(0::nat) \<noteq> Suc i mod ?n" using h_case0 by (by100 simp)+
                    have "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
                    from hC11_2[rule_format, OF hi \<open>0 < ?n\<close> \<open>0 \<noteq> i\<close> \<open>0 \<noteq> Suc i mod ?n\<close>]
                    show ?thesis by linarith
                  qed
                  have "?c0 \<noteq> 0" using \<open>?c0 < 0\<close> by linarith
                  have h1st_eq0: "1 - ss - ttp = 0"
                    using ht0 \<open>?c0 \<noteq> 0\<close> by (simp only: mult_eq_0_iff, by100 simp)
                  from mp[OF h1st0_imp h1st_eq0]
                  obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                    (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                  have "jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                  hence "jj < length ?w'" using hlen_eq by (by100 simp)
                  have "Suc jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                  hence "Suc jj mod ?n = Suc jj" by (by100 simp)
                  hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                  from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                  have "x \<noteq> ((1-t')*vx2 jj + t'*vx2(Suc jj mod length ?w'),
                             (1-t')*vy2 jj + t'*vy2(Suc jj mod length ?w'))" .
                  with hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> show False by (by100 simp)
                next
                  assume h_caseA: "\<not> (?k+1-jj = i \<or> ?k+1-jj = Suc i mod ?n)"
                  hence hneA_i: "?k+1-jj \<noteq> i" and hneA_si: "?k+1-jj \<noteq> Suc i mod ?n" by (by100 simp)+
                  from hC11_2[rule_format, OF hi hA_lt2 hneA_i hneA_si]
                  have hcA_strict: "?cA < 0" by linarith
                  have "?cA \<noteq> 0" using hcA_strict by linarith
                  have hss_eq0: "ss = 0" using htA \<open>?cA \<noteq> 0\<close>
                    by (simp only: mult_eq_0_iff, by100 simp)
                  \<comment> \<open>Now ss=0. From ht0: (1-ttp)*c0 = 0. From htB: ttp*cB = 0.
                     Case split on c0 and cB.\<close>
                  show False
                  proof (cases "?c0 = 0")
                    case hc0_zero: False
                    \<comment> \<open>c0 \\<noteq> 0: from ht0 with ss=0: (1-ttp)*c0 = 0 \\<to> 1-ttp = 0 \\<to> ttp = 1.
                       Then 1-ss-ttp = 0 \\<to> Case 0 \\<to> contradiction.\<close>
                    have "1 - ss - ttp = 0"
                      using ht0 hss_eq0 hc0_zero by (simp only: mult_eq_0_iff, by100 simp)
                    from mp[OF h1st0_imp this]
                    obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                      (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                    have "jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                    hence "jj < length ?w'" using hlen_eq by (by100 simp)
                    have "Suc jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                    hence "Suc jj mod ?n = Suc jj" by (by100 simp)
                    hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                    from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                    show False using hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> by (by100 simp)
                  next
                    case hc0_eq0: True
                    show False
                    proof (cases "?cB = 0")
                      case hcB_zero: False
                      \<comment> \<open>cB \\<noteq> 0: from htB: ttp = 0. With ss=0: 1-ss-ttp = 1.
                         phi\\_L(x) = v\\_0. Then x = v\\_0 \\<to> cross\\_diag = 0 \\<to> \\<bot>.\<close>
                      have "ttp = 0" using htB hcB_zero
                        by (simp only: mult_eq_0_iff, by100 simp)
                      \<comment> \<open>ss = 0, ttp = 0: phi\\_L(x) = 1*v\\_0 = v\\_0.
                         From Cramer: cross\\_j(x) = 0 and cross\\_{j+1}(x) = 0 \\<to> x = v\\_0.
                         cross\\_diag(v\\_0) = 0. Contradiction.\<close>
                      \<comment> \<open>ss=ttp=0: cross\\_j(x)=0 AND cross\\_{j+1}(x)=0 (two fan rays).
                         Fan det > 0 \\<to> unique solution x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.\<close>
                      from mp[OF hs0_imp \<open>ss = 0\<close>]
                      have hcr1: "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)" .
                      from mp[OF htp0_imp \<open>ttp = 0\<close>]
                      have hcr2: "(vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)" .
                      have hj_lt: "jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                      have hsj_lt: "Suc jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                      have hfdet: "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) > 0"
                        using hfan_det_0[rule_format, OF hj_lt hsj_lt hjj1 lessI] .
                      \<comment> \<open>Linear system: det > 0 and RHS = 0 \\<to> fst x = vx2 0, snd x = vy2 0.\<close>
                      have "fst x = vx2 0 \<and> snd x = vy2 0"
                      proof -
                        let ?dx = "fst x - vx2 0" let ?dy = "snd x - vy2 0"
                        from hcr1 have "(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx" by (by100 simp)
                        from hcr2 have "(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx" by (by100 simp)
                        \<comment> \<open>Cramer: ?dx = 0 and ?dy = 0 from det \\<noteq> 0.\<close>
                        have "?dx * ((vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0)) = 0"
                          using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close>
                                \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close>
                          by (by100 algebra)
                        hence "?dx = 0" using hfdet by (simp only: mult_eq_0_iff, by100 simp)
                        have "(vx2 jj - vx2 0)*?dy = 0"
                          using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close> \<open>?dx = 0\<close> by (by100 simp)
                        hence "?dy = 0"
                        proof (cases "vx2 jj = vx2 0")
                          case False hence "vx2 jj - vx2 0 \<noteq> 0" by linarith
                          with \<open>(vx2 jj - vx2 0)*?dy = 0\<close> show ?thesis
                            by (simp only: mult_eq_0_iff, by100 simp)
                        next
                          case True
                          have "(vx2(Suc jj) - vx2 0)*?dy = 0"
                            using \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close> \<open>?dx = 0\<close>
                            by (by100 simp)
                          moreover have "vx2(Suc jj) - vx2 0 \<noteq> 0"
                          proof
                            assume "vx2(Suc jj) - vx2 0 = 0"
                            with True have "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) = 0"
                              by (by100 simp)
                            with hfdet show False by linarith
                          qed
                          ultimately show "?dy = 0" by (simp only: mult_eq_0_iff, by100 simp)
                        qed
                        from \<open>?dx = 0\<close> \<open>?dy = 0\<close> show ?thesis by (by100 simp)
                      qed
                      hence hfst0: "fst x = vx2 0" and hsnd0: "snd x = vy2 0" by (by100 simp)+
                      have "cross_diag x = (vx2 ?k - vx2 0) * (snd x - vy2 0)
                        - (vy2 ?k - vy2 0) * (fst x - vx2 0)" unfolding cross_diag_def by (by100 simp)
                      hence "cross_diag x = 0" using hfst0 hsnd0 by (by100 simp)
                      with hcdx show False by linarith
                    next
                      case hcB_eq0: True
                      \<comment> \<open>c0 = 0 AND cB = 0. Both v\\_0 and v\\_B are edge endpoints.
                         So {0, k-jj} \\<subseteq> {i, Suc i mod n}.
                         Sub-case 0=i: Suc i=1, k-jj=1, jj=k-1 \\<to> cross\\_diag=0 \\<to> \\<bot>.
                         Sub-case 0=Suc i: i=n-1, k-jj=n-1 impossible.\<close>
                      \<comment> \<open>c0=0 means 0 = i or 0 = Suc i mod n (from C11: non-endpoints have c < 0).\<close>
                      have h0_endpoint: "(0::nat) = i \<or> 0 = Suc i mod ?n"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        hence "0 \<noteq> i" "(0::nat) \<noteq> Suc i mod ?n" by (by100 simp)+
                        have "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
                        from hC11_2[rule_format, OF hi \<open>0 < ?n\<close> \<open>0 \<noteq> i\<close> \<open>0 \<noteq> Suc i mod ?n\<close>]
                        have "?c0 < 0" by linarith
                        with hc0_eq0 show False by linarith
                      qed
                      show False
                      proof (cases "i = 0")
                        case True
                        hence "Suc 0 mod ?n = 1" using hn_ge3 by (by100 simp)
                        \<comment> \<open>cB = 0 means k-jj = i or k-jj = Suc i. Since i=0 and k-jj \\<ge> 1: k-jj = 1.\<close>
                        have hcB_endpoint: "?k-jj = 0 \<or> ?k-jj = Suc 0 mod ?n"
                        proof (rule ccontr)
                          assume "\<not> ?thesis"
                          hence "?k-jj \<noteq> 0" "?k-jj \<noteq> Suc 0 mod ?n" by (by100 simp)+
                          have "?k-jj \<noteq> i" using \<open>?k-jj \<noteq> 0\<close> True by simp
                          have "?k-jj \<noteq> Suc i mod ?n" using \<open>?k-jj \<noteq> Suc 0 mod ?n\<close> True by simp
                          from hC11_2[rule_format, OF hi hB_lt2 \<open>?k-jj \<noteq> i\<close> \<open>?k-jj \<noteq> Suc i mod ?n\<close>]
                          show False using hcB_eq0 by linarith
                        qed
                        hence "?k - jj = 1" using True hB_ne_0 \<open>Suc 0 mod ?n = 1\<close> by (by100 auto)
                        hence "jj = ?k - 1" by (by100 linarith)
                        \<comment> \<open>Suc jj = k. cross\\_{Suc jj}(x) = cross\\_k(x) = cross\\_diag(x) = 0.\<close>
                        have "Suc jj = ?k" using \<open>jj = ?k - 1\<close> hk_ge2 by (by100 linarith)
                        from mp[OF hs0_imp \<open>ss = 0\<close>]
                        have "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)" .
                        hence "(vx2 ?k - vx2 0)*(snd x - vy2 0) = (vy2 ?k - vy2 0)*(fst x - vx2 0)"
                          using \<open>Suc jj = ?k\<close> by (by100 simp)
                        hence "cross_diag x = 0" unfolding cross_diag_def by (by100 algebra)
                        with hcdx show False by linarith
                      next
                        case False
                        \<comment> \<open>i \\<noteq> 0 and 0 is endpoint: 0 = Suc i mod n \\<to> i = n-1.\<close>
                        hence "0 = Suc i mod ?n" using h0_endpoint by (by100 simp)
                        hence hSi_mod: "Suc i mod ?n = 0" by simp
                        have "i = ?n - 1"
                        proof -
                          have "\<not> (Suc i < ?n)"
                          proof
                            assume "Suc i < ?n"
                            hence "Suc i mod ?n = Suc i" by (by100 simp)
                            with hSi_mod show False by (by100 simp)
                          qed
                          moreover have "Suc i \<le> ?n" using hi by (by100 linarith)
                          ultimately show ?thesis by (by100 linarith)
                        qed
                        \<comment> \<open>cB=0 means k-jj is endpoint: k-jj = i or k-jj = Suc i.
                           k-jj = i = n-1: impossible (k-jj < n-1).
                           k-jj = Suc i mod n = 0: impossible (k-jj \\<ge> 1).\<close>
                        have "?k - jj < ?n - 1" using hjjk hjj1 hk_lt_nm1 by (by100 linarith)
                        have "?k - jj \<noteq> ?n - 1" using \<open>?k - jj < ?n - 1\<close> by linarith
                        have "?k - jj \<noteq> 0" using hB_ne_0 .
                        \<comment> \<open>But cB=0 requires k-jj = i or k-jj = Suc i mod n.
                           i = n-1 \\<to> k-jj \\<noteq> n-1. Suc i mod n = 0 \\<to> k-jj \\<noteq> 0.\<close>
                        have "?k-jj \<noteq> i" using \<open>?k-jj \<noteq> ?n-1\<close> \<open>i = ?n-1\<close> by simp
                        have "?k-jj \<noteq> Suc i mod ?n" using \<open>?k-jj \<noteq> 0\<close> \<open>0 = Suc i mod ?n\<close> by simp
                        from hC11_2[rule_format, OF hi hB_lt2 \<open>?k-jj \<noteq> i\<close> \<open>?k-jj \<noteq> Suc i mod ?n\<close>]
                        have "?cB < 0" by linarith
                        with hcB_eq0 show False by linarith
                      qed
                    qed
                  qed
                next
                  assume h_caseB: "\<not> (?k-jj = i \<or> ?k-jj = Suc i mod ?n)"
                  hence hneB_i: "?k-jj \<noteq> i" and hneB_si: "?k-jj \<noteq> Suc i mod ?n" by (by100 simp)+
                  from hC11_2[rule_format, OF hi hB_lt2 hneB_i hneB_si]
                  have hcB_strict: "?cB < 0" by linarith
                  have "?cB \<noteq> 0" using hcB_strict by linarith
                  have htp_eq0: "ttp = 0" using htB \<open>?cB \<noteq> 0\<close>
                    by (simp only: mult_eq_0_iff, by100 simp)
                  \<comment> \<open>ttp=0. From ht0: (1-ss)*c0 = 0. From htA: ss*cA = 0.\<close>
                  show False
                  proof (cases "?c0 = 0")
                    case hc0_z2: False
                    \<comment> \<open>c0 \\<noteq> 0: 1-ss = 0, ss = 1, 1-ss-ttp = 0 \\<to> Case 0 \\<to> \\<bot>.\<close>
                    have "1 - ss - ttp = 0"
                      using ht0 htp_eq0 hc0_z2 by (simp only: mult_eq_0_iff, by100 simp)
                    from mp[OF h1st0_imp this]
                    obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                      (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                    have "jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                    hence "jj < length ?w'" using hlen_eq by (by100 simp)
                    have "Suc jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                    hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                    from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                    show False using hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> by (by100 simp)
                  next
                    case hc0_eq02: True
                    show False
                    proof (cases "?cA = 0")
                      case hcA_z2: False
                      \<comment> \<open>cA \\<noteq> 0: ss = 0. With ttp=0: both = 0, phi\\_L(x)=v\\_0 \\<to> x=v\\_0 \\<to> cd=0 \\<to> \\<bot>.\<close>
                      have "ss = 0" using htA hcA_z2
                        by (simp only: mult_eq_0_iff, by100 simp)
                      \<comment> \<open>ss=ttp=0: cross\\_j(x)=0 AND cross\\_{j+1}(x)=0 (two fan rays).
                         Fan det > 0 \\<to> unique solution x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.\<close>
                      from mp[OF hs0_imp \<open>ss = 0\<close>]
                      have hcr1: "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)" .
                      from mp[OF htp0_imp \<open>ttp = 0\<close>]
                      have hcr2: "(vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)" .
                      have hj_lt: "jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                      have hsj_lt: "Suc jj < ?n" using hjjk hk_lt_nm1 by (by100 linarith)
                      have hfdet: "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) > 0"
                        using hfan_det_0[rule_format, OF hj_lt hsj_lt hjj1 lessI] .
                      \<comment> \<open>Linear system: det > 0 and RHS = 0 \\<to> fst x = vx2 0, snd x = vy2 0.\<close>
                      have "fst x = vx2 0 \<and> snd x = vy2 0"
                      proof -
                        let ?dx = "fst x - vx2 0" let ?dy = "snd x - vy2 0"
                        from hcr1 have "(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx" by (by100 simp)
                        from hcr2 have "(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx" by (by100 simp)
                        \<comment> \<open>Cramer: ?dx = 0 and ?dy = 0 from det \\<noteq> 0.\<close>
                        have "?dx * ((vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0)) = 0"
                          using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close>
                                \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close>
                          by (by100 algebra)
                        hence "?dx = 0" using hfdet by (simp only: mult_eq_0_iff, by100 simp)
                        have "(vx2 jj - vx2 0)*?dy = 0"
                          using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close> \<open>?dx = 0\<close> by (by100 simp)
                        hence "?dy = 0"
                        proof (cases "vx2 jj = vx2 0")
                          case False hence "vx2 jj - vx2 0 \<noteq> 0" by linarith
                          with \<open>(vx2 jj - vx2 0)*?dy = 0\<close> show ?thesis
                            by (simp only: mult_eq_0_iff, by100 simp)
                        next
                          case True
                          have "(vx2(Suc jj) - vx2 0)*?dy = 0"
                            using \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close> \<open>?dx = 0\<close>
                            by (by100 simp)
                          moreover have "vx2(Suc jj) - vx2 0 \<noteq> 0"
                          proof
                            assume "vx2(Suc jj) - vx2 0 = 0"
                            with True have "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) = 0"
                              by (by100 simp)
                            with hfdet show False by linarith
                          qed
                          ultimately show "?dy = 0" by (simp only: mult_eq_0_iff, by100 simp)
                        qed
                        from \<open>?dx = 0\<close> \<open>?dy = 0\<close> show ?thesis by (by100 simp)
                      qed
                      hence hfst0: "fst x = vx2 0" and hsnd0: "snd x = vy2 0" by (by100 simp)+
                      have "cross_diag x = (vx2 ?k - vx2 0) * (snd x - vy2 0)
                        - (vy2 ?k - vy2 0) * (fst x - vx2 0)" unfolding cross_diag_def by (by100 simp)
                      hence "cross_diag x = 0" using hfst0 hsnd0 by (by100 simp)
                      with hcdx show False by linarith
                    next
                      case hcA_eq02: True
                      \<comment> \<open>c0=0 and cA=0: both v\\_0 and v\\_A are endpoints of edge i.
                         {0, k+1-jj} \\<subseteq> {i, Suc i mod n}.\<close>
                      show False
                      proof (cases "i = 0")
                        case True
                        \<comment> \<open>i=0: Suc i = 1. k+1-jj must be 0 or 1. Since k+1-jj \\<ge> 2: impossible.\<close>
                        have "?k + 1 - jj \<ge> 2" using hjj1 hjjk hk_ge2 by (by100 linarith)
                        \<comment> \<open>cA=0 needs k+1-jj = i or k+1-jj = Suc i. i=0, Suc i=1. But k+1-jj \\<ge> 2.\<close>
                        have "?k+1-jj \<noteq> 0" using \<open>?k+1-jj \<ge> 2\<close> by (by100 linarith)
                        have "Suc 0 mod ?n = 1" using hn_ge3 by (by100 simp)
                        have "?k+1-jj \<noteq> 1" using \<open>?k+1-jj \<ge> 2\<close> by (by100 linarith)
                        hence "?k+1-jj \<noteq> Suc i mod ?n" using True \<open>Suc 0 mod ?n = 1\<close> by simp
                        from hC11_2[rule_format, OF hi hA_lt2 \<open>?k+1-jj \<noteq> 0\<close>[folded True] \<open>?k+1-jj \<noteq> Suc i mod ?n\<close>]
                        show False using hcA_eq02 by linarith
                      next
                        case False
                        \<comment> \<open>i \\<noteq> 0: c0=0 \\<to> 0 endpoint \\<to> 0 = Suc i mod n \\<to> i = n-1.\<close>
                        have h0ep: "(0::nat) = i \<or> 0 = Suc i mod ?n"
                        proof (rule ccontr)
                          assume "\<not> ?thesis"
                          hence "0 \<noteq> i" "(0::nat) \<noteq> Suc i mod ?n" by (by100 simp)+
                          have "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
                          from hC11_2[rule_format, OF hi \<open>0 < ?n\<close> \<open>0 \<noteq> i\<close> \<open>0 \<noteq> Suc i mod ?n\<close>]
                          show False using hc0_eq02 by linarith
                        qed
                        hence "0 = Suc i mod ?n" using False by (by100 simp)
                        hence hSi_mod2: "Suc i mod ?n = 0" by simp
                        have "i = ?n - 1"
                        proof -
                          have "\<not> (Suc i < ?n)"
                          proof
                            assume "Suc i < ?n"
                            hence "Suc i mod ?n = Suc i" by (by100 simp)
                            with hSi_mod2 show False by (by100 simp)
                          qed
                          moreover have "Suc i \<le> ?n" using hi by (by100 linarith)
                          ultimately show ?thesis by (by100 linarith)
                        qed
                        \<comment> \<open>k+1-jj is also endpoint of edge n-1. Suc(n-1) mod n = 0.
                           k+1-jj = n-1 or k+1-jj = 0. But k+1-jj \\<ge> 2 and k+1-jj \\<le> k < n-1.\<close>
                        have "?k + 1 - jj \<ge> 2" using hjj1 hjjk hk_ge2 by (by100 linarith)
                        have "?k + 1 - jj \<le> ?k" using hjj1 by (by100 linarith)
                        hence "?k + 1 - jj < ?n - 1" using hk_lt_nm1 by (by100 linarith)
                        have "?k+1-jj \<noteq> ?n - 1" using \<open>?k+1-jj < ?n-1\<close> by linarith
                        have "?k+1-jj \<noteq> 0" using \<open>?k+1-jj \<ge> 2\<close> by linarith
                        hence "?k+1-jj \<noteq> i" using \<open>i = ?n - 1\<close> \<open>?k+1-jj \<noteq> ?n-1\<close> by simp
                        have "?k+1-jj \<noteq> Suc i mod ?n" using \<open>?k+1-jj \<noteq> 0\<close> hSi_mod2 by simp
                        from hC11_2[rule_format, OF hi hA_lt2 \<open>?k+1-jj \<noteq> i\<close> \<open>?k+1-jj \<noteq> Suc i mod ?n\<close>]
                        show False using hcA_eq02 by linarith
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
          \<comment> \<open>SHARED: phi\\_R Cramer decomposition. Symmetric to hphi\\_L\\_decomp for right fan.\<close>
          have hphi_R_decomp: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x > 0 \<Longrightarrow>
              \<exists>j s tp. ?k \<le> j \<and> j < ?n - 1 \<and> s \<ge> 0 \<and> tp \<ge> 0 \<and> 1 - s - tp \<ge> 0 \<and>
              phi_R x = ((1-s-tp)*vx2 ?k + s*vx2(Suc j) + tp*vx2(Suc(Suc j) mod ?n),
                         (1-s-tp)*vy2 ?k + s*vy2(Suc j) + tp*vy2(Suc(Suc j) mod ?n)) \<and>
              (s = 0 \<longrightarrow> (vx2(Suc j) - vx2 0)*(snd x - vy2 0) = (vy2(Suc j) - vy2 0)*(fst x - vx2 0)) \<and>
              (tp = 0 \<longrightarrow> (vx2 j - vx2 0)*(snd x - vy2 0) = (vy2 j - vy2 0)*(fst x - vx2 0)) \<and>
              (1 - s - tp = 0 \<longrightarrow> (\<exists>t'\<in>I_set. x = ((1-t')*vx2 j + t'*vx2(Suc j),
                                                     (1-t')*vy2 j + t'*vy2(Suc j))))"
            sorry \<comment> \<open>Sector + LEAST + Cramer for right fan. Symmetric to hphi\\_L\\_decomp.\<close>
          \<comment> \<open>HELPER: k = Suc i mod n with k \\<ge> 2, k < n, i < n implies i = k - 1.
             Because i = n-1 gives Suc i mod n = 0, contradicting k \\<ge> 2.\<close>
          have hk_suc_mod: "\<And>ii. ii < ?n \<Longrightarrow> ?k = Suc ii mod ?n \<Longrightarrow> ii = ?k - 1"
          proof -
            fix ii assume hii: "ii < ?n" and hkeq: "?k = Suc ii mod ?n"
            show "ii = ?k - 1"
            proof (cases "ii < ?n - 1")
              case True hence "Suc ii < ?n" by (by100 linarith)
              hence "Suc ii mod ?n = Suc ii" by (by100 simp)
              hence "?k = Suc ii" using hkeq by simp
              thus ?thesis by (by100 linarith)
            next
              case False hence "ii = ?n - 1" using hii by (by100 linarith)
              hence "Suc ii = ?n" using hn_ge3 by (by100 linarith)
              hence "Suc ii mod ?n = 0" by (by100 simp)
              hence "?k = 0" using hkeq by simp
              with hk_ge2 show ?thesis by (by100 linarith)
            qed
          qed
          \<comment> \<open>HELPER: Suc(Suc jj) mod n cannot equal values < k when jj \\<ge> k and k \\<ge> 2.\<close>
          have hSSj_mod_ge: "\<And>jj. ?k \<le> jj \<Longrightarrow> jj < ?n - 1 \<Longrightarrow>
              Suc(Suc jj) mod ?n \<ge> ?k + 2 \<or> Suc(Suc jj) mod ?n = 0"
          proof -
            fix jj :: nat assume hjj_k: "?k \<le> jj" and hjj_n: "jj < ?n - 1"
            show "Suc(Suc jj) mod ?n \<ge> ?k + 2 \<or> Suc(Suc jj) mod ?n = 0"
            proof (cases "Suc(Suc jj) < ?n")
              case True hence "Suc(Suc jj) mod ?n = Suc(Suc jj)" by (by100 simp)
              moreover have "Suc(Suc jj) \<ge> ?k + 2" using hjj_k by (by100 linarith)
              ultimately show ?thesis by (by100 linarith)
            next
              case False hence "Suc(Suc jj) = ?n" using hjj_n by (by100 linarith)
              hence "Suc(Suc jj) mod ?n = 0" by (by100 simp)
              thus ?thesis by simp
            qed
          qed
          have hphi_R_int: "\<And>x. x \<in> P2 \<Longrightarrow> cross_diag x > 0 \<Longrightarrow>
              (\<forall>i'<length ?w'. \<forall>t'\<in>I_set.
                x \<noteq> ((1-t')*vx2 i'+t'*vx2(Suc i' mod length ?w'),(1-t')*vy2 i'+t'*vy2(Suc i' mod length ?w'))) \<Longrightarrow>
              (\<forall>i<?n. \<forall>t\<in>I_set.
                phi_R x \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n)))"
          proof (intro allI impI ballI)
            fix x assume hx: "x \<in> P2" and hcdx: "cross_diag x > 0"
              and hint_x: "\<forall>i'<length ?w'. \<forall>t'\<in>I_set.
                x \<noteq> ((1-t')*vx2 i'+t'*vx2(Suc i' mod length ?w'),(1-t')*vy2 i'+t'*vy2(Suc i' mod length ?w'))"
            fix i :: nat and t :: real assume hi: "i < ?n" and ht: "t \<in> I_set"
            show "phi_R x \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
            proof
              assume heq: "phi_R x = ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
              \<comment> \<open>Same structure as phi\\_L\\_int but with right-fan decomposition.\<close>
              have hfst: "fst (phi_R x) = (1-t)*vx2 i + t*vx2(Suc i mod ?n)" using heq by (by100 simp)
              have hsnd: "snd (phi_R x) = (1-t)*vy2 i + t*vy2(Suc i mod ?n)" using heq by (by100 simp)
              have hedge_cross: "(fst (phi_R x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_R x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = 0"
                using hfst hsnd by (by100 algebra)
              have hphi_in: "phi_R x \<in> P2" using hphi_R_in_P2[OF hx hcdx] .
              \<comment> \<open>C11: negated cross product \\<ge> 0 at all vertices.\<close>
              let ?Ai = "vx2 i * vy2(Suc i mod ?n) - vy2 i * vx2(Suc i mod ?n)"
              let ?Bi = "vy2 i - vy2(Suc i mod ?n)" let ?Ci = "vx2(Suc i mod ?n) - vx2 i"
              have hF_form: "\<And>px py :: real. -(px - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                + (py - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = ?Ai + ?Bi * px + ?Ci * py"
                by (by100 algebra)
              have "\<forall>l<?n. ?Ai + ?Bi * vx2 l + ?Ci * vy2 l \<ge> 0"
              proof (intro allI impI)
                fix l assume hl: "l < ?n"
                show "?Ai + ?Bi * vx2 l + ?Ci * vy2 l \<ge> 0"
                proof (cases "l = i")
                  case hli: True
                  have "?Ai + ?Bi * vx2 l + ?Ci * vy2 l =
                    -((vx2 l - vx2 i) * (vy2(Suc i mod ?n) - vy2 i) - (vy2 l - vy2 i) * (vx2(Suc i mod ?n) - vx2 i))"
                    by (by100 algebra)
                  thus ?thesis unfolding hli by (by100 simp)
                next
                  case False show ?thesis
                  proof (cases "l = Suc i mod ?n")
                    case hlsi: True
                    have "?Ai + ?Bi * vx2 l + ?Ci * vy2 l =
                      -((vx2 l - vx2 i) * (vy2(Suc i mod ?n) - vy2 i) - (vy2 l - vy2 i) * (vx2(Suc i mod ?n) - vx2 i))"
                      by (by100 algebra)
                    thus ?thesis unfolding hlsi by (by100 simp)
                  next
                    case False2: False
                    have hval_R: "?Ai + ?Bi * vx2 l + ?Ci * vy2 l =
                      -((vx2 l - vx2 i) * (vy2(Suc i mod ?n) - vy2 i) - (vy2 l - vy2 i) * (vx2(Suc i mod ?n) - vx2 i))"
                      by (by100 algebra)
                    from hC11_2[rule_format, OF hi hl False False2]
                    show ?thesis unfolding hval_R by linarith
                  qed
                qed
              qed
              from haffine_nonneg[OF hphi_in this]
              have "?Ai + ?Bi * fst (phi_R x) + ?Ci * snd (phi_R x) \<ge> 0" .
              hence hedge_le: "(fst (phi_R x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_R x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) \<le> 0"
                using hF_form[of "fst (phi_R x)" "snd (phi_R x)"] by linarith
              \<comment> \<open>Get phi\\_R decomposition.\<close>
              from hphi_R_decomp[OF hx hcdx]
              obtain jj ss ttp where hjjk: "?k \<le> jj" and hjjn: "jj < ?n - 1"
                and hss: "ss \<ge> 0" and htp2: "ttp \<ge> 0" and h1st2: "1 - ss - ttp \<ge> 0"
                and hphi_dec: "phi_R x = ((1-ss-ttp)*vx2 ?k + ss*vx2(Suc jj) + ttp*vx2(Suc(Suc jj) mod ?n),
                                           (1-ss-ttp)*vy2 ?k + ss*vy2(Suc jj) + ttp*vy2(Suc(Suc jj) mod ?n))"
                and hs0_imp: "ss = 0 \<longrightarrow> (vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)"
                and htp0_imp: "ttp = 0 \<longrightarrow> (vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)"
                and h1st0_imp: "1 - ss - ttp = 0 \<longrightarrow>
                  (\<exists>t'\<in>I_set. x = ((1-t')*vx2 jj + t'*vx2(Suc jj), (1-t')*vy2 jj + t'*vy2(Suc jj)))"
                by (by5000 blast)
              \<comment> \<open>Cross product linearity.\<close>
              let ?cK = "(vx2 ?k - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2 ?k - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              let ?cSj = "(vx2(Suc jj) - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2(Suc jj) - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              let ?cSSj = "(vx2(Suc(Suc jj) mod ?n) - vx2 i)*(vy2(Suc i mod ?n) - vy2 i) - (vy2(Suc(Suc jj) mod ?n) - vy2 i)*(vx2(Suc i mod ?n) - vx2 i)"
              have hlin: "(fst (phi_R x) - vx2 i) * (vy2(Suc i mod ?n) - vy2 i)
                - (snd (phi_R x) - vy2 i) * (vx2(Suc i mod ?n) - vx2 i) = (1-ss-ttp)*?cK + ss*?cSj + ttp*?cSSj"
              proof -
                have hf: "fst (phi_R x) = (1-ss-ttp)*vx2 ?k + ss*vx2(Suc jj) + ttp*vx2(Suc(Suc jj) mod ?n)"
                  using hphi_dec by (by100 simp)
                have hs: "snd (phi_R x) = (1-ss-ttp)*vy2 ?k + ss*vy2(Suc jj) + ttp*vy2(Suc(Suc jj) mod ?n)"
                  using hphi_dec by (by100 simp)
                show ?thesis using hf hs by (by100 algebra)
              qed
              \<comment> \<open>C11 \\<le> 0 for each vertex. General identity for the cross product.\<close>
              have hval_gen: "\<And>l. ?Ai + ?Bi * vx2 l + ?Ci * vy2 l =
                -((vx2 l - vx2 i) * (vy2(Suc i mod ?n) - vy2 i) - (vy2 l - vy2 i) * (vx2(Suc i mod ?n) - vx2 i))"
                by (by100 algebra)
              have hk_lt: "?k < ?n" using hk_lt_nm1 by (by100 linarith)
              have hcK_le: "?cK \<le> 0"
              proof (cases "?k = i")
                case hli_k: True thus ?thesis unfolding hli_k by (by100 simp)
              next
                case hne_k: False show ?thesis
                proof (cases "?k = Suc i mod ?n")
                  case True
                  hence hvx: "vx2(Suc i mod ?n) = vx2 ?k" and hvy: "vy2(Suc i mod ?n) = vy2 ?k" by simp+
                  show ?thesis by (simp only: hvx hvy, by100 simp)
                next
                  case False
                  from hC11_2[rule_format, OF hi hk_lt hne_k False]
                  show ?thesis unfolding hval_gen by linarith
                qed
              qed
              have hSj_lt: "Suc jj < ?n" using hjjn by (by100 linarith)
              have hcSj_le: "?cSj \<le> 0"
              proof (cases "Suc jj = i")
                case True thus ?thesis by (by100 simp)
              next
                case hne: False show ?thesis
                proof (cases "Suc jj = Suc i mod ?n")
                  case True
                  hence hvx: "vx2(Suc i mod ?n) = vx2(Suc jj)" and hvy: "vy2(Suc i mod ?n) = vy2(Suc jj)" by simp+
                  show ?thesis by (simp only: hvx hvy, by100 simp)
                next
                  case False
                  from hC11_2[rule_format, OF hi hSj_lt hne False]
                  show ?thesis by linarith
                qed
              qed
              have hSSj_lt: "Suc(Suc jj) mod ?n < ?n" by (by100 simp)
              have hcSSj_le: "?cSSj \<le> 0"
              proof (cases "Suc(Suc jj) mod ?n = i")
                case True thus ?thesis by (by100 simp)
              next
                case hne: False show ?thesis
                proof (cases "Suc(Suc jj) mod ?n = Suc i mod ?n")
                  case True
                  hence hvx: "vx2(Suc i mod ?n) = vx2(Suc(Suc jj) mod ?n)"
                    and hvy: "vy2(Suc i mod ?n) = vy2(Suc(Suc jj) mod ?n)" by simp+
                  show ?thesis by (simp only: hvx hvy, by100 simp)
                next
                  case False
                  from hC11_2[rule_format, OF hi hSSj_lt hne False]
                  show ?thesis by linarith
                qed
              qed
              \<comment> \<open>Sum of non-positive terms = 0 \\<to> each term = 0.\<close>
              have hsum0: "(1-ss-ttp)*?cK + ss*?cSj + ttp*?cSSj = 0" using hedge_cross hlin by linarith
              have hterm0_le: "(1-ss-ttp)*?cK \<le> 0" using h1st2 hcK_le
                mult_nonneg_nonneg[of "1-ss-ttp" "-?cK"] by linarith
              have htermSj_le: "ss*?cSj \<le> 0" using hss hcSj_le
                mult_nonneg_nonneg[of ss "-?cSj"] by linarith
              have htermSSj_le: "ttp*?cSSj \<le> 0" using htp2 hcSSj_le
                mult_nonneg_nonneg[of ttp "-?cSSj"] by linarith
              have htK: "(1-ss-ttp)*?cK = 0" using hsum0 hterm0_le htermSj_le htermSSj_le by linarith
              have htSj: "ss*?cSj = 0" using hsum0 hterm0_le htermSj_le htermSSj_le by linarith
              have htSSj: "ttp*?cSSj = 0" using hsum0 hterm0_le htermSj_le htermSSj_le by linarith
              \<comment> \<open>Pigeonhole + case analysis. Same structure as phi\\_L\\_int.\<close>
              \<comment> \<open>Three output vertices: k, Suc jj, Suc(Suc jj) mod n — distinct.\<close>
              have hK_ne_Sj: "?k \<noteq> Suc jj" using hjjk by (by100 linarith)
              have hK_ne_SSj: "?k \<noteq> Suc(Suc jj) mod ?n"
              proof (cases "Suc(Suc jj) < ?n")
                case True hence "Suc(Suc jj) mod ?n = Suc(Suc jj)" by (by100 simp)
                thus ?thesis using hjjk by (by100 linarith)
              next
                case False hence "Suc(Suc jj) = ?n" using hjjn by (by100 linarith)
                hence "Suc(Suc jj) mod ?n = 0" by (by100 simp)
                thus ?thesis using hk_ge2 by (by100 linarith)
              qed
              have hSj_ne_SSj: "Suc jj \<noteq> Suc(Suc jj) mod ?n"
              proof (cases "Suc(Suc jj) < ?n")
                case True hence "Suc(Suc jj) mod ?n = Suc(Suc jj)" by (by100 simp)
                thus ?thesis by (by100 linarith)
              next
                case False hence "Suc(Suc jj) = ?n" using hjjn by (by100 linarith)
                hence "Suc(Suc jj) mod ?n = 0" by (by100 simp)
                thus ?thesis using hjjk hk_ge2 by (by100 linarith)
              qed
              \<comment> \<open>3 distinct vertices vs 2 edge endpoints \\<to> at least 1 non-endpoint.\<close>
              have "\<not> (?k = i \<or> ?k = Suc i mod ?n) \<or>
                    \<not> (Suc jj = i \<or> Suc jj = Suc i mod ?n) \<or>
                    \<not> (Suc(Suc jj) mod ?n = i \<or> Suc(Suc jj) mod ?n = Suc i mod ?n)"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                hence hKin: "?k = i \<or> ?k = Suc i mod ?n"
                  and hSjin: "Suc jj = i \<or> Suc jj = Suc i mod ?n"
                  and hSSjin: "Suc(Suc jj) mod ?n = i \<or> Suc(Suc jj) mod ?n = Suc i mod ?n" by (by100 simp)+
                from hKin hSjin hSSjin hK_ne_Sj hK_ne_SSj hSj_ne_SSj
                show False by (by100 auto)
              qed
              thus False
              proof (elim disjE)
                assume "\<not> (?k = i \<or> ?k = Suc i mod ?n)"
                hence "?cK < 0"
                proof -
                  have "?k \<noteq> i" "?k \<noteq> Suc i mod ?n" using \<open>\<not> (?k = i \<or> ?k = Suc i mod ?n)\<close> by (by100 simp)+
                  from hC11_2[rule_format, OF hi hk_lt \<open>?k \<noteq> i\<close> \<open>?k \<noteq> Suc i mod ?n\<close>]
                  show ?thesis by linarith
                qed
                have "?cK \<noteq> 0" using \<open>?cK < 0\<close> by linarith
                have h1st_eq0: "1 - ss - ttp = 0" using htK \<open>?cK \<noteq> 0\<close>
                  by (simp only: mult_eq_0_iff, by100 simp)
                from mp[OF h1st0_imp h1st_eq0]
                obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                  (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                have "jj < ?n" using hjjn by (by100 linarith)
                hence "jj < length ?w'" using hlen_eq by (by100 simp)
                have "Suc jj < ?n" using hjjn by (by100 linarith)
                hence "Suc jj mod ?n = Suc jj" by (by100 simp)
                hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                show False using hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> by (by100 simp)
              next
                assume h_caseSj: "\<not> (Suc jj = i \<or> Suc jj = Suc i mod ?n)"
                hence "?cSj < 0"
                proof -
                  have "Suc jj \<noteq> i" "Suc jj \<noteq> Suc i mod ?n" using h_caseSj by (by100 simp)+
                  from hC11_2[rule_format, OF hi hSj_lt \<open>Suc jj \<noteq> i\<close> \<open>Suc jj \<noteq> Suc i mod ?n\<close>]
                  show ?thesis by linarith
                qed
                have "?cSj \<noteq> 0" using \<open>?cSj < 0\<close> by linarith
                have hss_eq0: "ss = 0" using htSj \<open>?cSj \<noteq> 0\<close>
                  by (simp only: mult_eq_0_iff, by100 simp)
                \<comment> \<open>ss=0. Sub-cases on cK and cSSj.\<close>
                show False
                proof (cases "?cK = 0")
                  case hcK_z: False
                  have "1 - ss - ttp = 0" using htK hcK_z by (simp only: mult_eq_0_iff, by100 simp)
                  from mp[OF h1st0_imp this]
                  obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                    (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                  have "jj < ?n" using hjjn by (by100 linarith)
                  hence "jj < length ?w'" using hlen_eq by (by100 simp)
                  have "Suc jj < ?n" using hjjn by (by100 linarith)
                  hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                  from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                  show False using hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> by (by100 simp)
                next
                  case hcK_eq0: True
                  show False
                  proof (cases "?cSSj = 0")
                    case hcSSj_z: False
                    have "ttp = 0" using htSSj hcSSj_z by (simp only: mult_eq_0_iff, by100 simp)
                    \<comment> \<open>ss=ttp=0 \\<to> fan det uniqueness \\<to> x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.
                       Wait: for RIGHT fan, the fan is still from v\\_0. So same argument.\<close>
                    from mp[OF hs0_imp hss_eq0]
                    have hcr1: "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)" .
                    from mp[OF htp0_imp \<open>ttp = 0\<close>]
                    have hcr2: "(vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)" .
                    have hj_lt: "jj < ?n" using hjjn by (by100 linarith)
                    have hsj_lt: "Suc jj < ?n" using hjjn by (by100 linarith)
                    have hjj1: "1 \<le> jj" using hjjk hk_ge2 by (by100 linarith)
                    have hfdet: "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) > 0"
                      using hfan_det_0[rule_format, OF hj_lt hsj_lt hjj1 lessI] .
                    have "fst x = vx2 0 \<and> snd x = vy2 0"
                    proof -
                      let ?dx = "fst x - vx2 0" let ?dy = "snd x - vy2 0"
                      from hcr1 have h1_R: "(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx" by (by100 simp)
                      from hcr2 have h2_R: "(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx" by (by100 simp)
                      have "?dx * ((vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0)) = 0"
                        using h1_R h2_R by (by100 algebra)
                      hence "?dx = 0" using hfdet by (simp only: mult_eq_0_iff, by100 simp)
                      have "(vx2 jj - vx2 0)*?dy = 0"
                        using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close> \<open>?dx = 0\<close> by (by100 simp)
                      hence "?dy = 0"
                      proof (cases "vx2 jj = vx2 0")
                        case False hence "vx2 jj - vx2 0 \<noteq> 0" by linarith
                        with \<open>(vx2 jj - vx2 0)*?dy = 0\<close> show ?thesis
                          by (simp only: mult_eq_0_iff, by100 simp)
                      next
                        case True
                        have "(vx2(Suc jj) - vx2 0)*?dy = 0"
                          using \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close> \<open>?dx = 0\<close>
                          by (by100 simp)
                        moreover have "vx2(Suc jj) - vx2 0 \<noteq> 0"
                        proof
                          assume "vx2(Suc jj) - vx2 0 = 0"
                          with True have "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) = 0"
                            by (by100 simp)
                          with hfdet show False by linarith
                        qed
                        ultimately show "?dy = 0" by (simp only: mult_eq_0_iff, by100 simp)
                      qed
                      from \<open>?dx = 0\<close> \<open>?dy = 0\<close> show ?thesis by (by100 simp)
                    qed
                    hence hfst0: "fst x = vx2 0" and hsnd0: "snd x = vy2 0" by (by100 simp)+
                    have "cross_diag x = (vx2 ?k - vx2 0) * (snd x - vy2 0)
                      - (vy2 ?k - vy2 0) * (fst x - vx2 0)" unfolding cross_diag_def by (by100 simp)
                    hence "cross_diag x = 0" using hfst0 hsnd0 by (by100 simp)
                    with hcdx show False by linarith
                  next
                    case hcSSj_eq0: True
                    \<comment> \<open>cK=0 and cSSj=0. Both v\\_k and v\\_{Suc(Suc jj) mod n} are edge endpoints.
                       Same pigeonhole: {k, Suc(Suc jj) mod n} = {i, Suc i mod n}.\<close>
                    show False
                    proof (cases "?k = i")
                      case True
                      \<comment> \<open>k = i. Then Suc(Suc jj) mod n = Suc i mod n = Suc k mod n = k+1 (since k < n-1).\<close>
                      have "Suc ?k < ?n" using hk_lt_nm1 by (by100 linarith)
                      hence hSk_mod: "Suc ?k mod ?n = Suc ?k" by (by100 simp)
                      \<comment> \<open>cSSj=0 \\<to> SSj = i or SSj = Suc i. i = k \\<to> SSj = k or SSj = k+1.\<close>
                      have hSSj_ep: "Suc(Suc jj) mod ?n = ?k \<or> Suc(Suc jj) mod ?n = Suc ?k"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        hence "Suc(Suc jj) mod ?n \<noteq> ?k" "Suc(Suc jj) mod ?n \<noteq> Suc ?k" by (by100 simp)+
                        hence "Suc(Suc jj) mod ?n \<noteq> i" "Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n"
                          using True hSk_mod by simp+
                        from hC11_2[rule_format, OF hi hSSj_lt
                          \<open>Suc(Suc jj) mod ?n \<noteq> i\<close> \<open>Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n\<close>]
                        show False using hcSSj_eq0 by linarith
                      qed
                      \<comment> \<open>SSj = k: but SSj \\<noteq> k (from hK\\_ne\\_SSj). So SSj = k+1.\<close>
                      hence "Suc(Suc jj) mod ?n = Suc ?k" using hK_ne_SSj by (by100 auto)
                      \<comment> \<open>Suc(Suc jj) mod n = k+1. Since jj \\<ge> k: Suc(Suc jj) \\<ge> k+2.
                         If Suc(Suc jj) < n: SSj mod n = Suc(Suc jj) = k+1 \\<to> jj = k-1. But jj \\<ge> k. \\<bot>.
                         If Suc(Suc jj) = n: SSj mod n = 0 = k+1 \\<to> k+1 = 0. But k \\<ge> 2. \\<bot>.
                         If Suc(Suc jj) > n: impossible (jj < n-1 \\<to> Suc(Suc jj) \\<le> n).\<close>
                      have "Suc(Suc jj) \<le> ?n" using hjjn by (by100 linarith)
                      show False
                      proof (cases "Suc(Suc jj) < ?n")
                        case True
                        hence "Suc(Suc jj) mod ?n = Suc(Suc jj)" by (by100 simp)
                        hence "Suc(Suc jj) = Suc ?k" using \<open>Suc(Suc jj) mod ?n = Suc ?k\<close> by simp
                        hence "jj = ?k - 1" by (by100 linarith)
                        with hjjk show False by (by100 linarith)
                      next
                        case False
                        hence "Suc(Suc jj) = ?n" using \<open>Suc(Suc jj) \<le> ?n\<close> by (by100 linarith)
                        hence "Suc(Suc jj) mod ?n = 0" by (by100 simp)
                        hence "0 = Suc ?k" using \<open>Suc(Suc jj) mod ?n = Suc ?k\<close> by simp
                        with hk_ge2 show False by (by100 linarith)
                      qed
                    next
                      case False
                      \<comment> \<open>k \\<noteq> i. cK=0 \\<to> k = Suc i mod n \\<to> i = k-1 or i = n-1.\<close>
                      have hK_ep: "?k = Suc i mod ?n"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        with False have "?k \<noteq> i" "?k \<noteq> Suc i mod ?n" by (by100 simp)+
                        from hC11_2[rule_format, OF hi hk_lt \<open>?k \<noteq> i\<close> \<open>?k \<noteq> Suc i mod ?n\<close>]
                        show False using hcK_eq0 by linarith
                      qed
                      \<comment> \<open>k = Suc i mod n. Combined with cSSj=0: Suc(Suc jj) mod n = i (since Suc i taken by k).\<close>
                      have hSSj_eq_i: "Suc(Suc jj) mod ?n = i"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        hence "Suc(Suc jj) mod ?n \<noteq> i" by simp
                        moreover have "Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n"
                          using hK_ne_SSj hK_ep by simp
                        ultimately show False
                          using hC11_2[rule_format, OF hi hSSj_lt] hcSSj_eq0 by linarith
                      qed
                      \<comment> \<open>ss=0 \\<to> cross\\_{Suc jj}(x)=0. Now Suc(Suc jj) mod n = i and k = Suc i mod n.
                         From cross\\_{Suc jj}=0 and cross\\_jj conditions, derive x=v\\_0 or x on edge.
                         Actually: we need tp=0 too for the v\\_0 argument.
                         tp might not be 0. But 1-ss-ttp might also not be 0.
                         The only forced-to-zero coefficient is ss (from Suc jj non-endpoint).
                         cK=0 (K is endpoint), cSSj=0 (SSj is endpoint). So the ONLY non-endpoint is Suc jj.
                         Its coefficient ss=0 is already established. The other two are free.
                         phi\\_R(x) = (1-ttp)*v\\_k + ttp*v\\_{SSj mod n} = (1-ttp)*v\\_{Suc i mod n} + ttp*v\\_i.
                         This IS on edge i (reversed). So phi\\_R(x) on edge i.\<close>
                      \<comment> \<open>But we ASSUMED phi\\_R(x) = edge(i,t) via heq. This is consistent, not a contradiction.
                         The contradiction must come from tracing back to x.
                         ss=0 \\<to> cross\\_{Suc jj}(x)=0. This means x on fan ray through v\\_{Suc jj}.
                         If Suc jj \\<ge> k+1: cross\\_{Suc jj} \\<noteq> cross\\_diag. So x can be on this ray
                         with cross\\_diag > 0. x is on a diagonal (not edge). So x is target-interior.
                         But phi\\_R(x) IS on edge i. This is allowed — phi\\_R CAN map interior to edge.
                         WAIT: but phi\\_R\\_int claims this can't happen!

                         Is this case actually reachable? k = Suc i mod n and Suc(Suc jj) mod n = i.
                         If i < k: then Suc i \\<le> k, and Suc i mod n = Suc i (since Suc i < n). So k = Suc i.
                         Then i = k-1. And Suc(Suc jj) mod n = k-1.
                         jj \\<ge> k. Suc(Suc jj) \\<ge> k+2. Suc(Suc jj) mod n = k-1.
                         If Suc(Suc jj) < n: Suc(Suc jj) = k-1. But Suc(Suc jj) \\<ge> k+2 > k-1. Impossible.
                         If Suc(Suc jj) = n: n mod n = 0 = k-1 \\<to> k = 1. But k \\<ge> 2. Impossible.
                         So i < k is impossible here.

                         If i \\<ge> k: then i \\<ge> k and k = Suc i mod n.
                         If i < n-1: Suc i < n, Suc i mod n = Suc i. k = Suc i. But i \\<ge> k = Suc i > i. \\<bot>.
                         If i = n-1: Suc i = n, Suc i mod n = 0. k = 0. But k \\<ge> 2. \\<bot>.\<close>
                      \<comment> \<open>So this case is impossible!\<close>
                      \<comment> \<open>k = Suc i mod n. If i < n-1: k = Suc i > i \\<ge> k. \\<bot>.
                         If i = n-1: k = 0. But k \\<ge> 2. \\<bot>.\<close>
                      show False
                      proof (cases "i < ?n - 1")
                        case True
                        hence "Suc i < ?n" by (by100 linarith)
                        hence "Suc i mod ?n = Suc i" by (by100 simp)
                        hence hk_si: "?k = Suc i" using hK_ep by simp
                        \<comment> \<open>SSj mod n must be \\<ge> k+2 or 0 (from hSSj\\_mod\\_ge). Neither = k-1 or k.\<close>
                        from hSSj_mod_ge[OF hjjk hjjn]
                        have "Suc(Suc jj) mod ?n \<ge> ?k + 2 \<or> Suc(Suc jj) mod ?n = 0" .
                        have hSi_eq: "Suc i mod ?n = Suc i" using True by (by100 simp)
                        have "Suc(Suc jj) mod ?n \<noteq> i \<and> Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n"
                        proof -
                          from \<open>Suc(Suc jj) mod ?n \<ge> ?k + 2 \<or> Suc(Suc jj) mod ?n = 0\<close>
                          show ?thesis
                          proof
                            assume "Suc(Suc jj) mod ?n \<ge> ?k + 2"
                            thus ?thesis using hk_si hSi_eq by (by100 linarith)
                          next
                            assume "Suc(Suc jj) mod ?n = 0"
                            thus ?thesis using hk_si hk_ge2 hSi_eq by (by100 linarith)
                          qed
                        qed
                        hence "Suc(Suc jj) mod ?n \<noteq> i" "Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n" by simp+
                        from hC11_2[rule_format, OF hi hSSj_lt
                          \<open>Suc(Suc jj) mod ?n \<noteq> i\<close> \<open>Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n\<close>]
                        have "?cSSj < 0" unfolding hval_gen by linarith
                        with hcSSj_eq0 show False by linarith
                      next
                        case False hence "i = ?n - 1" using hi by (by100 linarith)
                        hence "Suc i = ?n" using hn_ge3 by (by100 linarith)
                        hence "Suc i mod ?n = 0" by (by100 simp)
                        hence "?k = 0" using hK_ep by simp
                        with hk_ge2 show False by (by100 linarith)
                      qed
                    qed
                  qed
                qed
              next
                assume h_caseSSj: "\<not> (Suc(Suc jj) mod ?n = i \<or> Suc(Suc jj) mod ?n = Suc i mod ?n)"
                hence "?cSSj < 0"
                proof -
                  have "Suc(Suc jj) mod ?n \<noteq> i" "Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n" using h_caseSSj by (by100 simp)+
                  from hC11_2[rule_format, OF hi hSSj_lt \<open>Suc(Suc jj) mod ?n \<noteq> i\<close> \<open>Suc(Suc jj) mod ?n \<noteq> Suc i mod ?n\<close>]
                  show ?thesis by linarith
                qed
                have "?cSSj \<noteq> 0" using \<open>?cSSj < 0\<close> by linarith
                have htp_eq0: "ttp = 0" using htSSj \<open>?cSSj \<noteq> 0\<close>
                  by (simp only: mult_eq_0_iff, by100 simp)
                \<comment> \<open>ttp=0. Symmetric to Case A (ss=0). Same sub-case analysis.\<close>
                show False
                proof (cases "?cK = 0")
                  case hcK_z2: False
                  have "1 - ss - ttp = 0" using htK hcK_z2 by (simp only: mult_eq_0_iff, by100 simp)
                  from mp[OF h1st0_imp this]
                  obtain t' where ht': "t' \<in> I_set" and hxeq: "x = ((1-t')*vx2 jj + t'*vx2(Suc jj),
                    (1-t')*vy2 jj + t'*vy2(Suc jj))" by (by100 blast)
                  have "jj < ?n" using hjjn by (by100 linarith)
                  hence "jj < length ?w'" using hlen_eq by (by100 simp)
                  have "Suc jj < ?n" using hjjn by (by100 linarith)
                  hence "Suc jj mod length ?w' = Suc jj" using hlen_eq by (by100 simp)
                  from hint_x[rule_format, OF \<open>jj < length ?w'\<close> ht']
                  show False using hxeq \<open>Suc jj mod length ?w' = Suc jj\<close> by (by100 simp)
                next
                  case hcK_eq02: True
                  show False
                  proof (cases "?cSj = 0")
                    case hcSj_z2: False
                    have "ss = 0" using htSj hcSj_z2 by (simp only: mult_eq_0_iff, by100 simp)
                    \<comment> \<open>ss=ttp=0 \\<to> x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.\<close>
                    from mp[OF hs0_imp \<open>ss = 0\<close>]
                    have hcr1: "(vx2(Suc jj) - vx2 0)*(snd x - vy2 0) = (vy2(Suc jj) - vy2 0)*(fst x - vx2 0)" .
                    from mp[OF htp0_imp htp_eq0]
                    have hcr2: "(vx2 jj - vx2 0)*(snd x - vy2 0) = (vy2 jj - vy2 0)*(fst x - vx2 0)" .
                    have hj_lt: "jj < ?n" using hjjn by (by100 linarith)
                    have hsj_lt2: "Suc jj < ?n" using hjjn by (by100 linarith)
                    have hjj1: "1 \<le> jj" using hjjk hk_ge2 by (by100 linarith)
                    have hfdet: "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) > 0"
                      using hfan_det_0[rule_format, OF hj_lt hsj_lt2 hjj1 lessI] .
                    have "fst x = vx2 0 \<and> snd x = vy2 0"
                    proof -
                      let ?dx = "fst x - vx2 0" let ?dy = "snd x - vy2 0"
                      from hcr1 have h1_R2: "(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx" by (by100 simp)
                      from hcr2 have h2_R2: "(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx" by (by100 simp)
                      have "?dx * ((vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0)) = 0"
                        using h1_R2 h2_R2 by (by100 algebra)
                      hence "?dx = 0" using hfdet by (simp only: mult_eq_0_iff, by100 simp)
                      have "(vx2 jj - vx2 0)*?dy = 0"
                        using \<open>(vx2 jj - vx2 0)*?dy = (vy2 jj - vy2 0)*?dx\<close> \<open>?dx = 0\<close> by (by100 simp)
                      hence "?dy = 0"
                      proof (cases "vx2 jj = vx2 0")
                        case False hence "vx2 jj - vx2 0 \<noteq> 0" by linarith
                        with \<open>(vx2 jj - vx2 0)*?dy = 0\<close> show ?thesis
                          by (simp only: mult_eq_0_iff, by100 simp)
                      next
                        case True
                        have "(vx2(Suc jj) - vx2 0)*?dy = 0"
                          using \<open>(vx2(Suc jj) - vx2 0)*?dy = (vy2(Suc jj) - vy2 0)*?dx\<close> \<open>?dx = 0\<close>
                          by (by100 simp)
                        moreover have "vx2(Suc jj) - vx2 0 \<noteq> 0"
                        proof
                          assume "vx2(Suc jj) - vx2 0 = 0"
                          with True have "(vx2 jj - vx2 0)*(vy2(Suc jj) - vy2 0) - (vy2 jj - vy2 0)*(vx2(Suc jj) - vx2 0) = 0"
                            by (by100 simp)
                          with hfdet show False by linarith
                        qed
                        ultimately show "?dy = 0" by (simp only: mult_eq_0_iff, by100 simp)
                      qed
                      from \<open>?dx = 0\<close> \<open>?dy = 0\<close> show ?thesis by (by100 simp)
                    qed
                    hence hfst0: "fst x = vx2 0" and hsnd0: "snd x = vy2 0" by (by100 simp)+
                    have "cross_diag x = (vx2 ?k - vx2 0) * (snd x - vy2 0)
                      - (vy2 ?k - vy2 0) * (fst x - vx2 0)" unfolding cross_diag_def by (by100 simp)
                    hence "cross_diag x = 0" using hfst0 hsnd0 by (by100 simp)
                    with hcdx show False by linarith
                  next
                    case hcSj_eq02: True
                    \<comment> \<open>cK=0 and cSj=0. {k, Suc jj} are edge endpoints.
                       At least one of {k, Suc jj} must be Suc i mod n (since they're 2 distinct
                       values mapping to 2 endpoints {i, Suc i mod n}). Then k = Suc i mod n
                       or Suc jj = Suc i mod n. Combined with cSSj non-endpoint: derive contradiction.\<close>
                    \<comment> \<open>cK=0 \\<to> k is endpoint: k = i or k = Suc i mod n.\<close>
                    have hK_ep2: "?k = i \<or> ?k = Suc i mod ?n"
                    proof (rule ccontr)
                      assume "\<not> ?thesis"
                      hence "?k \<noteq> i" "?k \<noteq> Suc i mod ?n" by (by100 simp)+
                      from hC11_2[rule_format, OF hi hk_lt \<open>?k \<noteq> i\<close> \<open>?k \<noteq> Suc i mod ?n\<close>]
                      show False using hcK_eq02 unfolding hval_gen by linarith
                    qed
                    \<comment> \<open>cSj=0 \\<to> Suc jj is endpoint.\<close>
                    have hSj_ep2: "Suc jj = i \<or> Suc jj = Suc i mod ?n"
                    proof (rule ccontr)
                      assume "\<not> ?thesis"
                      hence "Suc jj \<noteq> i" "Suc jj \<noteq> Suc i mod ?n" by (by100 simp)+
                      from hC11_2[rule_format, OF hi hSj_lt \<open>Suc jj \<noteq> i\<close> \<open>Suc jj \<noteq> Suc i mod ?n\<close>]
                      show False using hcSj_eq02 unfolding hval_gen by linarith
                    qed
                    \<comment> \<open>k \\<noteq> Suc jj. So {k, Suc jj} = {i, Suc i mod n}.
                       Sub-case k=i, Suc jj = Suc i: jj = i \\<ge> k. But k = i, so jj \\<ge> k = i = jj - hmm.
                       Actually: k=i \\<to> Suc jj = Suc i mod n (since k \\<noteq> Suc jj).
                       Suc k mod n = Suc jj? Not necessarily.
                       Let me just use: k \\<noteq> Suc jj and both in {i, Suc i mod n}.\<close>
                    show False
                    proof (cases "?k = i")
                      case True
                      hence "Suc jj = Suc i mod ?n" using hK_ne_Sj hSj_ep2 by (by100 auto)
                      \<comment> \<open>k = i and Suc jj = Suc i mod n. SSj non-endpoint.
                         SSj mod n \\<noteq> i (since SSj \\<noteq> Suc jj = Suc i mod n and ...).
                         Actually, the conclusion cSSj < 0 already applies.
                         Wait, we're not in the SSj-non-endpoint branch here.
                         We need: with ss=0, ttp free, 1-ttp free: phi\\_R(x) = (1-ttp)*v\\_k + ttp*v\\_{SSj}.
                         = (1-ttp)*v\\_i + ttp*v\\_{SSj mod n}. This is on a segment from v\\_i.
                         For this to be on edge i = k: need SSj mod n = Suc i mod n = Suc k mod n.
                         But SSj = Suc(Suc jj) \\<ge> k+2. Suc k mod n = k+1 (k < n-1).
                         SSj mod n = k+1 needs Suc(Suc jj) = k+1 (if < n) or Suc(Suc jj) = n+k+1 (impossible).
                         Suc(Suc jj) = k+1 \\<to> jj = k-1. But jj \\<ge> k. \\<bot>.\<close>
                      \<comment> \<open>Direct: Suc jj = Suc i mod n = Suc k mod n = k+1 (since k < n-1).
                         So jj = k. But sector requires jj \\<ge> k. jj = k is OK.
                         But then ttp = 0 \\<to> cross\\_k(x) = cross\\_diag(x) = 0. \\<bot>? No, ttp isn't forced to 0.
                         Actually, we're in the ss=0 branch. 1-ss-ttp = 1-ttp. If cK \\<noteq> 0: 1-ttp=0.
                         But cK = 0 here! So 1-ttp is free.
                         And cSSj: free too. Actually cSSj is the one being checked.
                         We're in the sub-case cK=0 AND cSj=0 (both endpoints).
                         The ss coefficient is 0 (from case assumption). But 1-ttp and ttp are free.
                         There's no forced zero from {K, SSj} being non-endpoints.
                         Wait: the outer case is that Suc jj is the non-endpoint (case middle).
                         Oh wait, we're in the INNER case of case B (ttp=0), sub-case cK=0, sub-sub-case cSj=0.
                         In this sub-sub-case: ss=0 (from case B's cSSj non-endpoint), ttp=0 (from case B main),
                         so both ss=ttp=0, 1-ss-ttp=1. phi\\_R(x)=v\\_k.
                         But cK=0 means v\\_k is endpoint. And cSj=0 means v\\_{Suc jj} is endpoint.
                         With ss=ttp=0: phi\\_R(x)=v\\_k which is on edge endpoints.
                         And v\\_k being on edges means phi\\_R maps x to v\\_k.
                         From the fan det argument: ss=ttp=0 \\<to> x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.\<close>
                      \<comment> \<open>Wait, ttp=0 (from outer case). ss=0. So both are 0.
                         The fan det argument gives x=v\\_0 \\<to> cross\\_diag=0 \\<to> \\<bot>.
                         But that's the ss=ttp=0 argument from the hcSj\\_z2=False sub-case above.
                         In THIS sub-case (hcSj\\_eq02=True), we have cSj=0, meaning we can't use it to force ss=0.
                         But ss is ALREADY 0 (from the outer h\\_caseSj case). And ttp is ALREADY 0 (from the outer h\\_caseSSj case).
                         So ss=ttp=0 holds, and the x=v\\_0 argument applies.\<close>
                      \<comment> \<open>Actually: re-checking the structure. We're in:
                         - outer: Suc jj is non-endpoint (h\\_caseSj) \\<to> ss=0
                         - middle: SSj is non-endpoint (h\\_caseSSj) \\<to> ttp=0
                         No wait, we're in the THIRD case branch (h\\_caseSSj), not the second.
                         Let me re-read the proof structure.\<close>
                      \<comment> \<open>k=i, cSj=0 \\<to> Suc jj is endpoint \\<to> Suc jj = Suc i mod n (since k=i taken by K).
                         Then jj = i = k. htp0\\_imp gives cross\\_k(x)=0=cross\\_diag \\<to> \\<bot>.\<close>
                      have "Suc jj = Suc i mod ?n"
                        using hK_ne_Sj True hSj_ep2 by (by100 auto)
                      hence "jj = i"
                      proof (cases "i < ?n - 1")
                        case True hence "Suc i mod ?n = Suc i" by (by100 simp)
                        with \<open>Suc jj = Suc i mod ?n\<close> show "jj = i" by (by100 linarith)
                      next
                        case False hence "i = ?n - 1" using hi by (by100 linarith)
                        hence "Suc i = ?n" using hn_ge3 by (by100 linarith)
                        hence "Suc i mod ?n = 0" by (by100 simp)
                        with \<open>Suc jj = Suc i mod ?n\<close> have "Suc jj = 0" by simp
                        thus "jj = i" by (by100 linarith)
                      qed
                      hence "jj = ?k" using True by simp
                      from mp[OF htp0_imp htp_eq0]
                      have "(vx2 ?k - vx2 0)*(snd x - vy2 0) = (vy2 ?k - vy2 0)*(fst x - vx2 0)"
                        using \<open>jj = ?k\<close> by (by100 simp)
                      hence "cross_diag x = 0" unfolding cross_diag_def by (by100 simp)
                      with hcdx show False by linarith
                    next
                      case False
                      hence "?k = Suc i mod ?n" using hK_ep2 by simp
                      show False
                      proof (cases "i < ?n - 1")
                        case True
                        hence "Suc i < ?n" by (by100 linarith)
                        hence "Suc i mod ?n = Suc i" by (by100 simp)
                        hence hk_si: "?k = Suc i" using \<open>?k = Suc i mod ?n\<close> by simp
                        \<comment> \<open>k=Suc i, so i=k-1. Suc jj is endpoint: Suc jj \\<in> {i, Suc i mod n} = {k-1, k}.
                           Suc jj \\<noteq> k (from K\\_ne\\_Sj). So Suc jj = k-1, jj = k-2 < k \\<le> jj. \\<bot>.\<close>
                        have "Suc jj \<in> {i, Suc i mod ?n}" using hSj_ep2 by (by100 blast)
                        hence "Suc jj = i \<or> Suc jj = Suc i mod ?n" by (by100 blast)
                        hence "Suc jj = i" using hK_ne_Sj hk_si True by (by100 auto)
                        hence "jj = ?k - 2" using hk_si by (by100 linarith)
                        hence "jj < ?k" using hk_ge2 by (by100 linarith)
                        with hjjk show False by (by100 linarith)
                      next
                        case False hence "i = ?n - 1" using hi by (by100 linarith)
                        hence "Suc i = ?n" using hn_ge3 by (by100 linarith)
                        hence "Suc i mod ?n = 0" by (by100 simp)
                        hence "?k = 0" using \<open>?k = Suc i mod ?n\<close> by simp
                        with hk_ge2 show False by (by100 linarith)
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
          \<comment> \<open>DIAGONAL IMAGE LEMMA (expert audit 38, Step 1):
             For p on the virtual diagonal (cross\\_diag = 0), phi\\_L(p) lands on old edge 0.
             Proof: p = v\\_0 + t*(v\\_k - v\\_0). LEAST = k-1. Cramer: s=0, tp=t.
             Result: (1-t)*v\\_0 + t*v\\_1 = old edge 0 at parameter t.\<close>
          have hphi_L_diagonal_on_edge: "\<And>p. p \<in> P2 \<Longrightarrow> cross_diag p = 0 \<Longrightarrow>
              \<exists>t\<in>I_set. phi_L p = ((1-t)*vx2 0 + t*vx2(Suc 0 mod ?n),
                                    (1-t)*vy2 0 + t*vy2(Suc 0 mod ?n)) \<and>
              ((fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0) \<longrightarrow>
               (fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k) \<longrightarrow> t \<in> {0<..<(1::real)})"
          proof -
            fix p assume hp: "p \<in> P2" and hcd: "cross_diag p = 0"
            show "\<exists>t\<in>I_set. phi_L p = ((1-t)*vx2 0 + t*vx2(Suc 0 mod ?n),
                                        (1-t)*vy2 0 + t*vy2(Suc 0 mod ?n)) \<and>
              ((fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0) \<longrightarrow>
               (fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k) \<longrightarrow> t \<in> {0<..<(1::real)})"
            proof (cases "fst p = vx2 0 \<and> snd p = vy2 0")
              case True
              \<comment> \<open>p = v\\_0. phi\\_L(v\\_0) = v\\_0 = edge\\_0(0).\<close>
              have "phi_L p = phi_L (vx2 0, vy2 0)" using True by (cases p) simp
              also have "\<dots> = (vx2 0, vy2 0)" using hphi_L_v0 .
              also have "\<dots> = ((1-0)*vx2 0 + 0*vx2(Suc 0 mod ?n), (1-0)*vy2 0 + 0*vy2(Suc 0 mod ?n))"
                by simp
              finally have "phi_L p = ((1-(0::real))*vx2 0 + 0*vx2(Suc 0 mod ?n),
                                        (1-0)*vy2 0 + 0*vy2(Suc 0 mod ?n))" .
              moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
              moreover have "fst p = vx2 0 \<and> snd p = vy2 0" using True by (cases p) simp
              ultimately show ?thesis by (by100 blast)
            next
              case hne0: False
              show ?thesis
              proof (cases "fst p = vx2 ?k \<and> snd p = vy2 ?k")
                case True
                \<comment> \<open>p = v\\_k. phi\\_L(v\\_k) = v\\_1 = edge\\_0(1).\<close>
                have "phi_L p = phi_L (vx2 ?k, vy2 ?k)" using True by (cases p) simp
                also have "\<dots> = (vx2 1, vy2 1)" using hphi_L_vk_val .
                also have "\<dots> = ((1-1)*vx2 0 + 1*vx2(Suc 0 mod ?n), (1-1)*vy2 0 + 1*vy2(Suc 0 mod ?n))"
                  using hn_ge3 by simp
                finally have "phi_L p = ((1-(1::real))*vx2 0 + 1*vx2(Suc 0 mod ?n),
                                          (1-1)*vy2 0 + 1*vy2(Suc 0 mod ?n))" .
                moreover have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                moreover have "fst p = vx2 ?k \<and> snd p = vy2 ?k"
                  using \<open>fst p = vx2 ?k \<and> snd p = vy2 ?k\<close> .
                ultimately show ?thesis by (by100 blast)
              next
                case hnek: False
                \<comment> \<open>p strictly between v\\_0 and v\\_k on diagonal. LEAST=k-1, Cramer s=0, tp=\\<tau>.\<close>
                \<comment> \<open>p on diagonal interior: extract parameter \\<tau> and compute phi\\_L.\<close>
                \<comment> \<open>cross\\_diag = 0 and p \\<in> P2 with p \\<noteq> v\\_0, p \\<noteq> v\\_k means
                   p = (1-\\<tau>)*v\\_0 + \\<tau>*v\\_k for some 0 < \\<tau> < 1.\<close>
                \<comment> \<open>Then LEAST = k-1, Cramer s=0, tp=\\<tau>, phi\\_L = (1-\\<tau>)*v\\_0 + \\<tau>*v\\_1.\<close>
                \<comment> \<open>The computation mirrors hphi\\_L\\_sigma for left boundary edges.\<close>
                have "\<exists>\<tau>. \<tau> > 0 \<and> \<tau> < 1 \<and> fst p = (1-\<tau>)*vx2 0 + \<tau>*vx2 ?k \<and>
                           snd p = (1-\<tau>)*vy2 0 + \<tau>*vy2 ?k"
                proof -
                  \<comment> \<open>cross\\_diag = 0 means (fst p - vx2 0, snd p - vy2 0) parallel to (vx2 k - vx2 0, vy2 k - vy2 0).\<close>
                  have hcd_eq: "(vx2 ?k - vx2 0)*(snd p - vy2 0) = (vy2 ?k - vy2 0)*(fst p - vx2 0)"
                    using hcd unfolding cross_diag_def by (by100 linarith)
                  \<comment> \<open>v\\_0 \\<noteq> v\\_k from C3.\<close>
                  have "0 < ?n" using hn_ge3 by (by100 linarith)
                  have "?k < ?n" by (by100 simp)
                  from hC3_2[rule_format, OF \<open>0 < ?n\<close> \<open>?k < ?n\<close>]
                  have hvne: "(vx2 0, vy2 0) \<noteq> (vx2 ?k, vy2 ?k)" using hk_ge2 by (by100 simp)
                  hence "vx2 0 \<noteq> vx2 ?k \<or> vy2 0 \<noteq> vy2 ?k" by (by100 auto)
                  \<comment> \<open>L functional: fan\\_det(1,k) > 0 and L(p) \\<ge> 0 for all p \\<in> P2.
                     Used in both True/False cases to prove \\<tau> > 0.\<close>
                  have hfd1k: "(vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0) > 0"
                  proof -
                    have "1 < ?n" using hn_ge3 by (by100 linarith)
                    from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> \<open>?k < ?n\<close>]
                    show ?thesis using hk_ge2 by (by100 linarith)
                  qed
                  have hLp_nn: "(vx2 1 - vx2 0) * (snd p - vy2 0) - (vy2 1 - vy2 0) * (fst p - vx2 0) \<ge> 0"
                  proof -
                    have "p \<in> P2" using hp .
                    hence "\<exists>cfs. (\<forall>j<?n. cfs j \<ge> 0) \<and> (\<Sum>j<?n. cfs j) = 1 \<and>
                      fst p = (\<Sum>j<?n. cfs j * vx2 j) \<and> snd p = (\<Sum>j<?n. cfs j * vy2 j)"
                      using hC5_2 by (by5000 auto)
                    then obtain cfs where
                      hcg: "\<forall>j<?n. cfs j \<ge> 0"
                      and hcs: "(\<Sum>j<?n. cfs j) = 1"
                      and hcx: "fst p = (\<Sum>j<?n. cfs j * vx2 j)"
                      and hcy: "snd p = (\<Sum>j<?n. cfs j * vy2 j)"
                      by (by100 blast)
                    have hsy: "(\<Sum>j<?n. cfs j * (vy2 j - vy2 0)) = snd p - vy2 0"
                    proof -
                      have "(\<Sum>j<?n. cfs j * (vy2 j - vy2 0)) = (\<Sum>j<?n. cfs j * vy2 j + cfs j * (- vy2 0))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = (\<Sum>j<?n. cfs j * vy2 j) + (\<Sum>j<?n. cfs j * (- vy2 0))"
                        by (rule sum.distrib)
                      also have "(\<Sum>j<?n. cfs j * (- vy2 0)) = - vy2 0 * (\<Sum>j<?n. cfs j)"
                        by (simp only: mult.commute[of _ "- vy2 0"] sum_distrib_left[symmetric])
                      finally show ?thesis using hcy hcs by (by100 simp)
                    qed
                    have hsx: "(\<Sum>j<?n. cfs j * (vx2 j - vx2 0)) = fst p - vx2 0"
                    proof -
                      have "(\<Sum>j<?n. cfs j * (vx2 j - vx2 0)) = (\<Sum>j<?n. cfs j * vx2 j + cfs j * (- vx2 0))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = (\<Sum>j<?n. cfs j * vx2 j) + (\<Sum>j<?n. cfs j * (- vx2 0))"
                        by (rule sum.distrib)
                      also have "(\<Sum>j<?n. cfs j * (- vx2 0)) = - vx2 0 * (\<Sum>j<?n. cfs j)"
                        by (simp only: mult.commute[of _ "- vx2 0"] sum_distrib_left[symmetric])
                      finally show ?thesis using hcx hcs by (by100 simp)
                    qed
                    have "(vx2 1 - vx2 0) * (snd p - vy2 0) - (vy2 1 - vy2 0) * (fst p - vx2 0) =
                      (vx2 1 - vx2 0) * (\<Sum>j<?n. cfs j * (vy2 j - vy2 0)) -
                      (vy2 1 - vy2 0) * (\<Sum>j<?n. cfs j * (vx2 j - vx2 0))"
                      using hsy hsx by (by100 simp)
                    also have "\<dots> = (\<Sum>j<?n. (vx2 1 - vx2 0) * (cfs j * (vy2 j - vy2 0))) -
                      (\<Sum>j<?n. (vy2 1 - vy2 0) * (cfs j * (vx2 j - vx2 0)))"
                      by (simp only: sum_distrib_left)
                    also have "\<dots> = (\<Sum>j<?n. (vx2 1 - vx2 0) * (cfs j * (vy2 j - vy2 0)) -
                      (vy2 1 - vy2 0) * (cfs j * (vx2 j - vx2 0)))"
                      by (rule sum_subtractf[symmetric])
                    also have "\<dots> = (\<Sum>j<?n. cfs j * ((vx2 1 - vx2 0) * (vy2 j - vy2 0) -
                      (vy2 1 - vy2 0) * (vx2 j - vx2 0)))"
                    proof -
                      have hfact: "\<And>x. (vx2 1 - vx2 0) * (cfs x * (vy2 x - vy2 0)) -
                        (vy2 1 - vy2 0) * (cfs x * (vx2 x - vx2 0)) =
                        cfs x * ((vx2 1 - vx2 0) * (vy2 x - vy2 0) -
                        (vy2 1 - vy2 0) * (vx2 x - vx2 0))"
                      proof -
                        fix x
                        have "(vx2 1 - vx2 0) * (cfs x * (vy2 x - vy2 0)) -
                          (vy2 1 - vy2 0) * (cfs x * (vx2 x - vx2 0)) =
                          cfs x * ((vx2 1 - vx2 0) * (vy2 x - vy2 0)) -
                          cfs x * ((vy2 1 - vy2 0) * (vx2 x - vx2 0))"
                          by (by100 simp)
                        also have "\<dots> = cfs x * ((vx2 1 - vx2 0) * (vy2 x - vy2 0) -
                          (vy2 1 - vy2 0) * (vx2 x - vx2 0))"
                          using right_diff_distrib[symmetric, of "cfs x"]
                          by (by100 simp)
                        finally show "(vx2 1 - vx2 0) * (cfs x * (vy2 x - vy2 0)) -
                          (vy2 1 - vy2 0) * (cfs x * (vx2 x - vx2 0)) =
                          cfs x * ((vx2 1 - vx2 0) * (vy2 x - vy2 0) -
                          (vy2 1 - vy2 0) * (vx2 x - vx2 0))" .
                      qed
                      show ?thesis using hfact by (intro sum.cong) (by100 simp)+
                    qed
                    finally have hLs: "(vx2 1 - vx2 0) * (snd p - vy2 0) - (vy2 1 - vy2 0) * (fst p - vx2 0) =
                      (\<Sum>j<?n. cfs j * ((vx2 1 - vx2 0) * (vy2 j - vy2 0) - (vy2 1 - vy2 0) * (vx2 j - vx2 0)))" .
                    have "\<And>j. j \<in> {..<?n} \<Longrightarrow>
                      cfs j * ((vx2 1 - vx2 0) * (vy2 j - vy2 0) - (vy2 1 - vy2 0) * (vx2 j - vx2 0)) \<ge> 0"
                    proof -
                      fix j assume "j \<in> {..<?n}"
                      hence hj: "j < ?n" by (by100 simp)
                      have hcj: "cfs j \<ge> 0" using hcg hj by (by100 simp)
                      have hfd: "(vx2 1 - vx2 0) * (vy2 j - vy2 0) - (vy2 1 - vy2 0) * (vx2 j - vx2 0) \<ge> 0"
                      proof (cases "j \<le> 1")
                        case True
                        thus ?thesis
                        proof (cases "j = 0")
                          case True thus ?thesis by (by100 simp)
                        next
                          case False with \<open>j \<le> 1\<close> have "j = 1" by (by100 linarith)
                          thus ?thesis by (by100 simp)
                        qed
                      next
                        case False
                        hence "1 < j" by (by100 linarith)
                        have "1 < ?n" using hn_ge3 by (by100 linarith)
                        from hfan_det_0[rule_format, OF \<open>1 < ?n\<close> hj]
                        show ?thesis using \<open>1 < j\<close> by (by100 force)
                      qed
                      from hcj hfd show "cfs j * ((vx2 1 - vx2 0) * (vy2 j - vy2 0) - (vy2 1 - vy2 0) * (vx2 j - vx2 0)) \<ge> 0"
                        by (rule mult_nonneg_nonneg)
                    qed
                    hence "(\<Sum>j<?n. cfs j * ((vx2 1 - vx2 0) * (vy2 j - vy2 0) - (vy2 1 - vy2 0) * (vx2 j - vx2 0))) \<ge> 0"
                      by (rule sum_nonneg)
                    with hLs show ?thesis by (by100 linarith)
                  qed
                  \<comment> \<open>M functional: cross(p - v\\_{k-1}, v\\_k - v\\_{k-1}) \\<le> 0 for p \\<in> P2.
                     From C11 at edge k-1: all non-adjacent vertices on interior side.
                     Used to prove \\<tau> \\<le> 1.\<close>
                  have hMd1k: "(vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) < 0"
                  proof -
                    have hkm1: "?k - 1 < ?n" using hk_ge2 by (by100 simp)
                    have h0n: "(0::nat) < ?n" using hn_ge3 by (by100 linarith)
                    have h0_ne_km1: "(0::nat) \<noteq> ?k - 1" using hk_ge2 by (by100 linarith)
                    have hSuc_km1: "Suc (?k - 1) mod ?n = ?k"
                    proof -
                      have "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                      moreover have "?k < ?n" by (by100 simp)
                      ultimately show ?thesis by (by100 simp)
                    qed
                    have h0_ne_k: "(0::nat) \<noteq> ?k" using hk_ge2 by (by100 linarith)
                    from hC11_2[rule_format, OF hkm1 h0n h0_ne_km1]
                    have "(vx2 0 - vx2 (?k - 1)) * (vy2 (Suc (?k - 1) mod ?n) - vy2 (?k - 1)) -
                      (vy2 0 - vy2 (?k - 1)) * (vx2 (Suc (?k - 1) mod ?n) - vx2 (?k - 1)) < 0"
                      using h0_ne_k hSuc_km1 by (by100 force)
                    thus ?thesis using hSuc_km1 by (by100 simp)
                  qed
                  have hMp_le0: "(fst p - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (snd p - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) \<le> 0"
                  proof -
                    have "p \<in> P2" using hp .
                    hence "\<exists>cfs2. (\<forall>j<?n. cfs2 j \<ge> 0) \<and> (\<Sum>j<?n. cfs2 j) = 1 \<and>
                      fst p = (\<Sum>j<?n. cfs2 j * vx2 j) \<and> snd p = (\<Sum>j<?n. cfs2 j * vy2 j)"
                      using hC5_2 by (by5000 auto)
                    then obtain cfs2 where
                      hcg2: "\<forall>j<?n. cfs2 j \<ge> 0"
                      and hcs2: "(\<Sum>j<?n. cfs2 j) = 1"
                      and hcx2: "fst p = (\<Sum>j<?n. cfs2 j * vx2 j)"
                      and hcy2: "snd p = (\<Sum>j<?n. cfs2 j * vy2 j)"
                      by (by100 blast)
                    \<comment> \<open>Express coordinate sums shifted by v\\_{k-1}.\<close>
                    have hsy2: "(\<Sum>j<?n. cfs2 j * (vy2 j - vy2(?k-1))) = snd p - vy2(?k-1)"
                    proof -
                      have "(\<Sum>j<?n. cfs2 j * (vy2 j - vy2(?k-1))) = (\<Sum>j<?n. cfs2 j * vy2 j + cfs2 j * (- vy2(?k-1)))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = (\<Sum>j<?n. cfs2 j * vy2 j) + (\<Sum>j<?n. cfs2 j * (- vy2(?k-1)))"
                        by (rule sum.distrib)
                      also have "(\<Sum>j<?n. cfs2 j * (- vy2(?k-1))) = - vy2(?k-1) * (\<Sum>j<?n. cfs2 j)"
                        by (simp only: mult.commute[of _ "- vy2(?k-1)"] sum_distrib_left[symmetric])
                      finally show ?thesis using hcy2 hcs2 by (by100 simp)
                    qed
                    have hsx2: "(\<Sum>j<?n. cfs2 j * (vx2 j - vx2(?k-1))) = fst p - vx2(?k-1)"
                    proof -
                      have "(\<Sum>j<?n. cfs2 j * (vx2 j - vx2(?k-1))) = (\<Sum>j<?n. cfs2 j * vx2 j + cfs2 j * (- vx2(?k-1)))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = (\<Sum>j<?n. cfs2 j * vx2 j) + (\<Sum>j<?n. cfs2 j * (- vx2(?k-1)))"
                        by (rule sum.distrib)
                      also have "(\<Sum>j<?n. cfs2 j * (- vx2(?k-1))) = - vx2(?k-1) * (\<Sum>j<?n. cfs2 j)"
                        by (simp only: mult.commute[of _ "- vx2(?k-1)"] sum_distrib_left[symmetric])
                      finally show ?thesis using hcx2 hcs2 by (by100 simp)
                    qed
                    \<comment> \<open>M(p) = \\<Sigma> cfs2 j * M(v\\_j).\<close>
                    have "(fst p - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (snd p - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) =
                      (vy2 ?k - vy2(?k-1)) * (\<Sum>j<?n. cfs2 j * (vx2 j - vx2(?k-1))) -
                      (vx2 ?k - vx2(?k-1)) * (\<Sum>j<?n. cfs2 j * (vy2 j - vy2(?k-1)))"
                      using hsx2 hsy2 by (by100 simp)
                    also have "\<dots> = (\<Sum>j<?n. (vy2 ?k - vy2(?k-1)) * (cfs2 j * (vx2 j - vx2(?k-1)))) -
                      (\<Sum>j<?n. (vx2 ?k - vx2(?k-1)) * (cfs2 j * (vy2 j - vy2(?k-1))))"
                      by (simp only: sum_distrib_left)
                    also have "\<dots> = (\<Sum>j<?n. (vy2 ?k - vy2(?k-1)) * (cfs2 j * (vx2 j - vx2(?k-1))) -
                      (vx2 ?k - vx2(?k-1)) * (cfs2 j * (vy2 j - vy2(?k-1))))"
                      by (rule sum_subtractf[symmetric])
                    also have "\<dots> = (\<Sum>j<?n. cfs2 j * ((vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) -
                      (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))))"
                    proof -
                      have hfact2: "\<And>x. (vy2 ?k - vy2(?k-1)) * (cfs2 x * (vx2 x - vx2(?k-1))) -
                        (vx2 ?k - vx2(?k-1)) * (cfs2 x * (vy2 x - vy2(?k-1))) =
                        cfs2 x * ((vx2 x - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) -
                        (vy2 x - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))"
                      proof -
                        fix x
                        have "(vy2 ?k - vy2(?k-1)) * (cfs2 x * (vx2 x - vx2(?k-1))) -
                          (vx2 ?k - vx2(?k-1)) * (cfs2 x * (vy2 x - vy2(?k-1))) =
                          cfs2 x * ((vy2 ?k - vy2(?k-1)) * (vx2 x - vx2(?k-1))) -
                          cfs2 x * ((vx2 ?k - vx2(?k-1)) * (vy2 x - vy2(?k-1)))"
                          by (by100 simp)
                        also have "\<dots> = cfs2 x * ((vx2 x - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) -
                          (vy2 x - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))"
                          using right_diff_distrib[symmetric, of "cfs2 x"]
                          by (by100 simp)
                        finally show "(vy2 ?k - vy2(?k-1)) * (cfs2 x * (vx2 x - vx2(?k-1))) -
                          (vx2 ?k - vx2(?k-1)) * (cfs2 x * (vy2 x - vy2(?k-1))) =
                          cfs2 x * ((vx2 x - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) -
                          (vy2 x - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))" .
                      qed
                      show ?thesis using hfact2 by (intro sum.cong) (by100 simp)+
                    qed
                    finally have hMs: "(fst p - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (snd p - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) =
                      (\<Sum>j<?n. cfs2 j * ((vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))))" .
                    \<comment> \<open>Each term \\<le> 0 by C11 at edge k-1.\<close>
                    have "\<And>j. j \<in> {..<?n} \<Longrightarrow>
                      cfs2 j * ((vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) \<le> 0"
                    proof -
                      fix j assume "j \<in> {..<?n}"
                      hence hj: "j < ?n" by (by100 simp)
                      have hcj: "cfs2 j \<ge> 0" using hcg2 hj by (by100 simp)
                      show "cfs2 j * ((vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) \<le> 0"
                      proof (cases "j = ?k - 1 \<or> j = ?k")
                        case True
                        hence "(vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) = 0"
                        proof
                          assume "j = ?k - 1" thus ?thesis by (by100 simp)
                        next
                          assume "j = ?k" thus ?thesis by (by100 simp)
                        qed
                        thus ?thesis by (by100 simp)
                      next
                        case False
                        hence hj_ne: "j \<noteq> ?k - 1" "j \<noteq> ?k" by (by100 simp)+
                        have hkm1: "?k - 1 < ?n" using hk_ge2 by (by100 simp)
                        have hSuc_km1: "Suc (?k - 1) mod ?n = ?k"
                        proof -
                          have "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                          moreover have "?k < ?n" by (by100 simp)
                          ultimately show ?thesis by (by100 simp)
                        qed
                        from hC11_2[rule_format, OF hkm1 hj hj_ne(1)]
                        have "(vx2 j - vx2(?k-1)) * (vy2(Suc(?k-1) mod ?n) - vy2(?k-1)) -
                          (vy2 j - vy2(?k-1)) * (vx2(Suc(?k-1) mod ?n) - vx2(?k-1)) < 0"
                          using hj_ne(2) hSuc_km1 by (by100 force)
                        hence "(vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) < 0"
                          using hSuc_km1 by (by100 simp)
                        hence "(vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) \<le> 0"
                          by (by100 linarith)
                        with hcj show ?thesis using mult_nonneg_nonpos by (by100 fastforce)
                      qed
                    qed
                    hence "(\<Sum>j<?n. cfs2 j * ((vx2 j - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 j - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))) \<le> 0"
                      by (intro sum_nonpos) (by100 simp)
                    with hMs show ?thesis by (by100 linarith)
                  qed
                  \<comment> \<open>Case split: extract \\<tau> from the non-zero coordinate.\<close>
                  show ?thesis
                  proof (cases "vx2 ?k \<noteq> vx2 0")
                    case True
                    define \<tau> where "\<tau> = (fst p - vx2 0) / (vx2 ?k - vx2 0)"
                    have hfst: "fst p - vx2 0 = \<tau> * (vx2 ?k - vx2 0)"
                      unfolding \<tau>_def using True by (by100 simp)
                    hence hfst_eq: "fst p = (1-\<tau>)*vx2 0 + \<tau>*vx2 ?k" by (by100 algebra)
                    have hsnd_eq: "snd p = (1-\<tau>)*vy2 0 + \<tau>*vy2 ?k"
                    proof -
                      from hcd_eq hfst have "(vx2 ?k - vx2 0)*(snd p - vy2 0) = (vy2 ?k - vy2 0)*(\<tau>*(vx2 ?k - vx2 0))"
                        by (by100 simp)
                      hence "(vx2 ?k - vx2 0)*(snd p - vy2 0) = \<tau>*(vy2 ?k - vy2 0)*(vx2 ?k - vx2 0)"
                        by (by100 algebra)
                      hence "snd p - vy2 0 = \<tau>*(vy2 ?k - vy2 0)" using True by (by100 simp)
                      thus ?thesis by (by100 algebra)
                    qed
                    \<comment> \<open>Bounds: \\<tau> > 0 from p \\<noteq> v\\_0, \\<tau> < 1 from p \\<noteq> v\\_k.\<close>
                    have "fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0" using hne0 by (by100 simp)
                    hence "\<tau> \<noteq> 0" using hfst_eq hsnd_eq by (by100 auto)
                    have "fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k" using hnek by (by100 simp)
                    hence "\<tau> \<noteq> 1" using hfst_eq hsnd_eq by (by100 auto)
                    \<comment> \<open>\\<tau> \\<in> (0,1) from p \\<in> P2 (convex hull between v\\_0 and v\\_k).\<close>
                    \<comment> \<open>\\<tau> \\<in> [0,1] from p \\<in> P2 via cross\\_diag sign analysis.
                       p = \\<Sigma> \\<alpha>\\_j * v\\_j. cross\\_diag(p) = \\<Sigma> \\<alpha>\\_j * cross\\_diag(v\\_j) = 0.
                       For j with 1\\<le>j<k: cross\\_diag(v\\_j) < 0 (from fan\\_det antisymmetry).
                       For j with k<j<n: cross\\_diag(v\\_j) > 0 (from fan\\_det).
                       So all \\<alpha>\\_j = 0 for j \\<notin> \\{0,k\\}. Hence p = \\<alpha>\\_0*v\\_0 + \\<alpha>\\_k*v\\_k
                       with \\<alpha>\\_0+\\<alpha>\\_k=1, giving \\<tau>=\\<alpha>\\_k \\<in> [0,1].\<close>
                    have "\<tau> > 0 \<and> \<tau> < 1"
                    proof -
                      \<comment> \<open>Cross\\_diag at each vertex.\<close>
                      have hcd_v0: "cross_diag (vx2 0, vy2 0) = 0" unfolding cross_diag_def by (by100 simp)
                      have hcd_vk: "cross_diag (vx2 ?k, vy2 ?k) = 0"
                      proof -
                        have "(vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0) = 0"
                          by (by100 algebra)
                        thus ?thesis unfolding cross_diag_def by (by100 simp)
                      qed
                      have hcd_left_v: "\<And>j. 1 \<le> j \<Longrightarrow> j < ?k \<Longrightarrow> cross_diag (vx2 j, vy2 j) < 0"
                      proof -
                        fix j :: nat assume hj1: "1 \<le> j" and hjk: "j < ?k"
                        have "j < ?n" using hjk by (by100 simp)
                        have "?k < ?n" by (by100 simp)
                        from hfan_det_0[rule_format, OF \<open>j < ?n\<close> \<open>?k < ?n\<close> hj1 hjk]
                        have "(vx2 j - vx2 0)*(vy2 ?k - vy2 0) - (vy2 j - vy2 0)*(vx2 ?k - vx2 0) > 0" .
                        moreover have "cross_diag (vx2 j, vy2 j) =
                          (vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)"
                          unfolding cross_diag_def by (by100 simp)
                        moreover have "(vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0) =
                          -((vx2 j - vx2 0)*(vy2 ?k - vy2 0) - (vy2 j - vy2 0)*(vx2 ?k - vx2 0))"
                          by (by100 algebra)
                        ultimately show "cross_diag (vx2 j, vy2 j) < 0" by (by100 linarith)
                      qed
                      have hcd_right_v: "\<And>j. ?k < j \<Longrightarrow> j < ?n \<Longrightarrow> cross_diag (vx2 j, vy2 j) > 0"
                      proof -
                        fix j :: nat assume hkj: "?k < j" and hjn: "j < ?n"
                        have "?k < ?n" by (by100 simp)
                        have "1 \<le> ?k" using hk_ge2 by (by100 linarith)
                        from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> hjn \<open>1 \<le> ?k\<close> hkj]
                        have "cross_diag (vx2 j, vy2 j) =
                          (vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)"
                          unfolding cross_diag_def by (by100 simp)
                        thus "cross_diag (vx2 j, vy2 j) > 0"
                          using hfan_det_0[rule_format, OF \<open>?k < ?n\<close> hjn \<open>1 \<le> ?k\<close> hkj] by (by100 linarith)
                      qed
                      \<comment> \<open>p \\<in> P2: get coefficients.\<close>
                      have "p \<in> P2" using hp .
                      hence "\<exists>coeffs. (\<forall>j<?n. coeffs j \<ge> 0) \<and> (\<Sum>j<?n. coeffs j) = 1 \<and>
                        fst p = (\<Sum>j<?n. coeffs j * vx2 j) \<and> snd p = (\<Sum>j<?n. coeffs j * vy2 j)"
                        using hC5_2 by (by5000 auto)
                      then obtain coeffs where
                        hcoeffs_ge: "\<forall>j<?n. coeffs j \<ge> 0"
                        and hcoeffs_sum: "(\<Sum>j<?n. coeffs j) = 1"
                        and hcoeffs_x: "fst p = (\<Sum>j<?n. coeffs j * vx2 j)"
                        and hcoeffs_y: "snd p = (\<Sum>j<?n. coeffs j * vy2 j)"
                        by (by100 blast)
                      \<comment> \<open>cross\\_diag(p) = \\<Sigma> coeffs(j) * cross\\_diag(v\\_j) = 0.\<close>
                      have hcd_sum: "(\<Sum>j<?n. coeffs j * cross_diag (vx2 j, vy2 j)) = 0"
                      proof -
                        \<comment> \<open>Unfold cross\\_diag and distribute the sum.\<close>
                        have "\<And>j. coeffs j * cross_diag (vx2 j, vy2 j) =
                          coeffs j * ((vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0))"
                          unfolding cross_diag_def by (by100 simp)
                        hence "(\<Sum>j<?n. coeffs j * cross_diag (vx2 j, vy2 j)) =
                          (\<Sum>j<?n. coeffs j * ((vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)))"
                          by (intro sum.cong) (by100 simp)+
                        also have "\<dots> = (vx2 ?k - vx2 0) * (\<Sum>j<?n. coeffs j * (vy2 j - vy2 0))
                                      - (vy2 ?k - vy2 0) * (\<Sum>j<?n. coeffs j * (vx2 j - vx2 0))"
                        proof -
                          have "\<And>j. coeffs j * ((vx2 ?k - vx2 0) * (vy2 j - vy2 0) - (vy2 ?k - vy2 0) * (vx2 j - vx2 0))
                            = (vx2 ?k - vx2 0) * (coeffs j * (vy2 j - vy2 0)) - (vy2 ?k - vy2 0) * (coeffs j * (vx2 j - vx2 0))"
                            by (by100 algebra)
                          hence "(\<Sum>j<?n. coeffs j * ((vx2 ?k - vx2 0)*(vy2 j - vy2 0) - (vy2 ?k - vy2 0)*(vx2 j - vx2 0)))
                            = (\<Sum>j<?n. (vx2 ?k - vx2 0) * (coeffs j * (vy2 j - vy2 0)) - (vy2 ?k - vy2 0) * (coeffs j * (vx2 j - vx2 0)))"
                            by (intro sum.cong) (by100 simp)+
                          also have "\<dots> = (\<Sum>j<?n. (vx2 ?k - vx2 0) * (coeffs j * (vy2 j - vy2 0)))
                            - (\<Sum>j<?n. (vy2 ?k - vy2 0) * (coeffs j * (vx2 j - vx2 0)))"
                            by (rule sum_subtractf)
                          also have "\<dots> = (vx2 ?k - vx2 0) * (\<Sum>j<?n. coeffs j * (vy2 j - vy2 0))
                            - (vy2 ?k - vy2 0) * (\<Sum>j<?n. coeffs j * (vx2 j - vx2 0))"
                            by (simp only: sum_distrib_left[symmetric])
                          finally show ?thesis .
                        qed
                        also have "\<dots> = (vx2 ?k - vx2 0) * (snd p - vy2 0)
                                      - (vy2 ?k - vy2 0) * (fst p - vx2 0)"
                        proof -
                          have hsy: "(\<Sum>j<?n. coeffs j * (vy2 j - vy2 0)) = snd p - vy2 0"
                          proof -
                            have "(\<Sum>j<?n. coeffs j * (vy2 j - vy2 0)) = (\<Sum>j<?n. coeffs j * vy2 j + coeffs j * (- vy2 0))"
                              by (simp add: algebra_simps)
                            also have "\<dots> = (\<Sum>j<?n. coeffs j * vy2 j) + (\<Sum>j<?n. coeffs j * (- vy2 0))"
                              by (rule sum.distrib)
                            also have "(\<Sum>j<?n. coeffs j * (- vy2 0)) = - vy2 0 * (\<Sum>j<?n. coeffs j)"
                              by (simp only: mult.commute[of _ "- vy2 0"] sum_distrib_left[symmetric])
                            finally show ?thesis using hcoeffs_y hcoeffs_sum by (by100 simp)
                          qed
                          have hsx: "(\<Sum>j<?n. coeffs j * (vx2 j - vx2 0)) = fst p - vx2 0"
                          proof -
                            have "(\<Sum>j<?n. coeffs j * (vx2 j - vx2 0)) = (\<Sum>j<?n. coeffs j * vx2 j + coeffs j * (- vx2 0))"
                              by (simp add: algebra_simps)
                            also have "\<dots> = (\<Sum>j<?n. coeffs j * vx2 j) + (\<Sum>j<?n. coeffs j * (- vx2 0))"
                              by (rule sum.distrib)
                            also have "(\<Sum>j<?n. coeffs j * (- vx2 0)) = - vx2 0 * (\<Sum>j<?n. coeffs j)"
                              by (simp only: mult.commute[of _ "- vx2 0"] sum_distrib_left[symmetric])
                            finally show ?thesis using hcoeffs_x hcoeffs_sum by (by100 simp)
                          qed
                          show ?thesis using hsy hsx by (by100 simp)
                        qed
                        also have "\<dots> = cross_diag p" unfolding cross_diag_def by (by100 simp)
                        also have "\<dots> = 0" using hcd .
                        finally show ?thesis .
                      qed
                      \<comment> \<open>\\<tau> > 0 via supporting hyperplane (L functional at v\\_0).
                         L(p) = \\<tau> * fan\\_det(1,k), with L(p) \\<ge> 0 (hLp\\_nn) and fan\\_det > 0.\<close>
                      have htau_pos: "\<tau> > 0"
                      proof -
                        have "(vx2 1 - vx2 0) * (snd p - vy2 0) - (vy2 1 - vy2 0) * (fst p - vx2 0) =
                          \<tau> * ((vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0))"
                          using hfst_eq hsnd_eq by (by100 algebra)
                        hence "\<tau> * ((vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0)) \<ge> 0"
                          using hLp_nn by (by100 linarith)
                        hence "(0 \<le> \<tau> \<and> 0 \<le> (vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0)) \<or>
                          (\<tau> \<le> 0 \<and> (vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0) \<le> 0)"
                          using zero_le_mult_iff by (by100 blast)
                        with hfd1k have "\<tau> \<ge> 0" by (by100 linarith)
                        with \<open>\<tau> \<noteq> 0\<close> show "\<tau> > 0" by (by100 linarith)
                      qed
                      \<comment> \<open>\\<tau> < 1 via C11 supporting hyperplane at v\\_k (edge k-1).
                         M(p) = (1-\\<tau>)*M(v\\_0) with M(v\\_0) < 0 and M(p) \\<le> 0 \\<to> 1-\\<tau> \\<ge> 0.\<close>
                      have "\<tau> < 1"
                      proof -
                        have "(fst p - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (snd p - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) =
                          (1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))"
                          using hfst_eq hsnd_eq by (by100 algebra)
                        hence hMt_le: "(1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) \<le> 0"
                          using hMp_le0 by (by100 linarith)
                        \<comment> \<open>If 1-\\<tau> < 0: (negative)*(negative from hMd1k) = positive, contradicting \\<le> 0.\<close>
                        have "1-\<tau> \<ge> 0"
                        proof (rule ccontr)
                          assume "\<not> (0 \<le> 1 - \<tau>)"
                          hence "1 - \<tau> < 0" by (by100 linarith)
                          from mult_neg_neg[OF \<open>1 - \<tau> < 0\<close> hMd1k]
                          have "(1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) > 0" .
                          with hMt_le show False by (by100 linarith)
                        qed
                        hence "\<tau> \<le> 1" by (by100 linarith)
                        with \<open>\<tau> \<noteq> 1\<close> show "\<tau> < 1" by (by100 linarith)
                      qed
                      with htau_pos show "\<tau> > 0 \<and> \<tau> < 1" by (by100 linarith)
                    qed
                    with hfst_eq hsnd_eq show ?thesis by (by100 blast)
                  next
                    case False hence "vy2 ?k \<noteq> vy2 0" using \<open>vx2 0 \<noteq> vx2 ?k \<or> vy2 0 \<noteq> vy2 ?k\<close> by (by100 simp)
                    define \<tau> where "\<tau> = (snd p - vy2 0) / (vy2 ?k - vy2 0)"
                    have hsnd: "snd p - vy2 0 = \<tau> * (vy2 ?k - vy2 0)"
                      unfolding \<tau>_def using \<open>vy2 ?k \<noteq> vy2 0\<close> by (by100 simp)
                    hence hsnd_eq: "snd p = (1-\<tau>)*vy2 0 + \<tau>*vy2 ?k" by (by100 algebra)
                    have hfst_eq: "fst p = (1-\<tau>)*vx2 0 + \<tau>*vx2 ?k"
                    proof -
                      have "vx2 ?k = vx2 0" using False by (by100 simp)
                      hence "fst p = vx2 0" using hcd_eq \<open>vy2 ?k \<noteq> vy2 0\<close> by (by100 simp)
                      have "(1-\<tau>)*vx2 0 + \<tau>*vx2 ?k = (1-\<tau>)*vx2 0 + \<tau>*vx2 0"
                        using \<open>vx2 ?k = vx2 0\<close> by (by100 simp)
                      also have "\<dots> = vx2 0" by (simp add: algebra_simps)
                      finally show ?thesis using \<open>fst p = vx2 0\<close> by (by100 simp)
                    qed
                    have "\<tau> \<noteq> 0" using hne0 hsnd_eq hfst_eq by (by100 auto)
                    have "\<tau> \<noteq> 1" using hnek hsnd_eq hfst_eq by (by100 auto)
                    have "\<tau> > 0 \<and> \<tau> < 1"
                    proof -
                      have "(vx2 1 - vx2 0) * (snd p - vy2 0) - (vy2 1 - vy2 0) * (fst p - vx2 0) =
                        \<tau> * ((vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0))"
                        using hfst_eq hsnd_eq by (by100 algebra)
                      hence "\<tau> * ((vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0)) \<ge> 0"
                        using hLp_nn by (by100 linarith)
                      hence "(0 \<le> \<tau> \<and> 0 \<le> (vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0)) \<or>
                        (\<tau> \<le> 0 \<and> (vx2 1 - vx2 0) * (vy2 ?k - vy2 0) - (vy2 1 - vy2 0) * (vx2 ?k - vx2 0) \<le> 0)"
                        using zero_le_mult_iff by (by100 blast)
                      with hfd1k have "\<tau> \<ge> 0" by (by100 linarith)
                      with \<open>\<tau> \<noteq> 0\<close> have "\<tau> > 0" by (by100 linarith)
                      moreover have "\<tau> < 1"
                      proof -
                        have "(fst p - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (snd p - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)) =
                          (1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1)))"
                          using hfst_eq hsnd_eq by (by100 algebra)
                        hence hMt_le2: "(1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) \<le> 0"
                          using hMp_le0 by (by100 linarith)
                        have "1-\<tau> \<ge> 0"
                        proof (rule ccontr)
                          assume "\<not> (0 \<le> 1 - \<tau>)"
                          hence "1 - \<tau> < 0" by (by100 linarith)
                          from mult_neg_neg[OF \<open>1 - \<tau> < 0\<close> hMd1k]
                          have "(1-\<tau>) * ((vx2 0 - vx2(?k-1)) * (vy2 ?k - vy2(?k-1)) - (vy2 0 - vy2(?k-1)) * (vx2 ?k - vx2(?k-1))) > 0" .
                          with hMt_le2 show False by (by100 linarith)
                        qed
                        hence "\<tau> \<le> 1" by (by100 linarith)
                        with \<open>\<tau> \<noteq> 1\<close> show "\<tau> < 1" by (by100 linarith)
                      qed
                      ultimately show ?thesis by (by100 linarith)
                    qed
                    with hfst_eq hsnd_eq show ?thesis by (by100 blast)
                  qed
                qed
                then obtain \<tau> where htau: "\<tau> > 0" "\<tau> < 1"
                  and hpx: "fst p = (1-\<tau>)*vx2 0 + \<tau>*vx2 ?k"
                  and hpy: "snd p = (1-\<tau>)*vy2 0 + \<tau>*vy2 ?k" by (by100 blast)
                \<comment> \<open>Now compute phi\\_L(p) with LEAST=k-1 and Cramer s=0, tp=\\<tau>.\<close>
                \<comment> \<open>The displacement is dx=\\<tau>*(vx2 k - vx2 0), dy=\\<tau>*(vy2 k - vy2 0).
                   In sector k-1: ex=vx2(k-1)-vx2 0, fx=vx2 k-vx2 0.
                   dx=\\<tau>*fx, dy=\\<tau>*fy. So s=(fy*\\<tau>*fx-fx*\\<tau>*fy)/det=0, tp=(ex*\\<tau>*fy-ey*\\<tau>*fx)/det=\\<tau>*det/det=\\<tau>.\<close>
                have "phi_L p = ((1-\<tau>)*vx2 0 + \<tau>*vx2 1, (1-\<tau>)*vy2 0 + \<tau>*vy2 1)"
                proof -
                  \<comment> \<open>Displacement from v\\_0.\<close>
                  have hdx: "fst p - vx2 0 = \<tau>*(vx2 ?k - vx2 0)" using hpx by (by100 algebra)
                  have hdy: "snd p - vy2 0 = \<tau>*(vy2 ?k - vy2 0)" using hpy by (by100 algebra)
                  \<comment> \<open>LEAST predicate at k-1.\<close>
                  let ?PL = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
                    (vx2 j - vx2 0)*(snd p - vy2 0) - (vy2 j - vy2 0)*(fst p - vx2 0) \<ge> 0 \<and>
                    (vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0) \<le> 0"
                  have hPL_km1: "?PL (?k - 1)"
                  proof -
                    have "1 \<le> ?k - 1" using hk_ge2 by (by100 linarith)
                    moreover have "?k - 1 < ?k" using hk_ge2 by (by100 linarith)
                    moreover have "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                    \<comment> \<open>Lower: cross(v\\_{k-1}, p-v\\_0) = \\<tau>*fan\\_det(k-1,k) \\<ge> 0.\<close>
                    moreover have "(vx2(?k-1) - vx2 0)*(snd p - vy2 0) - (vy2(?k-1) - vy2 0)*(fst p - vx2 0) \<ge> 0"
                    proof -
                      have "(vx2(?k-1) - vx2 0)*(snd p - vy2 0) - (vy2(?k-1) - vy2 0)*(fst p - vx2 0)
                        = \<tau>*((vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0))"
                        using hdx hdy by (by100 algebra)
                      moreover have "?k - 1 < ?n" using hk_ge2 by (by100 simp)
                      moreover have "?k < ?n" by (by100 simp)
                      moreover have "1 \<le> ?k - 1" using hk_ge2 by (by100 linarith)
                      ultimately have hfd: "(vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0) > 0"
                        using hfan_det_0 by (by100 force)
                      show ?thesis using mult_pos_pos[OF htau(1) hfd]
                        \<open>(vx2(?k-1) - vx2 0)*(snd p - vy2 0) - (vy2(?k-1) - vy2 0)*(fst p - vx2 0)
                        = \<tau>*((vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0))\<close>
                        by (by100 linarith)
                    qed
                    \<comment> \<open>Upper: cross(v\\_k, p-v\\_0) = \\<tau>*0 = 0.\<close>
                    moreover have "(vx2(Suc(?k-1)) - vx2 0)*(snd p - vy2 0) - (vy2(Suc(?k-1)) - vy2 0)*(fst p - vx2 0) \<le> 0"
                    proof -
                      have "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                      have "(vx2 ?k - vx2 0)*(snd p - vy2 0) - (vy2 ?k - vy2 0)*(fst p - vx2 0) = 0"
                        using hdx hdy by (by100 algebra)
                      thus ?thesis using \<open>Suc (?k - 1) = ?k\<close> by (by100 simp)
                    qed
                    ultimately show ?thesis by (by100 blast)
                  qed
                  have hPL_min: "\<And>j. ?PL j \<Longrightarrow> ?k - 1 \<le> j"
                  proof -
                    fix j assume hj: "?PL j"
                    hence hj1: "1 \<le> j" and hjk: "j < ?k" and
                      hupper: "(vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0) \<le> 0"
                      by (by100 simp)+
                    show "?k - 1 \<le> j"
                    proof (rule ccontr)
                      assume "\<not> ?k - 1 \<le> j" hence "j < ?k - 1" by (by100 linarith)
                      hence "Suc j < ?k" by (by100 linarith)
                      hence "Suc j < ?n" by (by100 simp)
                      have "?k < ?n" by (by100 simp)
                      have "1 \<le> Suc j" using hj1 by (by100 linarith)
                      \<comment> \<open>fan\\_det at Suc j, k > 0.\<close>
                      from hfan_det_0[rule_format, OF \<open>Suc j < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> Suc j\<close> \<open>Suc j < ?k\<close>]
                      have hfd: "(vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0) > 0" .
                      \<comment> \<open>Upper = \\<tau> * fan\\_det > 0.\<close>
                      have "(vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0)
                        = \<tau>*((vx2(Suc j) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(Suc j) - vy2 0)*(vx2 ?k - vx2 0))"
                        using hdx hdy by (by100 algebra)
                      hence "(vx2(Suc j) - vx2 0)*(snd p - vy2 0) - (vy2(Suc j) - vy2 0)*(fst p - vx2 0) > 0"
                        using mult_pos_pos[OF htau(1) hfd] by (by100 linarith)
                      with hupper show False by (by100 linarith)
                    qed
                  qed
                  have hLeast: "(LEAST j. ?PL j) = ?k - 1"
                    using Least_equality[of ?PL "?k - 1"] hPL_km1 hPL_min by (by100 blast)
                  \<comment> \<open>Cramer: dx=\\<tau>*fx, dy=\\<tau>*fy. s=0, tp=\\<tau>.\<close>
                  have hSuc_km1: "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                  \<comment> \<open>det = ex*fy - ey*fx > 0 from fan det.\<close>
                  have hdd_ne: "(vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0) \<noteq> 0"
                  proof -
                    have "?k - 1 < ?n" using hk_ge2 by (by100 simp)
                    have "?k < ?n" by (by100 simp)
                    have "1 \<le> ?k - 1" using hk_ge2 by (by100 linarith)
                    from hfan_det_0[rule_format, OF \<open>?k - 1 < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k - 1\<close>]
                    show ?thesis using hk_ge2 by (by100 linarith)
                  qed
                  \<comment> \<open>s numerator: fy*dx - fx*dy = \\<tau>*(fy*fx - fx*fy) = 0.\<close>
                  have hs_num: "((vy2 ?k - vy2 0)*(fst p - vx2 0) - (vx2 ?k - vx2 0)*(snd p - vy2 0)) = 0"
                    using hdx hdy by (by100 algebra)
                  \<comment> \<open>tp numerator: ex*dy - ey*dx = \\<tau>*(ex*fy - ey*fx) = \\<tau>*det.\<close>
                  have htp_num: "((vx2(?k-1) - vx2 0)*(snd p - vy2 0) - (vy2(?k-1) - vy2 0)*(fst p - vx2 0))
                    = \<tau>*((vx2(?k-1) - vx2 0)*(vy2 ?k - vy2 0) - (vy2(?k-1) - vy2 0)*(vx2 ?k - vx2 0))"
                    using hdx hdy by (by100 algebra)
                  \<comment> \<open>phi\\_L = (1-0-\\<tau>)*v\\_0 + 0*v\\_2 + \\<tau>*v\\_1 = (1-\\<tau>)*v\\_0 + \\<tau>*v\\_1.\<close>
                  show ?thesis unfolding phi_L_def Let_def
                    apply (simp only: fst_conv snd_conv hLeast hSuc_km1)
                    apply (insert hs_num htp_num hdd_ne)
                    by (simp add: divide_simps)
                qed
                moreover have "\<tau> \<in> I_set" using htau unfolding top1_unit_interval_def by (by100 auto)
                moreover have "Suc 0 mod ?n = 1" using hn_ge3 by (by100 simp)
                moreover have "((1-\<tau>)*vx2 0 + \<tau>*vx2 1, (1-\<tau>)*vy2 0 + \<tau>*vy2 1) =
                  ((1-\<tau>)*vx2 0 + \<tau>*vx2(Suc 0 mod ?n), (1-\<tau>)*vy2 0 + \<tau>*vy2(Suc 0 mod ?n))"
                  using \<open>Suc 0 mod ?n = 1\<close> by (by100 simp)
                moreover have "(fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0) \<longrightarrow>
                  (fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k) \<longrightarrow> \<tau> \<in> {0<..<(1::real)}"
                  using htau hne0 hnek by (by100 auto)
                ultimately show ?thesis by (by100 metis)
              qed
            qed
          qed
          \<comment> \<open>SHARED HELPER: affine functions non-negative at all vertices are non-negative at all P2 points.\<close>
          have hphi_L_R_disjoint: "\<And>x y. x \<in> P2 \<Longrightarrow> y \<in> P2 \<Longrightarrow>
              cross_diag x < 0 \<Longrightarrow> cross_diag y > 0 \<Longrightarrow> phi_L x \<noteq> phi_R y"
          proof
            fix x y assume hx: "x \<in> P2" and hy: "y \<in> P2"
              and hcdx: "cross_diag x < 0" and hcdy: "cross_diag y > 0"
              and heq: "phi_L x = phi_R y"
            \<comment> \<open>Step 1: get decompositions.\<close>
            from hphi_L_decomp[OF hx less_imp_le[OF hcdx]]
            obtain jL sL tpL where hjL: "1 \<le> jL" "jL < ?k"
              and hsL: "sL \<ge> 0" and htpL: "tpL \<ge> 0" and h1stL: "1 - sL - tpL \<ge> 0"
              and hphiL_dec: "phi_L x = ((1-sL-tpL)*vx2 0 + sL*vx2(?k+1-jL) + tpL*vx2(?k-jL),
                                          (1-sL-tpL)*vy2 0 + sL*vy2(?k+1-jL) + tpL*vy2(?k-jL))"
              by (by5000 blast)
            \<comment> \<open>Step 2: cross\\_diag decomposition for phi\\_L(x) — facts at outer scope.\<close>
            have hfstL: "fst (phi_L x) = (1-sL-tpL)*vx2 0 + sL*vx2(?k+1-jL) + tpL*vx2(?k-jL)"
              using hphiL_dec by (by100 simp)
            have hsndL: "snd (phi_L x) = (1-sL-tpL)*vy2 0 + sL*vy2(?k+1-jL) + tpL*vy2(?k-jL)"
              using hphiL_dec by (by100 simp)
            have hsumL: "(1-sL-tpL) + sL + tpL = (1::real)" by linarith
            have hcd_eq: "cross_diag (phi_L x) =
              sL*((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0))
            + tpL*((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0))"
            proof -
              have hcd_lin:
                "(vx2 ?k - vx2 0)*((1-sL-tpL)*vy2 0 + sL*vy2(?k+1-jL) + tpL*vy2(?k-jL) - vy2 0)
               - (vy2 ?k - vy2 0)*((1-sL-tpL)*vx2 0 + sL*vx2(?k+1-jL) + tpL*vx2(?k-jL) - vx2 0)
               = (1-sL-tpL)*((vx2 ?k - vx2 0)*(vy2 0 - vy2 0) - (vy2 ?k - vy2 0)*(vx2 0 - vx2 0))
               + sL*((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0))
               + tpL*((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0))"
                by (rule cross_product_affine_3[OF hsumL])
              show ?thesis unfolding cross_diag_def using hcd_lin hfstL hsndL by (by100 simp)
            qed
            have h_cdA: "(vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0) \<le> 0"
            proof (cases "?k+1-jL = ?k")
              case True thus ?thesis by (by100 simp)
            next
              case False
              have "1 \<le> ?k+1-jL" using hjL hk_ge2 by (by100 linarith)
              have "?k+1-jL < ?k" using False hjL by (by100 linarith)
              have "?k+1-jL < ?n" using \<open>?k+1-jL < ?k\<close> hk_lt_nm1 by (by100 linarith)
              have "?k < ?n" using hk_lt_nm1 by (by100 linarith)
              from hfan_det_0[rule_format, OF \<open>?k+1-jL < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k+1-jL\<close> \<open>?k+1-jL < ?k\<close>]
              show ?thesis
                apply (simp only: mult.commute[of "vx2 ?k - vx2 0"] mult.commute[of "vy2 ?k - vy2 0"])
                done
            qed
            have h_cdB: "(vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0) \<le> 0"
            proof -
              have "1 \<le> ?k-jL" using hjL by (by100 linarith)
              have "?k-jL < ?k" using hjL by (by100 linarith)
              have "?k-jL < ?n" using \<open>?k-jL < ?k\<close> hk_lt_nm1 by (by100 linarith)
              have "?k < ?n" using hk_lt_nm1 by (by100 linarith)
              from hfan_det_0[rule_format, OF \<open>?k-jL < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k-jL\<close> \<open>?k-jL < ?k\<close>]
              show ?thesis
                apply (simp only: mult.commute[of "vx2 ?k - vx2 0"] mult.commute[of "vy2 ?k - vy2 0"])
                done
            qed
            have hcd_phiL: "cross_diag (phi_L x) \<le> 0"
              using hcd_eq hsL htpL h_cdA h_cdB
              mult_nonneg_nonneg[of sL "-((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0))"]
              mult_nonneg_nonneg[of tpL "-((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0))"]
              by linarith
            \<comment> \<open>Step 3: cross\\_diag(phi\\_R(y)) \\<ge> 0 (symmetric).\<close>
            have hcd_phiR: "cross_diag (phi_R y) \<ge> 0"
            proof -
              from hphi_R_decomp[OF hy hcdy]
              obtain jR sR tpR where hjR: "?k \<le> jR" "jR < ?n - 1"
                and hsR: "sR \<ge> 0" and htpR: "tpR \<ge> 0" and h1stR: "1 - sR - tpR \<ge> 0"
                and hphiR_dec: "phi_R y = ((1-sR-tpR)*vx2 ?k + sR*vx2(Suc jR) + tpR*vx2(Suc(Suc jR) mod ?n),
                                           (1-sR-tpR)*vy2 ?k + sR*vy2(Suc jR) + tpR*vy2(Suc(Suc jR) mod ?n))"
                sorry \<comment> \<open>hphi\\_R\\_decomp extraction.\<close>
              have hsumR: "(1-sR-tpR) + sR + tpR = (1::real)" by linarith
              have hcd_eqR: "cross_diag (phi_R y) =
                sR*((vx2 ?k - vx2 0)*(vy2(Suc jR) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc jR) - vx2 0))
              + tpR*((vx2 ?k - vx2 0)*(vy2(Suc(Suc jR) mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc(Suc jR) mod ?n) - vx2 0))"
              proof -
                have hcd_linR:
                  "(vx2 ?k - vx2 0)*((1-sR-tpR)*vy2 ?k + sR*vy2(Suc jR) + tpR*vy2(Suc(Suc jR) mod ?n) - vy2 0)
                 - (vy2 ?k - vy2 0)*((1-sR-tpR)*vx2 ?k + sR*vx2(Suc jR) + tpR*vx2(Suc(Suc jR) mod ?n) - vx2 0)
                 = (1-sR-tpR)*((vx2 ?k - vx2 0)*(vy2 ?k - vy2 0) - (vy2 ?k - vy2 0)*(vx2 ?k - vx2 0))
                 + sR*((vx2 ?k - vx2 0)*(vy2(Suc jR) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc jR) - vx2 0))
                 + tpR*((vx2 ?k - vx2 0)*(vy2(Suc(Suc jR) mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc(Suc jR) mod ?n) - vx2 0))"
                  by (rule cross_product_affine_3[OF hsumR])
                show ?thesis unfolding cross_diag_def
                  using hcd_linR hphiR_dec by (by100 simp)
              qed
              \<comment> \<open>Right-fan vertices have cross\\_diag \\<ge> 0.\<close>
              have h_cdSj: "(vx2 ?k - vx2 0)*(vy2(Suc jR) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc jR) - vx2 0) \<ge> 0"
              proof -
                have "?k < Suc jR" using hjR by (by100 linarith)
                have "Suc jR < ?n" using hjR by (by100 linarith)
                have "?k < ?n" using hk_lt_nm1 by (by100 linarith)
                have "1 \<le> ?k" using hk_ge2 by (by100 linarith)
                from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> \<open>Suc jR < ?n\<close> \<open>1 \<le> ?k\<close> \<open>?k < Suc jR\<close>]
                show ?thesis by linarith
              qed
              have h_cdSSj: "(vx2 ?k - vx2 0)*(vy2(Suc(Suc jR) mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc(Suc jR) mod ?n) - vx2 0) \<ge> 0"
              proof -
                have hSSjR_lt: "Suc(Suc jR) mod ?n < ?n" by (by100 simp)
                have "?k < ?n" using hk_lt_nm1 by (by100 linarith)
                show ?thesis
                proof (cases "Suc(Suc jR) mod ?n = 0")
                  case True
                  \<comment> \<open>SSj mod n = 0 = vertex v\\_0. cross\\_diag(v\\_0) = 0.\<close>
                  thus ?thesis by (by100 simp)
                next
                  case False
                  \<comment> \<open>SSj mod n > 0. From hSSj\\_mod\\_ge: SSj mod n \\<ge> k+2 > k.\<close>
                  from hSSj_mod_ge[OF hjR(1) hjR(2)]
                  have "Suc(Suc jR) mod ?n \<ge> ?k + 2 \<or> Suc(Suc jR) mod ?n = 0" .
                  with False have "Suc(Suc jR) mod ?n \<ge> ?k + 2" by linarith
                  hence "?k < Suc(Suc jR) mod ?n" by linarith
                  have "1 \<le> ?k" using hk_ge2 by (by100 linarith)
                  from hfan_det_0[rule_format, OF \<open>?k < ?n\<close> hSSjR_lt \<open>1 \<le> ?k\<close> \<open>?k < Suc(Suc jR) mod ?n\<close>]
                  show ?thesis by linarith
                qed
              qed
              show ?thesis using hcd_eqR hsR htpR h_cdSj h_cdSSj
                mult_nonneg_nonneg[of sR "((vx2 ?k - vx2 0)*(vy2(Suc jR) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc jR) - vx2 0))"]
                mult_nonneg_nonneg[of tpR "((vx2 ?k - vx2 0)*(vy2(Suc(Suc jR) mod ?n) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(Suc(Suc jR) mod ?n) - vx2 0))"]
                by linarith
            qed
            \<comment> \<open>Step 4: equality forces cross\\_diag = 0 on both.\<close>
            have "cross_diag (phi_L x) = cross_diag (phi_R y)" using heq by (by100 simp)
            hence hcd_zero: "cross_diag (phi_L x) = 0" using hcd_phiL hcd_phiR by linarith
            \<comment> \<open>Step 5: cross\\_diag = 0 forces coefficients to 0, then x = v\\_0, contradiction.\<close>
            \<comment> \<open>Step 5: sL*cdA + tpL*cdB = 0, cdB < 0 \\<to> tpL = 0, then sL analysis.\<close>
            have hsum_zero: "sL*((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0))
              + tpL*((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0)) = 0"
              using hcd_eq hcd_zero by linarith
            have hcdB_strict: "(vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0) < 0"
            proof -
              have "?k-jL < ?k" using hjL by (by100 linarith)
              have "?k-jL < ?n" using \<open>?k-jL < ?k\<close> hk_lt_nm1 by (by100 linarith)
              have "?k < ?n" using hk_lt_nm1 by (by100 linarith)
              have "1 \<le> ?k-jL" using hjL by (by100 linarith)
              from hfan_det_0[rule_format, OF \<open>?k-jL < ?n\<close> \<open>?k < ?n\<close> \<open>1 \<le> ?k-jL\<close> \<open>?k-jL < ?k\<close>]
              show ?thesis
                apply (simp only: mult.commute[of "vx2 ?k - vx2 0"] mult.commute[of "vy2 ?k - vy2 0"])
                done
            qed
            have "tpL*((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0)) = 0"
            proof -
              have "tpL*((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0)) \<le> 0"
                using htpL hcdB_strict
                mult_nonneg_nonneg[of tpL "-((vx2 ?k - vx2 0)*(vy2(?k-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k-jL) - vx2 0))"]
                by linarith
              moreover have "sL*((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0)) \<le> 0"
                using hsL h_cdA
                mult_nonneg_nonneg[of sL "-((vx2 ?k - vx2 0)*(vy2(?k+1-jL) - vy2 0) - (vy2 ?k - vy2 0)*(vx2(?k+1-jL) - vx2 0))"]
                by linarith
              ultimately show ?thesis using hsum_zero by linarith
            qed
            hence htpL_zero: "tpL = 0" using hcdB_strict
              by (simp only: mult_eq_0_iff, by100 simp)
            \<comment> \<open>tpL=0. From hphi\\_L\\_decomp Cramer: cross\\_jL(x) = 0.
               From sL*cdA = 0 (since sum=0 and tpL=0): either sL=0 or cdA=0.
               If sL=0: phi\\_L(x) = v\\_0. Cramer \\<to> x = v\\_0. cross\\_diag(v\\_0) = 0. \\<bot>.
               If cdA=0 (jL=1): phi\\_L(x) = (1-sL)*v\\_0 + sL*v\\_k on diagonal.
               Then phi\\_R(y) = phi\\_L(x) on diagonal. By symmetric argument: cross\\_diag(y) = 0. \\<bot>.\<close>
            show False
              sorry \<comment> \<open>tpL=0 proved. sL+Cramer or symmetric y-argument needed.\<close>
          qed
          have hphi_L_inj: "\<And>x y. x \<in> P2 \<Longrightarrow> y \<in> P2 \<Longrightarrow>
              cross_diag x \<le> 0 \<Longrightarrow> cross_diag y \<le> 0 \<Longrightarrow> phi_L x = phi_L y \<Longrightarrow> x = y"
          proof -
            fix x y assume hx: "x \<in> P2" and hy: "y \<in> P2"
              and hcdx: "cross_diag x \<le> 0" and hcdy: "cross_diag y \<le> 0"
              and heq: "phi_L x = phi_L y"
            \<comment> \<open>Let j\\_x, j\\_y be the LEAST sectors for x, y.\<close>
            let ?PLx = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd x - vy2 0) - (vy2 j - vy2 0)*(fst x - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd x - vy2 0) - (vy2(Suc j) - vy2 0)*(fst x - vx2 0) \<le> 0"
            let ?PLy = "\<lambda>j. 1 \<le> j \<and> j < ?k \<and>
              (vx2 j - vx2 0)*(snd y - vy2 0) - (vy2 j - vy2 0)*(fst y - vx2 0) \<ge> 0 \<and>
              (vx2(Suc j) - vx2 0)*(snd y - vy2 0) - (vy2(Suc j) - vy2 0)*(fst y - vx2 0) \<le> 0"
            \<comment> \<open>Unfold phi\\_L\\_def for both x and y.\<close>
            have hphi_x: "phi_L x = (let j = (LEAST j. ?PLx j) in
              let ex = vx2 j - vx2 0; ey = vy2 j - vy2 0;
                  fx = vx2(Suc j) - vx2 0; fy = vy2(Suc j) - vy2 0;
                  det = ex*fy - ey*fx;
                  s = (fy*(fst x - vx2 0) - fx*(snd x - vy2 0))/det;
                  tp = (ex*(snd x - vy2 0) - ey*(fst x - vx2 0))/det in
              ((1-s-tp)*vx2 0 + s*vx2(?k+1-j) + tp*vx2(?k-j),
               (1-s-tp)*vy2 0 + s*vy2(?k+1-j) + tp*vy2(?k-j)))"
              unfolding phi_L_def Let_def by (by100 simp)
            show "x = y"
              sorry \<comment> \<open>Same sector: Cramer inversion (det \\<noteq> 0 gives unique (s,tp) \\<to> unique (x,y)).
                 Different sectors: fan triangle interiors disjoint \\<to> contradiction.\<close>
          qed
          have hphi_R_inj: "\<And>x y. x \<in> P2 \<Longrightarrow> y \<in> P2 \<Longrightarrow>
              cross_diag x > 0 \<Longrightarrow> cross_diag y > 0 \<Longrightarrow> phi_R x = phi_R y \<Longrightarrow> x = y"
            sorry \<comment> \<open>phi\\_R is injective on right half.\<close>
          \<comment> \<open>Main C8 argument.\<close>
          show "p = p'"
          proof -
            \<comment> \<open>p is target interior. Determine which half p and p' are in via cross\\_diag.\<close>
            have hg_eq: "g p = g p'" by (rule heq)
            show ?thesis
            proof (cases "cross_diag p < 0")
              case True
              \<comment> \<open>p strictly left. g(p) = q2(phi\\_L(p)). phi\\_L(p) is old interior.\<close>
              have hgp: "g p = q2 (phi_L p)" using True unfolding g_def by (by100 simp)
              have hphi_int_p: "\<forall>i<?n. \<forall>t\<in>I_set.
                  phi_L p \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
                using hphi_L_int[OF hp True hint] .
              have hphi_in: "phi_L p \<in> P2" using hphi_L_in_P2[OF hp less_imp_le[OF True]] .
              \<comment> \<open>Old C8 at phi\\_L(p): singleton fibre.\<close>
              have hC8_at_p: "\<forall>p'\<in>P2. q2 (phi_L p) = q2 p' \<longrightarrow> phi_L p = p'"
                using hC8_2[rule_format, OF hphi_in] hphi_int_p by (by100 blast)
              \<comment> \<open>Now analyze p'.\<close>
              \<comment> \<open>Case analysis on cross\\_diag(p').\<close>
              show ?thesis
              proof (cases "cross_diag p' < 0")
                case True2: True
                \<comment> \<open>p' also left. g(p') = q2(phi\\_L(p')). From g=g: q2(phi\\_L(p))=q2(phi\\_L(p')).
                   hC8\\_at\\_p: phi\\_L(p) = phi\\_L(p'). hphi\\_L\\_inj: p = p'.\<close>
                have "g p' = q2 (phi_L p')" using True2 unfolding g_def by (by100 simp)
                hence "q2 (phi_L p) = q2 (phi_L p')" using hgp hg_eq by simp
                moreover have "phi_L p' \<in> P2" using hphi_L_in_P2[OF hp' less_imp_le[OF True2]] .
                ultimately have "phi_L p = phi_L p'" using hC8_at_p by (by100 blast)
                thus ?thesis using hphi_L_inj[OF hp hp' _ _ \<open>phi_L p = phi_L p'\<close>]
                  True True2 by linarith
              next
                case False2: False
                show ?thesis
                proof (cases "cross_diag p' > 0")
                  case True3: True
                  \<comment> \<open>p left, p' right. g(p') = q2(phi\\_R(p')). From g=g: q2(phi\\_L(p))=q2(phi\\_R(p')).
                     hC8\\_at\\_p: phi\\_L(p) = phi\\_R(p'). Contradicts disjointness.\<close>
                  have "g p' = q2 (phi_R p')" using True3 unfolding g_def by (by100 simp)
                  hence "q2 (phi_L p) = q2 (phi_R p')" using hgp hg_eq by simp
                  moreover have "phi_R p' \<in> P2" using hphi_R_in_P2[OF hp' True3] .
                  ultimately have "phi_L p = phi_R p'" using hC8_at_p by (by100 blast)
                  with hphi_L_R_disjoint[OF hp hp' True True3] show ?thesis by simp
                next
                  case False3: False
                  hence "cross_diag p' = 0" using False2 by linarith
                  \<comment> \<open>p' on diagonal. g(p') = q2(phi\\_L(p')). From g=g: q2(phi\\_L(p))=q2(phi\\_L(p')).
                     hC8\\_at\\_p: phi\\_L(p) = phi\\_L(p'). hphi\\_L\\_inj: p = p'.\<close>
                  have hcd_p'_le: "cross_diag p' \<le> 0" using \<open>cross_diag p' = 0\<close> by simp
                  have "g p' = q2 (phi_L p')" using \<open>cross_diag p' = 0\<close> unfolding g_def by (by100 simp)
                  hence "q2 (phi_L p) = q2 (phi_L p')" using hgp hg_eq by simp
                  moreover have "phi_L p' \<in> P2" using hphi_L_in_P2[OF hp' hcd_p'_le] .
                  ultimately have "phi_L p = phi_L p'" using hC8_at_p by (by100 blast)
                  thus ?thesis using hphi_L_inj[OF hp hp' _ _ \<open>phi_L p = phi_L p'\<close>]
                    True \<open>cross_diag p' = 0\<close> by linarith
                qed
              qed
            next
              case False
              \<comment> \<open>cross\\_diag(p) \\<ge> 0: right-half or diagonal case. Symmetric to left-half.\<close>
              show ?thesis
              proof (cases "cross_diag p > 0")
                case True2: True
                \<comment> \<open>p strictly right. g(p) = q2(phi\\_R(p)).\<close>
                have hgp: "g p = q2 (phi_R p)" using True2 unfolding g_def by (by100 simp)
                have hphi_int_p: "\<forall>i<?n. \<forall>t\<in>I_set.
                    phi_R p \<noteq> ((1-t)*vx2 i + t*vx2(Suc i mod ?n), (1-t)*vy2 i + t*vy2(Suc i mod ?n))"
                  using hphi_R_int[OF hp True2 hint] .
                have hphi_in: "phi_R p \<in> P2" using hphi_R_in_P2[OF hp True2] .
                have hC8_at_p: "\<forall>p'\<in>P2. q2 (phi_R p) = q2 p' \<longrightarrow> phi_R p = p'"
                  using hC8_2[rule_format, OF hphi_in] hphi_int_p by (by100 blast)
                show ?thesis
                proof (cases "cross_diag p' > 0")
                  case True3: True
                  \<comment> \<open>Both right.\<close>
                  have "g p' = q2 (phi_R p')" using True3 unfolding g_def by (by100 simp)
                  hence "q2 (phi_R p) = q2 (phi_R p')" using hgp hg_eq by simp
                  moreover have "phi_R p' \<in> P2" using hphi_R_in_P2[OF hp' True3] .
                  ultimately have hphieq: "phi_R p = phi_R p'" using hC8_at_p by (by100 blast)
                  from hphi_R_inj[OF hp hp' True2 True3 hphieq] show ?thesis .
                next
                  case False3: False
                  show ?thesis
                  proof (cases "cross_diag p' < 0")
                    case True4: True
                    \<comment> \<open>p right, p' left.\<close>
                    have "g p' = q2 (phi_L p')" using True4 unfolding g_def by (by100 simp)
                    hence "q2 (phi_R p) = q2 (phi_L p')" using hgp hg_eq by simp
                    moreover have "phi_L p' \<in> P2" using hphi_L_in_P2[OF hp' less_imp_le[OF True4]] .
                    ultimately have "phi_R p = phi_L p'" using hC8_at_p by (by100 blast)
                    with hphi_L_R_disjoint[OF hp' hp True4 True2] show ?thesis by simp
                  next
                    case False4: False
                    hence "cross_diag p' = 0" using False3 by linarith
                    have hcd_p'_le2: "cross_diag p' \<le> 0" using \<open>cross_diag p' = 0\<close> by simp
                    \<comment> \<open>p right, p' on diagonal.\<close>
                    have "g p' = q2 (phi_L p')" using \<open>cross_diag p' = 0\<close> unfolding g_def by (by100 simp)
                    hence "q2 (phi_R p) = q2 (phi_L p')" using hgp hg_eq by simp
                    moreover have "phi_L p' \<in> P2" using hphi_L_in_P2[OF hp' hcd_p'_le2] .
                    ultimately have heq_RL: "phi_R p = phi_L p'" using hC8_at_p by (by100 blast)
                    \<comment> \<open>Expert audit 38: phi\\_L(p') on old edge 0, phi\\_R(p) not on old edge 0.\<close>
                    from hphi_L_diagonal_on_edge[OF hp' \<open>cross_diag p' = 0\<close>]
                    obtain t_d where ht_d: "t_d \<in> I_set"
                      and hphiL_edge: "phi_L p' = ((1-t_d)*vx2 0 + t_d*vx2(Suc 0 mod ?n),
                                                    (1-t_d)*vy2 0 + t_d*vy2(Suc 0 mod ?n))"
                      and ht_d_strict: "(fst p' \<noteq> vx2 0 \<or> snd p' \<noteq> vy2 0) \<longrightarrow>
                        (fst p' \<noteq> vx2 ?k \<or> snd p' \<noteq> vy2 ?k) \<longrightarrow> t_d \<in> {0<..<(1::real)}"
                      by (by100 blast)
                    have "(0::nat) < ?n" using hn_ge3 by linarith
                    from hphi_R_int[OF hp True2 hint, rule_format, OF \<open>0 < ?n\<close> ht_d]
                    have "phi_R p \<noteq> ((1-t_d)*vx2 0 + t_d*vx2(Suc 0 mod ?n),
                                      (1-t_d)*vy2 0 + t_d*vy2(Suc 0 mod ?n))" .
                    with heq_RL hphiL_edge show ?thesis by simp
                  qed
                qed
              next
                case False2: False
                hence hcd0: "cross_diag p = 0" using False by linarith
                have hcd0_le: "cross_diag p \<le> 0" using hcd0 by simp
                \<comment> \<open>p on diagonal. g(p) = q2(phi\\_L(p)).\<close>
                have hgp: "g p = q2 (phi_L p)" using hcd0 unfolding g_def by (by100 simp)
                show ?thesis
                proof (cases "cross_diag p' > 0")
                  case True3: True
                  \<comment> \<open>p on diagonal, p' right.\<close>
                  have "g p' = q2 (phi_R p')" using True3 unfolding g_def by (by100 simp)
                  hence "q2 (phi_L p) = q2 (phi_R p')" using hgp hg_eq by simp
                  \<comment> \<open>phi\\_L(p) is on old boundary (diagonal maps to edge 0 or k).
                     phi\\_R(p') is old interior. Old C8: boundary \\<inter> interior = \\<emptyset> in fibres.
                     So phi\\_L(p) \\<noteq> phi\\_R(p'). But q2(phi\\_L(p)) = q2(phi\\_R(p')).
                     From hC8\\_at phi\\_R(p'): phi\\_R(p') = phi\\_L(p). Contradicts disjointness.\<close>
                  have hphi_R_in: "phi_R p' \<in> P2" using hphi_R_in_P2[OF hp' True3] .
                  have hphi_L_in: "phi_L p \<in> P2" using hphi_L_in_P2[OF hp hcd0_le] .
                  \<comment> \<open>phi\\_L(p) is on old edge 0 (from diagonal).\<close>
                  from hphi_L_diagonal_on_edge[OF hp hcd0]
                  obtain t_d where ht_d: "t_d \<in> I_set"
                    and hphiL_edge: "phi_L p = ((1-t_d)*vx2 0 + t_d*vx2(Suc 0 mod ?n),
                                                (1-t_d)*vy2 0 + t_d*vy2(Suc 0 mod ?n))"
                    by (by5000 blast)
                  \<comment> \<open>Case split: is phi\\_R(p') on an old edge or interior?\<close>
                  show ?thesis
                  proof (cases "\<forall>ii<?n. \<forall>tt\<in>I_set.
                      phi_R p' \<noteq> ((1-tt)*vx2 ii+tt*vx2(Suc ii mod ?n),(1-tt)*vy2 ii+tt*vy2(Suc ii mod ?n))")
                    case True_int: True
                    \<comment> \<open>phi\\_R(p') is interior. C8 at phi\\_R(p') \\<to> phi\\_R(p')=phi\\_L(p) \\<to> on edge 0 \\<to> contradiction.\<close>
                    have hC8_Rp: "\<forall>q\<in>P2. q2 (phi_R p') = q2 q \<longrightarrow> phi_R p' = q"
                      using hC8_2[rule_format, OF hphi_R_in] True_int by (by100 blast)
                    have "q2 (phi_R p') = q2 (phi_L p)" using \<open>q2 (phi_L p) = q2 (phi_R p')\<close> by simp
                    hence heq_RL: "phi_R p' = phi_L p" using hC8_Rp[rule_format, OF hphi_L_in] by simp
                    \<comment> \<open>phi\\_R(p') = phi\\_L(p) = edge\\_0(t\\_d). But phi\\_R(p') is not on any edge. Contradiction.\<close>
                    have "(0::nat) < ?n" using hn_ge3 by linarith
                    from True_int[rule_format, OF \<open>0 < ?n\<close> ht_d]
                    have "phi_R p' \<noteq> ((1-t_d)*vx2 0 + t_d*vx2(Suc 0 mod ?n),
                                      (1-t_d)*vy2 0 + t_d*vy2(Suc 0 mod ?n))" .
                    with heq_RL hphiL_edge show ?thesis by simp
                  next
                    case False
                    \<comment> \<open>phi\\_R(p') IS on an old edge. Both on edges: use C9.\<close>
                    show ?thesis sorry \<comment> \<open>Edge-vs-edge C9 analysis for diagonal p, edge p'.\<close>
                  qed
                next
                  case False3: False
                  hence "cross_diag p' \<le> 0" by linarith
                  \<comment> \<open>Both on left or diagonal.\<close>
                  have "g p' = q2 (phi_L p')" using \<open>cross_diag p' \<le> 0\<close> unfolding g_def by (by100 simp)
                  hence hq_eq: "q2 (phi_L p) = q2 (phi_L p')" using hgp hg_eq by simp
                  have hphi_L_p'_in: "phi_L p' \<in> P2" using hphi_L_in_P2[OF hp' \<open>cross_diag p' \<le> 0\<close>] .
                  have hphi_L_p_in: "phi_L p \<in> P2" using hphi_L_in_P2[OF hp hcd0_le] .
                  \<comment> \<open>Expert audit 38: split on p' strict left vs p' diagonal.\<close>
                  have "phi_L p = phi_L p'"
                  proof (cases "cross_diag p' < 0")
                    case True4: True
                    \<comment> \<open>p' strict left. Case split on phi\\_L(p') interior vs on edge.\<close>
                    show ?thesis
                    proof (cases "\<forall>ii<?n. \<forall>tt\<in>I_set.
                        phi_L p' \<noteq> ((1-tt)*vx2 ii+tt*vx2(Suc ii mod ?n),(1-tt)*vy2 ii+tt*vy2(Suc ii mod ?n))")
                      case True_int: True
                      hence "\<forall>q\<in>P2. q2 (phi_L p') = q2 q \<longrightarrow> phi_L p' = q"
                        using hC8_2[rule_format, OF hphi_L_p'_in] by (by100 blast)
                      from this[rule_format, OF hphi_L_p_in]
                      show ?thesis using hq_eq by simp
                    next
                      case False
                      \<comment> \<open>phi\\_L(p') is on an old edge. Both phi\\_L(p) and phi\\_L(p') on edges.\<close>
                      show ?thesis sorry \<comment> \<open>Edge-vs-edge: use C9 for two boundary points.\<close>
                    qed
                  next
                    case False4: False
                    hence "cross_diag p' = 0" using \<open>cross_diag p' \<le> 0\<close> by linarith
                    \<comment> \<open>Both p and p' on diagonal. phi\\_L(p) and phi\\_L(p') both on old edge 0.
                       Use old C9 for parameter equality (expert audit 38: diagonal g injective).\<close>
                    \<comment> \<open>Expert audit 38: diagonal-vs-diagonal. Both phi\\_L(p), phi\\_L(p') on old edge 0.
                       phi\\_L(p) at interior parameter (p is target interior \\<to> param \\<in> (0,1)).
                       If phi\\_L(p') also at interior param: old C9 gives equality.
                       If phi\\_L(p') at vertex (t=0 or t=1): old C8 at phi\\_L(p) gives contradiction.\<close>
                    \<comment> \<open>phi\\_L(p) is on old edge 0 at some interior parameter.\<close>
                    from hphi_L_diagonal_on_edge[OF hp hcd0]
                    obtain tp where htp: "tp \<in> I_set"
                      and hphiL_p: "phi_L p = ((1-tp)*vx2 0 + tp*vx2(Suc 0 mod ?n),
                                                (1-tp)*vy2 0 + tp*vy2(Suc 0 mod ?n))"
                      and htp_strict: "(fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0) \<longrightarrow>
                        (fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k) \<longrightarrow> tp \<in> {0<..<(1::real)}"
                      by (by5000 blast)
                    from hphi_L_diagonal_on_edge[OF hp' \<open>cross_diag p' = 0\<close>]
                    obtain tp' where htp': "tp' \<in> I_set"
                      and hphiL_p': "phi_L p' = ((1-tp')*vx2 0 + tp'*vx2(Suc 0 mod ?n),
                                                  (1-tp')*vy2 0 + tp'*vy2(Suc 0 mod ?n))"
                      by (by5000 blast)
                    \<comment> \<open>p is target interior: p \\<noteq> v\\_0 (on edge 0 at t=0), p \\<noteq> v\\_k (on edge k-1 at t=1).\<close>
                    have htp_interior: "tp \<in> {0<..<(1::real)}"
                    proof -
                      have hpne0: "fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0"
                      proof (rule ccontr)
                        assume "\<not> (fst p \<noteq> vx2 0 \<or> snd p \<noteq> vy2 0)"
                        hence "fst p = vx2 0" "snd p = vy2 0" by (by100 simp)+
                        hence "p = ((1-(0::real))*vx2 0+0*vx2(Suc 0 mod length ?w'),(1-0)*vy2 0+0*vy2(Suc 0 mod length ?w'))"
                          by (cases p) simp
                        moreover have "(0::nat) < length ?w'" using hlen_eq hn_ge3 by (by100 simp)
                        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        ultimately show False using hint by (by100 blast)
                      qed
                      have hpnek: "fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k"
                      proof (rule ccontr)
                        assume "\<not> (fst p \<noteq> vx2 ?k \<or> snd p \<noteq> vy2 ?k)"
                        hence "fst p = vx2 ?k" "snd p = vy2 ?k" by (by100 simp)+
                        have hSuc_km1: "Suc (?k - 1) mod ?n = ?k"
                        proof -
                          have "Suc (?k - 1) = ?k" using hk_ge2 by (by100 linarith)
                          moreover have "?k < ?n" by (by100 simp)
                          ultimately show ?thesis by (by100 simp)
                        qed
                        have "p = ((1-(1::real))*vx2(?k-1)+1*vx2(Suc(?k-1) mod length ?w'),(1-1)*vy2(?k-1)+1*vy2(Suc(?k-1) mod length ?w'))"
                          using \<open>fst p = vx2 ?k\<close> \<open>snd p = vy2 ?k\<close> hSuc_km1 hlen_eq
                          by (cases p) simp
                        moreover have "?k - 1 < length ?w'" using hlen_eq hk_ge2 by (by100 simp)
                        moreover have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
                        ultimately show False using hint by (by100 blast)
                      qed
                      from htp_strict hpne0 hpnek show ?thesis by (by100 simp)
                    qed
                    show ?thesis
                    proof (cases "tp' \<in> {0<..<(1::real)}")
                      case True5: True
                      \<comment> \<open>Both interior params. Old C9 at i=0, j=0 gives tp = tp'.\<close>
                      have "(0::nat) < ?n" using hn_ge3 by linarith
                      \<comment> \<open>Old C9 at i=0, j=0: tp' = tp (same label, same direction).\<close>
                      have "tp = tp'"
                      proof -
                        \<comment> \<open>Apply old C9 at i=0, j=0, t=tp, s=tp'.\<close>
                        have h0_lt: "(0::nat) < ?n" using hn_ge3 by linarith
                        have hq_edge: "q2 ((1-tp)*vx2 0+tp*vx2(Suc 0 mod ?n),(1-tp)*vy2 0+tp*vy2(Suc 0 mod ?n))
                          = q2 ((1-tp')*vx2 0+tp'*vx2(Suc 0 mod ?n),(1-tp')*vy2 0+tp'*vy2(Suc 0 mod ?n))"
                          using hq_eq hphiL_p hphiL_p' by simp
                        from hC9_2[rule_format, OF h0_lt h0_lt htp_interior True5 hq_edge]
                        show ?thesis by (elim disjE) simp_all
                      qed
                      thus ?thesis using hphiL_p hphiL_p' by simp
                    next
                      case False5: False
                      \<comment> \<open>tp' is 0 or 1 (vertex). phi\\_L(p') = v\\_0 or v\\_1.
                         phi\\_L(p) is at interior param. q2(edge\\_0(tp)) = q2(vertex).
                         Old C8: phi\\_L(p) NOT a vertex (interior param). But q2 equals vertex image.
                         Use old C8 at... actually need old C9 variant for vertex matching.\<close>
                      \<comment> \<open>Since tp' \\<notin> (0,1) and tp' \\<in> [0,1]: tp' = 0 or tp' = 1.
                         phi\\_L(p') is either v\\_0 or v\\_1. These are OLD polygon vertices.
                         phi\\_L(p) is an old edge 0 interior point.
                         q2(edge\\_0(tp)) = q2(v\\_0) or q2(v\\_1).
                         By old C7 at i=0: q2(edge\\_0(t)) = q2(edge\\_{?k}(t)).
                         So q2(v\\_0) = q2(edge\\_0(0)) and q2(v\\_1) = q2(edge\\_0(1)).
                         But q2(edge\\_0(tp)) with tp \\<in> (0,1) can only equal q2(edge\\_j(s))
                         for specific j,s from C9. For j=0: s=tp. For j=?k: s=tp (same dir).
                         q2(edge\\_0(tp)) = q2(v\\_0) would need tp=0. Contradiction.\<close>
                      show ?thesis sorry \<comment> \<open>Vertex vs interior diagonal: C7/C9 boundary analysis.\<close>
                    qed
                  qed
                  thus ?thesis using hphi_L_inj[OF hp hp'] hcd0 \<open>cross_diag p' \<le> 0\<close>
                    by simp
                qed
              qed
            qed
          qed
        qed
        show "\<forall>i<length ?w'. \<forall>j<length ?w'. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
            g ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w'))
            = g ((1-s)*vx2 j+s*vx2(Suc j mod length ?w'),(1-s)*vy2 j+s*vy2(Suc j mod length ?w'))
            \<longrightarrow> (i=j \<and> t=s) \<or> (fst(?w'!i)=fst(?w'!j) \<and>
            (if snd(?w'!i)=snd(?w'!j) then s=t else s=1-t))"
        proof (intro allI impI ballI)
          fix i j t s assume hi: "i < length ?w'" and hj: "j < length ?w'"
              and ht: "t \<in> {0<..<(1::real)}" and hs: "s \<in> {0<..<(1::real)}"
              and heq: "g ((1-t)*vx2 i+t*vx2(Suc i mod length ?w'),(1-t)*vy2 i+t*vy2(Suc i mod length ?w'))
                = g ((1-s)*vx2 j+s*vx2(Suc j mod length ?w'),(1-s)*vy2 j+s*vy2(Suc j mod length ?w'))"
          have hi': "i < ?n" and hj': "j < ?n" using hi hj hlen_eq by simp+
          have ht_I: "t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 auto)
          have hs_I: "s \<in> I_set" using hs unfolding top1_unit_interval_def by (by100 auto)
          \<comment> \<open>From hg\\_bdy: g on edges = q2 o sigma.\<close>
          have hgi: "g ((1-t)*vx2 i+t*vx2(Suc i mod ?n),(1-t)*vy2 i+t*vy2(Suc i mod ?n))
            = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
            using hg_bdy[rule_format, OF hi' ht_I] .
          have hgj: "g ((1-s)*vx2 j+s*vx2(Suc j mod ?n),(1-s)*vy2 j+s*vy2(Suc j mod ?n))
            = q2 (paste_sigma vx2 vy2 ?k ?n j s)"
            using hg_bdy[rule_format, OF hj' hs_I] .
          \<comment> \<open>From heq + hgi + hgj: q2(sigma(i,t)) = q2(sigma(j,s)).\<close>
          have hq2_eq: "q2 (paste_sigma vx2 vy2 ?k ?n i t) = q2 (paste_sigma vx2 vy2 ?k ?n j s)"
            using heq hgi hgj hlen_eq by (by100 simp)
          \<comment> \<open>Apply C9\\_2 to sigma(i,t) and sigma(j,s) to get original matching.
             Then translate to target matching via sigma correspondence.\<close>
          \<comment> \<open>Expert audit 38, Step 3: C9 via hg\\_bdy + old C9 + sigma correspondence.
             Case split on which target edges i, j are (c-edges vs u2-edges vs v-edges).\<close>
          show "(i=j \<and> t=s) \<or> (fst(?w'!i)=fst(?w'!j) \<and>
            (if snd(?w'!i)=snd(?w'!j) then s=t else s=1-t))"
          proof (cases "i = 0 \<or> i = ?n - 1")
            case True
            \<comment> \<open>i is a c-edge: sigma(i,t) = (1-t)*v\\_0 + t*v\\_k (diagonal, old interior).
               If j is also a c-edge: sigma(j,s) = (1-s)*v\\_0 + s*v\\_k.
               Then equality gives t = s. Labels match (both c, same dir).
               If j is not a c-edge: sigma(j,s) is on an old edge (boundary).
               Old C8 at sigma(i,t) (interior) forces sigma(i,t)=sigma(j,s).
               But diagonal \\<noteq> edge: contradiction.\<close>
            show ?thesis
            proof (cases "j = 0 \<or> j = ?n - 1")
              case True2: True
              \<comment> \<open>Both c-edges. sigma(i,t) = sigma(j,s) gives t = s.
                 Both have label c, same direction True.\<close>
              \<comment> \<open>Both c-edges: sigma(i,t) = (1-t)*v\\_0+t*v\\_k, sigma(j,s) = (1-s)*v\\_0+s*v\\_k.
                 q2 equality + C8 at interior point gives sigma(i,t) = sigma(j,s), hence t = s.
                 Both i,j \\<in> \\{0,n-1\\} with label c, same direction True.\<close>
              \<comment> \<open>sigma(i,t) and sigma(j,s) are both on the diagonal (interior).\<close>
              have hsigma_i: "paste_sigma vx2 vy2 ?k ?n i t = ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k)"
                using True unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by simp
              have hsigma_j: "paste_sigma vx2 vy2 ?k ?n j s = ((1-s)*vx2 0 + s*vx2 ?k, (1-s)*vy2 0 + s*vy2 ?k)"
                using True2 unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by simp
              \<comment> \<open>These are interior polygon points (on the diagonal).\<close>
              \<comment> \<open>From hq2\\_eq: q2 of these are equal. Since they are on the diagonal
                 (inside polygon, not on any old edge for 0<t<1), old C8 forces equality.\<close>
              have "paste_sigma vx2 vy2 ?k ?n i t = paste_sigma vx2 vy2 ?k ?n j s"
              proof (cases "?k < ?n - 1")
                case True3: True
                \<comment> \<open>k < n-1: diagonal not an edge. hdiag gives interior point. Old C8 gives equality.\<close>
                have "paste_sigma vx2 vy2 ?k ?n i t \<in> P2" using hsigma_in_P2[OF hi' ht_I] .
                moreover have "\<forall>i''<?n. \<forall>t''\<in>I_set.
                  paste_sigma vx2 vy2 ?k ?n i t \<noteq>
                  ((1-t'')*vx2 i'' + t''*vx2(Suc i'' mod ?n), (1-t'')*vy2 i'' + t''*vy2(Suc i'' mod ?n))"
                  using hdiag_not_on_edge[OF ht] hsigma_i by (by100 simp)
                ultimately have "\<forall>p'\<in>P2. q2 (paste_sigma vx2 vy2 ?k ?n i t) = q2 p' \<longrightarrow>
                  paste_sigma vx2 vy2 ?k ?n i t = p'"
                  using hC8_2[rule_format] by (by100 blast)
                moreover have "paste_sigma vx2 vy2 ?k ?n j s \<in> P2" using hsigma_in_P2[OF hj' hs_I] .
                ultimately show ?thesis using hq2_eq by (by100 blast)
              next
                case False3: False
                hence "?k = ?n - 1" using hk_ge2 by (by100 simp)
                \<comment> \<open>k = n-1: diagonal IS edge n-1. Use old C9 at (n-1, n-1) to get t = s.\<close>
                \<comment> \<open>k=n-1: diagonal IS edge n-1. diagonal(t) = edge(n-1, 1-t).\<close>
                have h1mt: "1 - t \<in> {0<..<(1::real)}" using ht by (by100 auto)
                have h1ms: "1 - s \<in> {0<..<(1::real)}" using hs by (by100 auto)
                have hnm1: "?n - 1 < ?n" using hn_ge3 by (by100 linarith)
                have hSuc_nm1: "Suc (?n - 1) mod ?n = 0" using hn_ge3 by (by100 simp)
                \<comment> \<open>diagonal(t) = (1-t)*v\\_0 + t*v\\_{n-1} = edge(n-1, 1-t).\<close>
                have hedge_i: "((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) =
                  ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n))"
                  using \<open>?k = ?n - 1\<close> hSuc_nm1 by (by100 simp)
                have hedge_j: "((1-s)*vx2 0 + s*vx2 ?k, (1-s)*vy2 0 + s*vy2 ?k) =
                  ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))"
                  using \<open>?k = ?n - 1\<close> hSuc_nm1 by (by100 simp)
                \<comment> \<open>q2 equality on edge n-1.\<close>
                have hq2_diag: "q2 ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) =
                  q2 ((1-s)*vx2 0 + s*vx2 ?k, (1-s)*vy2 0 + s*vy2 ?k)"
                  using hq2_eq hsigma_i hsigma_j by (by100 simp)
                have hq2_edge: "q2 ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n)) =
                  q2 ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))"
                proof -
                  from arg_cong[OF hedge_i, of q2]
                  have "q2 ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k) =
                    q2 ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                     (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n))" .
                  moreover from arg_cong[OF hedge_j, of q2]
                  have "q2 ((1-s)*vx2 0 + s*vx2 ?k, (1-s)*vy2 0 + s*vy2 ?k) =
                    q2 ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                     (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))" .
                  ultimately show ?thesis using hq2_diag by (by100 simp)
                qed
                \<comment> \<open>Old C9 at (n-1, n-1): gives 1-t = 1-s.\<close>
                from hC9_2[rule_format, OF hnm1 hnm1 h1mt h1ms hq2_edge]
                have "(1-t) = (1-s)"
                proof (elim disjE conjE)
                  assume "?n - 1 = ?n - 1" "1 - t = 1 - s"
                  thus "(1-t) = (1-s)" by (by100 simp)
                next
                  assume "fst(?w!(?n-1)) = fst(?w!(?n-1))"
                    and hif: "if snd(?w!(?n-1)) = snd(?w!(?n-1)) then 1-s = 1-t else 1-s = 1-(1-t)"
                  from hif show "(1-t) = (1-s)" by (by100 simp)
                qed
                hence "t = s" by (by100 linarith)
                thus ?thesis using hsigma_i hsigma_j by (by100 simp)
              qed
              hence ht_eq_s: "t = s"
              proof -
                from \<open>paste_sigma vx2 vy2 ?k ?n i t = paste_sigma vx2 vy2 ?k ?n j s\<close>
                     hsigma_i hsigma_j
                have "(1-t)*vx2 0 + t*vx2 ?k = (1-s)*vx2 0 + s*vx2 ?k" by simp
                hence "(t - s) * (vx2 ?k - vx2 0) = 0" by (by100 algebra)
                moreover have "vx2 ?k \<noteq> vx2 0 \<or> vy2 ?k \<noteq> vy2 0"
                  using hC3_2[rule_format] hk_ge2 hn_ge3 by (by100 force)
                moreover have "(1-t)*vy2 0 + t*vy2 ?k = (1-s)*vy2 0 + s*vy2 ?k"
                  using \<open>paste_sigma vx2 vy2 ?k ?n i t = paste_sigma vx2 vy2 ?k ?n j s\<close>
                        hsigma_i hsigma_j by simp
                hence "(t - s) * (vy2 ?k - vy2 0) = 0" by (by100 algebra)
                ultimately show "t = s" by (by100 auto)
              qed
              \<comment> \<open>Labels: both i, j \\<in> \\{0, n-1\\}, both have label c, direction True.\<close>
              have hfst_c_i: "fst(?w'!i) = c"
              proof -
                from True show ?thesis
                proof (elim disjE)
                  assume "i = 0" thus ?thesis by simp
                next
                  assume "i = ?n - 1"
                  have "last ?w' = (c, True)" by simp
                  moreover have "?w' ! (?n - 1) = last ?w'"
                    using last_conv_nth[of ?w'] hn_ge3 hlen_eq by simp
                  ultimately show ?thesis using \<open>i = ?n - 1\<close> hlen_eq by simp
                qed
              qed
              have hfst_c_j: "fst(?w'!j) = c"
              proof -
                from True2 show ?thesis
                proof (elim disjE)
                  assume "j = 0" thus ?thesis by simp
                next
                  assume "j = ?n - 1"
                  have "last ?w' = (c, True)" by simp
                  moreover have "?w' ! (?n - 1) = last ?w'"
                    using last_conv_nth[of ?w'] hn_ge3 hlen_eq by simp
                  ultimately show ?thesis using \<open>j = ?n - 1\<close> hlen_eq by simp
                qed
              qed
              show ?thesis
              proof (cases "i = j")
                case True thus ?thesis using ht_eq_s by simp
              next
                case False
                hence "fst(?w'!i) = fst(?w'!j)" using hfst_c_i hfst_c_j by simp
                moreover have "snd(?w'!i) = snd(?w'!j)"
                proof -
                  have "snd(?w'!i) = True"
                  proof -
                    from True show ?thesis
                    proof (elim disjE)
                      assume "i = 0" thus ?thesis by simp
                    next
                      assume "i = ?n - 1"
                      have "last ?w' = (c, True)" by simp
                      moreover have "?w' ! (?n - 1) = last ?w'"
                        using last_conv_nth[of ?w'] hn_ge3 hlen_eq by simp
                      ultimately show ?thesis using \<open>i = ?n - 1\<close> hlen_eq by simp
                    qed
                  qed
                  moreover have "snd(?w'!j) = True"
                  proof -
                    from True2 show ?thesis
                    proof (elim disjE)
                      assume "j = 0" thus ?thesis by simp
                    next
                      assume "j = ?n - 1"
                      have "last ?w' = (c, True)" by simp
                      moreover have "?w' ! (?n - 1) = last ?w'"
                        using last_conv_nth[of ?w'] hn_ge3 hlen_eq by simp
                      ultimately show ?thesis using \<open>j = ?n - 1\<close> hlen_eq by simp
                    qed
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis using ht_eq_s by simp
              qed
            next
              case False2: False
              \<comment> \<open>i c-edge, j not c-edge. sigma(i,t) diagonal (interior), sigma(j,s) on old edge.
                 Old C8: interior \\<noteq> boundary under q2. Contradiction.\<close>
              \<comment> \<open>sigma(i,t) is on diagonal (interior), sigma(j,s) is on old edge (boundary).
                 Old C8 at sigma(i,t): forces sigma(i,t) = sigma(j,s). But they differ.\<close>
              \<comment> \<open>sigma(i,t) diagonal (interior), sigma(j,s) on old edge.
                 Old C8 forces sigma(i,t) = sigma(j,s), contradicting interior \\<noteq> boundary.\<close>
              \<comment> \<open>sigma(i,t) on diagonal (interior). sigma(j,s) on old edge.\<close>
              have hj_not_c: "j \<noteq> 0" "j \<noteq> ?n - 1" using False2 by (by100 simp)+
              have hsigma_i_diag: "paste_sigma vx2 vy2 ?k ?n i t = ((1-t)*vx2 0 + t*vx2 ?k, (1-t)*vy2 0 + t*vy2 ?k)"
                using True unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by (by100 simp)
              \<comment> \<open>Case split: k < n-1 uses hdiag + C8, k = n-1 uses C9 + freshness.\<close>
              show ?thesis
              proof (cases "?k < ?n - 1")
                case hk_lt: True
                \<comment> \<open>k < n-1: diagonal not on edge. C8 gives sigma equality, contradicting edge membership.\<close>
                have hsigma_i_int: "\<forall>i'<?n. \<forall>t'\<in>I_set.
                  paste_sigma vx2 vy2 ?k ?n i t \<noteq>
                    ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
                  using hdiag_not_on_edge[OF ht] hsigma_i_diag by (by100 simp)
                have hsigma_i_in: "paste_sigma vx2 vy2 ?k ?n i t \<in> P2"
                  using hsigma_in_P2[OF hi' ht_I] .
                have hsigma_j_in: "paste_sigma vx2 vy2 ?k ?n j s \<in> P2"
                  using hsigma_in_P2[OF hj' hs_I] .
                have "paste_sigma vx2 vy2 ?k ?n i t = paste_sigma vx2 vy2 ?k ?n j s"
                  using hC8_2 hsigma_i_in hsigma_i_int hsigma_j_in hq2_eq by (by100 blast)
                moreover have "\<exists>i'<?n. \<exists>t'\<in>I_set.
                  paste_sigma vx2 vy2 ?k ?n j s =
                    ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
                proof -
                  from hnonc_sigma_on_edge[OF hj' hj_not_c(1) hj_not_c(2) hs]
                  obtain i'' t'' where "i'' < ?n" "t'' \<in> {0<..<(1::real)}"
                    "paste_sigma vx2 vy2 ?k ?n j s =
                      ((1-t'')*vx2 i'' + t''*vx2(Suc i'' mod ?n), (1-t'')*vy2 i'' + t''*vy2(Suc i'' mod ?n))"
                    by (by100 blast)
                  moreover have "t'' \<in> I_set" using \<open>t'' \<in> {0<..<(1::real)}\<close>
                    unfolding top1_unit_interval_def by (by100 auto)
                  ultimately show ?thesis by (by100 blast)
                qed
                ultimately show ?thesis using hsigma_i_int by (by100 auto)
              next
                case hk_eq: False
                hence "?k = ?n - 1" using hk_ge2 by (by100 simp)
                \<comment> \<open>k = n-1: diagonal IS edge n-1. Use C9 + a-freshness for contradiction.
                   sigma(i,t) on edge n-1 at 1-t. sigma(j,s) on old edge j\\_old.
                   C9 at (n-1, j\\_old): either n-1 = j\\_old (impossible: j\\_old \\<le> n-2)
                   or label match (impossible: w!(n-1) = (a,T) and a fresh in u2).\<close>
                \<comment> \<open>Compute sigma(j,s) directly on old edge k-j (bypass existential).\<close>
                have hj1: "j \<ge> 1" using hj_not_c(1) by (by100 linarith)
                have hjk1: "j \<le> ?k - 1" using hj_not_c(2) hj' \<open>?k = ?n - 1\<close> by (by100 linarith)
                have hkj_lt: "?k - j < ?n" using hjk1 by (by100 simp)
                have hkj_ne: "?k - j \<noteq> ?n - 1" using hj1 \<open>?k = ?n - 1\<close> by (by100 linarith)
                have h1ms: "(1-s) \<in> {0<..<(1::real)}" using hs by (by100 auto)
                have h1mt: "1 - t \<in> {0<..<(1::real)}" using ht by (by100 auto)
                have hnm1: "?n - 1 < ?n" using hn_ge3 by (by100 linarith)
                \<comment> \<open>Sigma(j,s) = edge(k-j, 1-s).\<close>
                have hSuc_kj: "Suc (?k - j) mod ?n = ?k + 1 - j"
                proof -
                  have "?k - j < ?n - 1" using hj1 hkj_ne hkj_lt by (by100 linarith)
                  hence "Suc (?k - j) < ?n" by (by100 simp)
                  hence "Suc (?k - j) mod ?n = Suc (?k - j)" by (by100 simp)
                  also have "Suc (?k - j) = ?k + 1 - j" using hjk1 by (by100 simp)
                  finally show ?thesis .
                qed
                have hsigma_j_kj: "paste_sigma vx2 vy2 ?k ?n j s =
                  ((1-(1-s))*vx2(?k-j) + (1-s)*vx2(Suc(?k-j) mod ?n),
                   (1-(1-s))*vy2(?k-j) + (1-s)*vy2(Suc(?k-j) mod ?n))"
                proof -
                  have hsx: "paste_chain_sigma_x vx2 ?k ?n j s = s*vx2(?k-j) + (1-s)*vx2(?k+1-j)"
                    using hj_not_c(1) hj_not_c(2) hjk1 unfolding paste_chain_sigma_x_def by (by100 simp)
                  have hsy: "paste_chain_sigma_y vy2 ?k ?n j s = s*vy2(?k-j) + (1-s)*vy2(?k+1-j)"
                    using hj_not_c(1) hj_not_c(2) hjk1 unfolding paste_chain_sigma_y_def by (by100 simp)
                  show ?thesis using hsx hsy hSuc_kj by (by100 simp)
                qed
                \<comment> \<open>Sigma(i,t) = edge(n-1, 1-t).\<close>
                have hSuc_nm1: "Suc (?n - 1) mod ?n = 0" using hn_ge3 by (by100 simp)
                have hsigma_i_edge: "paste_sigma vx2 vy2 ?k ?n i t =
                  ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n))"
                  using hsigma_i_diag \<open>?k = ?n - 1\<close> hSuc_nm1 by (by100 simp)
                \<comment> \<open>q2 on edges n-1 and k-j.\<close>
                have hq2_kj: "q2 ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n)) =
                  q2 ((1-(1-s))*vx2(?k-j) + (1-s)*vx2(Suc(?k-j) mod ?n),
                   (1-(1-s))*vy2(?k-j) + (1-s)*vy2(Suc(?k-j) mod ?n))"
                proof -
                  from arg_cong[OF hsigma_i_edge, of q2]
                  have "q2 (paste_sigma vx2 vy2 ?k ?n i t) =
                    q2 ((1-(1-t))*vx2(?n-1) + (1-t)*vx2(Suc(?n-1) mod ?n),
                     (1-(1-t))*vy2(?n-1) + (1-t)*vy2(Suc(?n-1) mod ?n))" by (by100 simp)
                  moreover from arg_cong[OF hsigma_j_kj, of q2]
                  have "q2 (paste_sigma vx2 vy2 ?k ?n j s) =
                    q2 ((1-(1-s))*vx2(?k-j) + (1-s)*vx2(Suc(?k-j) mod ?n),
                     (1-(1-s))*vy2(?k-j) + (1-s)*vy2(Suc(?k-j) mod ?n))" by (by100 simp)
                  ultimately show ?thesis using hq2_eq by (by100 simp)
                qed
                \<comment> \<open>Old C9 at (n-1, k-j). n-1 \\<noteq> k-j and labels don't match (a fresh in u2).\<close>
                from hC9_2[rule_format, OF hnm1 hkj_lt h1mt h1ms hq2_kj]
                have "(?n-1 = ?k-j \<and> 1-t = 1-s) \<or>
                  (fst(?w!(?n-1)) = fst(?w!(?k-j)) \<and>
                    (if snd(?w!(?n-1)) = snd(?w!(?k-j)) then 1-s = 1-t else 1-s = 1-(1-t)))" .
                hence False
                proof (elim disjE conjE)
                  assume "?n - 1 = ?k - j"
                  with hkj_ne show False by (by100 simp)
                next
                  assume "fst(?w!(?n-1)) = fst(?w!(?k-j))"
                  have "fst(?w!(?n-1)) = a" using \<open>?k = ?n - 1\<close> by (by100 simp)
                  hence hfst_a: "fst(?w!(?k-j)) = a" using \<open>fst(?w!(?n-1)) = fst(?w!(?k-j))\<close> by (by100 simp)
                  \<comment> \<open>w!(k-j) = u2!(k-j-1) since 1 \\<le> k-j \\<le> k-1 = length u2.\<close>
                  have hkj_ge1: "?k - j \<ge> 1" using hjk1 by (by100 linarith)
                  have hkj_le: "?k - j \<le> length u2" using hj1 by (by100 simp)
                  have hkjm1: "?k - j - 1 < length u2" using hkj_ge1 hkj_le by (by100 linarith)
                  have "?w ! (?k-j) = ((a,True) # u2 @ [(a,True)] @ v) ! (?k-j)" by (by100 simp)
                  also have "\<dots> = (u2 @ [(a,True)] @ v) ! (?k-j-1)" using hkj_ge1 by (by100 simp)
                  also have "\<dots> = u2 ! (?k-j-1)"
                    using hkjm1 nth_append[of u2 "[(a,True)] @ v" "?k-j-1"] by (by100 simp)
                  finally have hw_kj: "?w ! (?k-j) = u2 ! (?k-j-1)" .
                  have "u2 ! (?k-j-1) \<in> set u2" using hkjm1 by (by100 simp)
                  hence "fst(u2 ! (?k-j-1)) \<in> fst ` set u2" by (by100 force)
                  hence "fst(u2 ! (?k-j-1)) \<noteq> a" using ha_fresh_u2 by (by100 auto)
                  hence "fst(?w!(?k-j)) \<noteq> a" using hw_kj by (by100 simp)
                  with hfst_a show False by (by100 simp)
                qed
                thus ?thesis by (by100 blast)
              qed
            qed
          next
            case False hence hi_not_c: "i \<noteq> 0" "i \<noteq> ?n - 1" by simp+
            show ?thesis
            proof (cases "j = 0 \<or> j = ?n - 1")
              case True2: True
              \<comment> \<open>j c-edge, i not c-edge. Symmetric to c vs non-c above.\<close>
              have hsigma_j_diag: "paste_sigma vx2 vy2 ?k ?n j s = ((1-s)*vx2 0 + s*vx2 ?k, (1-s)*vy2 0 + s*vy2 ?k)"
                using True2 unfolding paste_chain_sigma_x_def paste_chain_sigma_y_def by (by100 simp)
              \<comment> \<open>Symmetric case split: k < n-1 vs k = n-1.\<close>
              show ?thesis
              proof (cases "?k < ?n - 1")
                case hk_lt: True
                have hsigma_j_int: "\<forall>j'<?n. \<forall>s'\<in>I_set.
                  paste_sigma vx2 vy2 ?k ?n j s \<noteq>
                    ((1-s')*vx2 j' + s'*vx2(Suc j' mod ?n), (1-s')*vy2 j' + s'*vy2(Suc j' mod ?n))"
                  using hdiag_not_on_edge[OF hs] hsigma_j_diag by (by100 simp)
                have hsigma_j_in: "paste_sigma vx2 vy2 ?k ?n j s \<in> P2"
                  using hsigma_in_P2[OF hj' hs_I] .
                have hsigma_i_in: "paste_sigma vx2 vy2 ?k ?n i t \<in> P2"
                  using hsigma_in_P2[OF hi' ht_I] .
                have hq2_eq_sym: "q2 (paste_sigma vx2 vy2 ?k ?n j s) = q2 (paste_sigma vx2 vy2 ?k ?n i t)"
                  using hq2_eq by (by100 simp)
                have "paste_sigma vx2 vy2 ?k ?n j s = paste_sigma vx2 vy2 ?k ?n i t"
                  using hC8_2 hsigma_j_in hsigma_j_int hsigma_i_in hq2_eq_sym by (by100 blast)
                moreover have "\<exists>i'<?n. \<exists>t'\<in>I_set.
                  paste_sigma vx2 vy2 ?k ?n i t =
                    ((1-t')*vx2 i' + t'*vx2(Suc i' mod ?n), (1-t')*vy2 i' + t'*vy2(Suc i' mod ?n))"
                proof -
                  from hnonc_sigma_on_edge[OF hi' hi_not_c(1) hi_not_c(2) ht]
                  obtain i'' t'' where "i'' < ?n" "t'' \<in> {0<..<(1::real)}"
                    "paste_sigma vx2 vy2 ?k ?n i t =
                      ((1-t'')*vx2 i'' + t''*vx2(Suc i'' mod ?n), (1-t'')*vy2 i'' + t''*vy2(Suc i'' mod ?n))"
                  by (by100 blast)
                moreover have "t'' \<in> I_set" using \<open>t'' \<in> {0<..<(1::real)}\<close>
                  unfolding top1_unit_interval_def by (by100 auto)
                ultimately show ?thesis by (by100 blast)
              qed
              ultimately show ?thesis using hsigma_j_int by (by100 auto)
              next
                case hk_eq: False
                hence "?k = ?n - 1" using hk_ge2 by (by100 simp)
                \<comment> \<open>k=n-1: symmetric to c-vs-nonc k=n-1 case. Diagonal IS edge n-1.
                   Use C9 + a-freshness for contradiction.\<close>
                \<comment> \<open>Symmetric: compute sigma(i,t) directly on old edge k-i.\<close>
                have hi1: "i \<ge> 1" using hi_not_c(1) by (by100 linarith)
                have hik1: "i \<le> ?k - 1" using hi_not_c(2) hi' \<open>?k = ?n - 1\<close> by (by100 linarith)
                have hki_lt: "?k - i < ?n" using hik1 by (by100 simp)
                have hki_ne: "?k - i \<noteq> ?n - 1" using hi1 \<open>?k = ?n - 1\<close> by (by100 linarith)
                have h1mt: "(1-t) \<in> {0<..<(1::real)}" using ht by (by100 auto)
                have h1ms: "1 - s \<in> {0<..<(1::real)}" using hs by (by100 auto)
                have hnm1: "?n - 1 < ?n" using hn_ge3 by (by100 linarith)
                have hSuc_ki: "Suc (?k - i) mod ?n = ?k + 1 - i"
                proof -
                  have "?k - i < ?n - 1" using hi1 hki_ne hki_lt by (by100 linarith)
                  hence "Suc (?k - i) < ?n" by (by100 simp)
                  hence "Suc (?k - i) mod ?n = Suc (?k - i)" by (by100 simp)
                  also have "Suc (?k - i) = ?k + 1 - i" using hik1 by (by100 simp)
                  finally show ?thesis .
                qed
                have hsigma_i_ki: "paste_sigma vx2 vy2 ?k ?n i t =
                  ((1-(1-t))*vx2(?k-i) + (1-t)*vx2(Suc(?k-i) mod ?n),
                   (1-(1-t))*vy2(?k-i) + (1-t)*vy2(Suc(?k-i) mod ?n))"
                proof -
                  have hsx: "paste_chain_sigma_x vx2 ?k ?n i t = t*vx2(?k-i) + (1-t)*vx2(?k+1-i)"
                    using hi_not_c(1) hi_not_c(2) hik1 unfolding paste_chain_sigma_x_def by (by100 simp)
                  have hsy: "paste_chain_sigma_y vy2 ?k ?n i t = t*vy2(?k-i) + (1-t)*vy2(?k+1-i)"
                    using hi_not_c(1) hi_not_c(2) hik1 unfolding paste_chain_sigma_y_def by (by100 simp)
                  show ?thesis using hsx hsy hSuc_ki by (by100 simp)
                qed
                have hSuc_nm1: "Suc (?n - 1) mod ?n = 0" using hn_ge3 by (by100 simp)
                have hsigma_j_edge: "paste_sigma vx2 vy2 ?k ?n j s =
                  ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))"
                  using hsigma_j_diag \<open>?k = ?n - 1\<close> hSuc_nm1 by (by100 simp)
                have hq2_ki: "q2 ((1-(1-t))*vx2(?k-i) + (1-t)*vx2(Suc(?k-i) mod ?n),
                   (1-(1-t))*vy2(?k-i) + (1-t)*vy2(Suc(?k-i) mod ?n)) =
                  q2 ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                   (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))"
                proof -
                  from arg_cong[OF hsigma_i_ki, of q2]
                  have "q2 (paste_sigma vx2 vy2 ?k ?n i t) =
                    q2 ((1-(1-t))*vx2(?k-i) + (1-t)*vx2(Suc(?k-i) mod ?n),
                     (1-(1-t))*vy2(?k-i) + (1-t)*vy2(Suc(?k-i) mod ?n))" by (by100 simp)
                  moreover from arg_cong[OF hsigma_j_edge, of q2]
                  have "q2 (paste_sigma vx2 vy2 ?k ?n j s) =
                    q2 ((1-(1-s))*vx2(?n-1) + (1-s)*vx2(Suc(?n-1) mod ?n),
                     (1-(1-s))*vy2(?n-1) + (1-s)*vy2(Suc(?n-1) mod ?n))" by (by100 simp)
                  ultimately show ?thesis using hq2_eq by (by100 simp)
                qed
                from hC9_2[rule_format, OF hki_lt hnm1 h1mt h1ms hq2_ki]
                have "(?k-i = ?n-1 \<and> 1-t = 1-s) \<or>
                  (fst(?w!(?k-i)) = fst(?w!(?n-1)) \<and>
                    (if snd(?w!(?k-i)) = snd(?w!(?n-1)) then 1-s = 1-t else 1-s = 1-(1-t)))" .
                hence False
                proof (elim disjE conjE)
                  assume "?k - i = ?n - 1"
                  with hki_ne show False by (by100 simp)
                next
                  assume "fst(?w!(?k-i)) = fst(?w!(?n-1))"
                  have "fst(?w!(?n-1)) = a" using \<open>?k = ?n - 1\<close> by (by100 simp)
                  hence hfst_a: "fst(?w!(?k-i)) = a" using \<open>fst(?w!(?k-i)) = fst(?w!(?n-1))\<close> by (by100 simp)
                  have hki_ge1: "?k - i \<ge> 1" using hik1 by (by100 linarith)
                  have hki_le: "?k - i \<le> length u2" using hi1 by (by100 simp)
                  have hkim1: "?k - i - 1 < length u2" using hki_ge1 hki_le by (by100 linarith)
                  have "?w ! (?k-i) = ((a,True) # u2 @ [(a,True)] @ v) ! (?k-i)" by (by100 simp)
                  also have "\<dots> = (u2 @ [(a,True)] @ v) ! (?k-i-1)" using hki_ge1 by (by100 simp)
                  also have "\<dots> = u2 ! (?k-i-1)"
                    using hkim1 nth_append[of u2 "[(a,True)] @ v" "?k-i-1"] by (by100 simp)
                  finally have hw_ki: "?w ! (?k-i) = u2 ! (?k-i-1)" .
                  have "u2 ! (?k-i-1) \<in> set u2" using hkim1 by (by100 simp)
                  hence "fst(u2 ! (?k-i-1)) \<in> fst ` set u2" by (by100 force)
                  hence "fst(u2 ! (?k-i-1)) \<noteq> a" using ha_fresh_u2 by (by100 auto)
                  hence "fst(?w!(?k-i)) \<noteq> a" using hw_ki by (by100 simp)
                  with hfst_a show False by (by100 simp)
                qed
                thus ?thesis by (by100 blast)
              qed
            next
              case False2: False hence hj_not_c: "j \<noteq> 0" "j \<noteq> ?n - 1" by simp+
              \<comment> \<open>Both non-c-edges. sigma maps to old edges.
                 Use old C9 on the old edges, then translate via target label correspondence.\<close>
              \<comment> \<open>Both non-c. sigma maps to old edges. Get old edge indices/params.\<close>
              \<comment> \<open>Use full dictionary for i and j.\<close>
              from hnonc_sigma_dict[OF hi' hi_not_c(1) hi_not_c(2) ht]
              obtain i_old ri where hdict_i:
                "i_old < ?n"
                "(if ri then 1 - t else t) \<in> {0<..<(1::real)}"
                "paste_sigma vx2 vy2 ?k ?n i t =
                  ((1-(if ri then 1-t else t))*vx2 i_old +
                   (if ri then 1-t else t)*vx2(Suc i_old mod ?n),
                   (1-(if ri then 1-t else t))*vy2 i_old +
                   (if ri then 1-t else t)*vy2(Suc i_old mod ?n))"
                "fst (?w' ! i) = fst (?w ! i_old)"
                "(snd (?w' ! i) = snd (?w ! i_old)) = (\<not> ri)"
                "i_old = (if ri then ?k - i else Suc i)"
                "if ri then i \<le> ?k - 1 else i \<ge> ?k"
                by (by5000 blast)
              have hrange_i: "if ri then i \<le> ?k - 1 else i \<ge> ?k"
                using hdict_i(7) .
              from hnonc_sigma_dict[OF hj' hj_not_c(1) hj_not_c(2) hs]
              obtain j_old rj where hdict_j:
                "j_old < ?n"
                "(if rj then 1 - s else s) \<in> {0<..<(1::real)}"
                "paste_sigma vx2 vy2 ?k ?n j s =
                  ((1-(if rj then 1-s else s))*vx2 j_old +
                   (if rj then 1-s else s)*vx2(Suc j_old mod ?n),
                   (1-(if rj then 1-s else s))*vy2 j_old +
                   (if rj then 1-s else s)*vy2(Suc j_old mod ?n))"
                "fst (?w' ! j) = fst (?w ! j_old)"
                "(snd (?w' ! j) = snd (?w ! j_old)) = (\<not> rj)"
                "j_old = (if rj then ?k - j else Suc j)"
                "if rj then j \<le> ?k - 1 else j \<ge> ?k"
                by (by5000 blast)
              have hrange_j: "if rj then j \<le> ?k - 1 else j \<ge> ?k"
                using hdict_j(7) .
              \<comment> \<open>q2 equality on old edges.\<close>
              let ?ti = "if ri then 1 - t else t"
              let ?tj = "if rj then 1 - s else s"
              have hq2_old: "q2 ((1-?ti)*vx2 i_old + ?ti*vx2(Suc i_old mod ?n),
                                 (1-?ti)*vy2 i_old + ?ti*vy2(Suc i_old mod ?n))
                           = q2 ((1-?tj)*vx2 j_old + ?tj*vx2(Suc j_old mod ?n),
                                 (1-?tj)*vy2 j_old + ?tj*vy2(Suc j_old mod ?n))"
                using hq2_eq hdict_i(3) hdict_j(3) by (by100 simp)
              \<comment> \<open>Apply old C9.\<close>
              from hC9_2[rule_format, OF hdict_i(1) hdict_j(1) hdict_i(2) hdict_j(2) hq2_old]
              have hold_C9: "(i_old=j_old \<and> ?ti=?tj) \<or>
                (fst(?w!i_old)=fst(?w!j_old) \<and>
                  (if snd(?w!i_old)=snd(?w!j_old) then ?tj=?ti else ?tj=1-?ti))" .
              \<comment> \<open>Apply paste\\_sigma\\_non\\_c\\_C9\\_transport.\<close>
              have hpar_i: "?ti = (if ri then 1 - t else t)" by (by100 simp)
              have hpar_j: "?tj = (if rj then 1 - s else s)" by (by100 simp)
              from paste_sigma_non_c_C9_transport[OF hdict_i(4) hdict_i(5) hpar_i
                hdict_j(4) hdict_j(5) hpar_j hold_C9]
              have htransport: "(i_old = j_old \<and> t = s) \<or>
                (fst (?w' ! i) = fst (?w' ! j) \<and>
                  (if snd (?w' ! i) = snd (?w' ! j) then s = t else s = 1 - t))" .
              \<comment> \<open>Close the C9 goal.\<close>
              from htransport show ?thesis
              proof (elim disjE conjE)
                assume "i_old = j_old" "t = s"
                \<comment> \<open>From i\\_old formula: both = (if ri then k-i else Suc i) = (if rj then k-j else Suc j).\<close>
                \<comment> \<open>From i\\_old = j\\_old + formula: i = j (injective mapping).\<close>
                have "i = j"
                proof (cases ri; cases rj)
                  assume "ri" "rj" \<comment> \<open>Both left: k - i = k - j.\<close>
                  hence "?k - i = ?k - j" using \<open>i_old = j_old\<close> hdict_i(6) hdict_j(6) by (by100 simp)
                  moreover have "i \<le> ?k" using hrange_i \<open>ri\<close> by (by100 simp)
                  moreover have "j \<le> ?k" using hrange_j \<open>rj\<close> by (by100 simp)
                  ultimately show "i = j" by (by100 linarith)
                next
                  assume "ri" "\<not>rj" \<comment> \<open>Cross: k - i = Suc j. Ranges disjoint.\<close>
                  hence "?k - i = Suc j" using \<open>i_old = j_old\<close> hdict_i(6) hdict_j(6) by (by100 simp)
                  moreover have "?k - i \<le> ?k - 1" using hrange_i \<open>ri\<close> hi_not_c(1) by (by100 linarith)
                  moreover have "Suc j \<ge> Suc ?k" using hrange_j \<open>\<not>rj\<close> by (by100 simp)
                  ultimately have False by (by100 linarith)
                  thus "i = j" by (by100 blast)
                next
                  assume "\<not>ri" "rj" \<comment> \<open>Cross: Suc i = k - j. Ranges disjoint.\<close>
                  hence "Suc i = ?k - j" using \<open>i_old = j_old\<close> hdict_i(6) hdict_j(6) by (by100 simp)
                  moreover have "Suc i \<ge> Suc ?k" using hrange_i \<open>\<not>ri\<close> by (by100 simp)
                  moreover have "?k - j \<le> ?k - 1" using hrange_j \<open>rj\<close> hj_not_c(1) by (by100 linarith)
                  ultimately have False by (by100 linarith)
                  thus "i = j" by (by100 blast)
                next
                  assume "\<not>ri" "\<not>rj" \<comment> \<open>Both right: Suc i = Suc j.\<close>
                  thus "i = j" using \<open>i_old = j_old\<close> hdict_i(6) hdict_j(6) by (by100 simp)
                qed
                with \<open>t = s\<close> show ?thesis by (by100 simp)
              next
                assume "fst (?w' ! i) = fst (?w' ! j)"
                  "if snd (?w' ! i) = snd (?w' ! j) then s = t else s = 1 - t"
                thus ?thesis using hi' hj' hlen_eq by (by100 auto)
              qed
            qed
          qed
        qed
        show "\<forall>i<length ?w'. let cx=(\<Sum>j<length ?w'. vx2 j)/real(length ?w');
            cy=(\<Sum>j<length ?w'. vy2 j)/real(length ?w')
            in (vx2 i-cx)*(vy2(Suc i mod length ?w')-cy)-(vy2 i-cy)*(vx2(Suc i mod length ?w')-cx)>0"
          by (rule hC10')
        show "\<forall>i<length ?w'. \<forall>k<length ?w'. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length ?w' \<longrightarrow>
            (vx2 k-vx2 i)*(vy2(Suc i mod length ?w')-vy2 i)-(vy2 k-vy2 i)*(vx2(Suc i mod length ?w')-vx2 i)<0"
          by (rule hC11')
      qed
    qed
  qed
  qed
  qed
qed


end































