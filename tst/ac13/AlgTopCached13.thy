theory AlgTopCached13
  imports "AlgTopCached12.AlgTopCached12"
begin


\<comment> \<open>m\\_projective\\_scheme\\_CW\\_data: REMOVED (unused, was an early CW-structure attempt
   for \\<S>75.4 now cached in ac12). See git history for full proof body.\<close>



(** Theorem 71.3: fully proved and cached in ac9/AlgTopCached9.thy. **)




\<comment> \<open>free\_group\_hom\_subset\_injective + Theorem\_71\_3\_pi1\_free moved to AlgTopCached9.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful) is now Theorem\_71\_3 in AlgTopCached9.
   It states: \\<pi>\\_1(X, p) is free on J (the actual book statement).
   The old int-set packaging wrapper (Theorem\_71\_3\_wedge\_of\_circles\_general)
   was unused dead code and has been removed.\<close>





\<comment> \<open>§71 helpers + §74 moved to AlgTopCached8.\<close>

\<comment> \<open>Elementary scheme operations (Munkres \\<S>76).
   A scheme is a list of (edge\\_name, direction) pairs representing a polygonal identification.
   Elementary operations preserve the quotient homeomorphism type.\<close>

definition top1_inverse_edge :: "'a \<times> bool \<Rightarrow> 'a \<times> bool" where
  "top1_inverse_edge e = (fst e, \<not> snd e)"

inductive top1_elementary_scheme_operation :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  rotate: "top1_elementary_scheme_operation (u @ v) (v @ u)" |
  cancel: "top1_elementary_scheme_operation (u @ [a, top1_inverse_edge a] @ v) (u @ v)" |
  uncancel: "top1_elementary_scheme_operation (u @ v) (u @ [a, top1_inverse_edge a] @ v)" |
  invert: "top1_elementary_scheme_operation w (rev (map top1_inverse_edge w))" |
  \<comment> \<open>Relabel: replace all occurrences of label old by label new.
     Book \\<S>76 operation (iii): "replace all occurrences of any given label by some other
     label that does not appear elsewhere in the scheme."\<close>
  relabel: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (if l = old then new else l, b)) w)" |
  \<comment> \<open>Flip orientation: change sign of exponent of all occurrences of a given label.
     Book \\<S>76 operation (iii): "one can change the sign of the exponent of all occurrences
     of a given label a; this amounts to reversing the orientations of all edges labelled a."\<close>
  flip_label: "top1_elementary_scheme_operation w (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) w)" |
  \<comment> \<open>Cut-and-repaste: the combined effect of Munkres \\<S>76 Theorem 76.1 on a single polygon.
     Cut at position between u1 and u2, introducing new label c.
     Flip one piece. Paste along label a (which appears in both pieces).
     Net effect on scheme: [u1] a [u2] a [u3] \\<sim> [u1] a a [u2\\<inverse>] [u3].
     This brings two copies of label a (same orientation) together.
     Formally: rotate one piece around and paste, cancelling u2 into u2\\<inverse>.\<close>
  cut_paste: "top1_elementary_scheme_operation
      (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)
      (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)" |
  \<comment> \<open>Cut-paste variant 2 (Figure 77.2): rearrange with a new label.
     Transforms y0 a y1 a y2 into b y2 b (y1 y0\\<inverse>) where b is new.
     This is the book's Figure 77.2 operation from \\<S>77 Lemma 77.1 Step 2.\<close>
  cut_paste2: "top1_elementary_scheme_operation
      (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)
      ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))" |
  \<comment> \<open>Cut-paste for opposite-orientation labels (Figure 77.3).
     Net effect: move u1 from before a to after a\\<inverse>.
     u0 @ u1 @ [(a,T)] @ u2 @ [(a,F)] @ u3 \\<to> u0 @ [(a,T)] @ u2 @ [(a,F)] @ u1 @ u3.\<close>
  cut_paste_opp: "top1_elementary_scheme_operation
      (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)
      (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)" |
  \<comment> \<open>Context rule: any elementary operation can be performed with a prefix.
     This makes scheme\_equiv a congruence on the left: if y ~ z then prefix@y ~ prefix@z.\<close>
  context_left: "top1_elementary_scheme_operation y z \<Longrightarrow>
      top1_elementary_scheme_operation (prefix @ y) (prefix @ z)"

\<comment> \<open>The scheme equivalence is the reflexive-transitive closure of elementary operations.\<close>
definition top1_scheme_equiv :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  "top1_scheme_equiv = top1_elementary_scheme_operation\<^sup>*\<^sup>*"

\<comment> \<open>Labels appearing in a scheme.\<close>
definition scheme_labels :: "('a \<times> bool) list \<Rightarrow> 'a set" where
  "scheme_labels w = fst ` set w"

\<comment> \<open>Valid elementary operation: same as above but with freshness side conditions
   where the book requires them (relabel, uncancel, cut\\_paste2).
   Per expert audit 13 step 0.\<close>
inductive top1_valid_scheme_operation :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  v_rotate: "top1_valid_scheme_operation (u @ v) (v @ u)" |
  v_cancel: "top1_valid_scheme_operation (u @ [a, top1_inverse_edge a] @ v) (u @ v)" |
  v_uncancel: "fst a \<notin> scheme_labels (u @ v) \<Longrightarrow>
    top1_valid_scheme_operation (u @ v) (u @ [a, top1_inverse_edge a] @ v)" |
  v_invert: "top1_valid_scheme_operation w (rev (map top1_inverse_edge w))" |
  v_relabel: "\<lbrakk>new \<notin> fst ` set w; new \<noteq> old\<rbrakk> \<Longrightarrow>
    top1_valid_scheme_operation w (map (\<lambda>(l,b). (if l = old then new else l, b)) w)" |
  v_flip_label: "top1_valid_scheme_operation w (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) w)" |
  v_cut_paste: "top1_valid_scheme_operation
      (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)
      (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)" |
  v_cut_paste2: "\<lbrakk> b \<notin> scheme_labels (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2) \<rbrakk> \<Longrightarrow>
    top1_valid_scheme_operation
      (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)
      ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))" |
  v_cut_paste_opp: "top1_valid_scheme_operation
      (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)
      (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)" |
  \<comment> \<open>Reverse cancel: insert a cancel pair (no freshness needed since it cancels).\<close>
  v_cancel_reverse: "top1_valid_scheme_operation (u @ v) (u @ [a, top1_inverse_edge a] @ v)" |
  \<comment> \<open>Context rule: valid operations can be performed with a prefix.\<close>
  v_context_left: "top1_valid_scheme_operation y z \<Longrightarrow>
      top1_valid_scheme_operation (prefix @ y) (prefix @ z)"

\<comment> \<open>Valid scheme equivalence.\<close>
definition top1_valid_scheme_equiv :: "('a \<times> bool) list \<Rightarrow> ('a \<times> bool) list \<Rightarrow> bool" where
  "top1_valid_scheme_equiv = top1_valid_scheme_operation\<^sup>*\<^sup>*"

\<comment> \<open>Every valid operation is also an unrestricted operation.\<close>
lemma valid_implies_elementary:
  "top1_valid_scheme_operation w w' \<Longrightarrow> top1_elementary_scheme_operation w w'"
  apply (induction rule: top1_valid_scheme_operation.induct)
  apply (rule top1_elementary_scheme_operation.rotate)
  apply (rule top1_elementary_scheme_operation.cancel)
  apply (rule top1_elementary_scheme_operation.uncancel)
  apply (rule top1_elementary_scheme_operation.invert)
  apply (rule top1_elementary_scheme_operation.relabel)
  apply (rule top1_elementary_scheme_operation.flip_label)
  apply (rule top1_elementary_scheme_operation.cut_paste)
  apply (rule top1_elementary_scheme_operation.cut_paste2)
  apply (rule top1_elementary_scheme_operation.cut_paste_opp)
  apply (rule top1_elementary_scheme_operation.uncancel)
  apply (rule top1_elementary_scheme_operation.context_left)
  apply assumption
  done

\<comment> \<open>Valid equivalence implies unrestricted equivalence.\<close>
lemma valid_equiv_implies_equiv:
  "top1_valid_scheme_equiv w w' \<Longrightarrow> top1_scheme_equiv w w'"
  unfolding top1_valid_scheme_equiv_def top1_scheme_equiv_def
  by (induction rule: rtranclp.induct) (by100 simp, meson rtranclp.rtrancl_into_rtrancl valid_implies_elementary)

\<comment> \<open>Valid equivalence: single fresh relabel is a valid equivalence step.\<close>
lemma valid_equiv_fresh_relabel:
  assumes "new \<notin> fst ` set w" and "new \<noteq> old"
  shows "top1_valid_scheme_equiv w (map (\<lambda>(l,b). (if l = old then new else l, b)) w)"
  unfolding top1_valid_scheme_equiv_def
  using top1_valid_scheme_operation.v_relabel[OF assms]
        rtranclp.rtrancl_into_rtrancl[OF rtranclp.rtrancl_refl]
  by (by100 simp)

\<comment> \<open>Valid equivalence: transitivity.\<close>
lemma valid_equiv_trans:
  "top1_valid_scheme_equiv a b \<Longrightarrow> top1_valid_scheme_equiv b c \<Longrightarrow> top1_valid_scheme_equiv a c"
  unfolding top1_valid_scheme_equiv_def by (rule rtranclp_trans)

\<comment> \<open>Valid equivalence: prefix congruence (uses v\\_context\\_left).\<close>
lemma valid_equiv_prepend:
  "top1_valid_scheme_equiv rest rest' \<Longrightarrow> top1_valid_scheme_equiv (prefix @ rest) (prefix @ rest')"
  unfolding top1_valid_scheme_equiv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl thus ?case by (by100 simp)
next
  case (rtrancl_into_rtrancl x y z)
  have "top1_valid_scheme_operation (prefix @ y) (prefix @ z)"
    by (rule top1_valid_scheme_operation.v_context_left[OF rtrancl_into_rtrancl.hyps(2)])
  thus ?case using rtrancl_into_rtrancl.IH by (meson rtranclp.rtrancl_into_rtrancl)
qed

\<comment> \<open>Valid equivalence: suffix congruence (via rotate + prepend + rotate).\<close>
lemma valid_equiv_append:
  "top1_valid_scheme_equiv xs ys \<Longrightarrow> top1_valid_scheme_equiv (xs @ suffix) (ys @ suffix)"
proof -
  assume h: "top1_valid_scheme_equiv xs ys"
  have r1: "top1_valid_scheme_equiv (xs @ suffix) (suffix @ xs)"
    unfolding top1_valid_scheme_equiv_def
    using top1_valid_scheme_operation.v_rotate[of xs suffix] by (by100 simp)
  have r2: "top1_valid_scheme_equiv (suffix @ xs) (suffix @ ys)"
    by (rule valid_equiv_prepend[OF h])
  have r3: "top1_valid_scheme_equiv (suffix @ ys) (ys @ suffix)"
    unfolding top1_valid_scheme_equiv_def
    using top1_valid_scheme_operation.v_rotate[of suffix ys] by (by100 simp)
  from r1 r2 r3 show ?thesis using valid_equiv_trans by (by100 blast)
qed

\<comment> \<open>Single valid operation implies valid equivalence.\<close>
lemma valid_imp_equiv:
  "top1_valid_scheme_operation s t \<Longrightarrow> top1_valid_scheme_equiv s t"
  unfolding top1_valid_scheme_equiv_def by (by100 simp)

\<comment> \<open>Valid relabel is reversible: fresh relabel can be undone.\<close>
lemma valid_relabel_reverse:
  assumes "nw \<notin> fst ` set wd" and "nw \<noteq> ol"
  shows "top1_valid_scheme_equiv (map (\<lambda>(x,b). (if x = ol then nw else x, b)) wd) wd"
proof -
  define t where "t = map (\<lambda>(x,b). (if x = ol then nw else x, b)) wd"
  have hol_fresh: "ol \<notin> fst ` set t"
  proof
    assume "ol \<in> fst ` set t"
    then obtain l b where "(l, b) \<in> set wd" "ol = (if l = ol then nw else l)"
      unfolding t_def by (by100 fastforce)
    then show False using assms(2) by (cases "l = ol") (by100 auto)+
  qed
  have hrev_eq: "map (\<lambda>(x,b). (if x = nw then ol else x, b)) t = wd"
    unfolding t_def using assms(1)
  proof (induction wd)
    case Nil thus ?case by (by100 simp)
  next
    case (Cons e ws)
    obtain l b where hlb: "e = (l, b)" by (cases e)
    have "l \<noteq> nw" using Cons.prems hlb by (by100 force)
    thus ?case using hlb Cons.IH Cons.prems by (by100 simp)
  qed
  have "top1_valid_scheme_operation t (map (\<lambda>(x,b). (if x = nw then ol else x, b)) t)"
    by (rule top1_valid_scheme_operation.v_relabel[OF hol_fresh assms(2)[symmetric]])
  hence "top1_valid_scheme_operation t wd" using hrev_eq by (by100 simp)
  thus ?thesis unfolding t_def by (rule valid_imp_equiv)
qed

\<comment> \<open>Cancel reverse: u@v is validly equivalent to u@[a,inv a]@v.
   Now trivial: v\\_cancel\\_reverse is a primitive valid operation.\<close>
lemma valid_cancel_reverse:
  "top1_valid_scheme_equiv (u @ v) (u @ [a, top1_inverse_edge a] @ v)"
  by (rule valid_imp_equiv[OF top1_valid_scheme_operation.v_cancel_reverse])

\<comment> \<open>Valid relabel to avoid a label: replace all occurrences with a fresh one.\<close>
lemma valid_equiv_relabel_avoid:
  fixes target :: "(nat \<times> bool) list" and a :: nat
  shows "\<exists>target'. top1_valid_scheme_equiv target target' \<and> (\<forall>e \<in> set target'. fst e \<noteq> a)"
proof -
  have "finite (fst ` set target \<union> {a} :: nat set)" by (by100 simp)
  from ex_new_if_finite[OF infinite_UNIV_nat this]
  obtain fresh :: nat where hfresh: "fresh \<notin> fst ` set target \<union> {a}" by (by100 blast)
  hence "fresh \<noteq> a" and "fresh \<notin> fst ` set target" by (by100 blast)+
  define target' where "target' = map (\<lambda>(l,b). (if l = a then fresh else l, b)) target"
  have "top1_valid_scheme_equiv target target'"
  proof (cases "a \<in> fst ` set target")
    case True
    have "top1_valid_scheme_operation target (map (\<lambda>(l, b). (if l = a then fresh else l, b)) target)"
      by (rule top1_valid_scheme_operation.v_relabel[OF \<open>fresh \<notin> fst ` set target\<close> \<open>fresh \<noteq> a\<close>])
    then show ?thesis unfolding target'_def by (rule valid_imp_equiv)
  next
    case False
    then have "target' = target" unfolding target'_def
      by (induction target) (by100 auto)+
    then show ?thesis unfolding top1_valid_scheme_equiv_def by (by100 simp)
  qed
  moreover have "\<forall>e \<in> set target'. fst e \<noteq> a"
  proof
    fix e assume "e \<in> set target'"
    then obtain l b where hlb: "(l,b) \<in> set target" "e = (if l = a then fresh else l, b)"
      unfolding target'_def by (by100 auto)
    then show "fst e \<noteq> a" using \<open>fresh \<noteq> a\<close> by (by100 auto)
  qed
  ultimately show ?thesis by (by100 blast)
qed


\<comment> \<open>Alpha-renaming: a bijective relabeling is a valid equivalence (per expert audit 20).
   Proof: apply fresh relabels sequentially via intermediate fresh labels.\<close>
\<comment> \<open>Helper: renaming one label in a scheme using map.\<close>
lemma map_relabel_comp:
  "map (\<lambda>(l,b). (if l = new then target else l, b))
       (map (\<lambda>(l,b). (if l = old then new else l, b)) w)
   = map (\<lambda>(l,b). (if l = old then target else if l = new then target else l, b)) w"
  by (by100 auto)

\<comment> \<open>Helper: if old \\<notin> fst ` set w, then relabeling old does nothing.\<close>
lemma map_relabel_id:
  assumes "old \<notin> fst ` set w"
  shows "map (\<lambda>(l,b). (if l = old then new else l, b)) w = w"
  using assms by (induction w) (by100 auto)+

\<comment> \<open>Helper: labels after a single relabel step.\<close>
lemma fst_set_single_relabel:
  assumes "old \<in> fst ` set w" "new \<notin> fst ` set w" "old \<noteq> new"
  shows "fst ` set (map (\<lambda>(l,b). (if l = old then new else l, b)) w) =
         (fst ` set w - {old}) \<union> {new}"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> fst ` set (map (\<lambda>(l, b). (if l = old then new else l, b)) w)"
  then obtain l b where hlb: "(l, b) \<in> set w" and hx: "x = (if l = old then new else l)"
    by (by100 fastforce)
  show "x \<in> (fst ` set w - {old}) \<union> {new}"
  proof (cases "l = old")
    case True then show ?thesis using hx by (by100 simp)
  next
    case False
    then have "x = l" using hx by (by100 simp)
    moreover have "l \<in> fst ` set w" using hlb by (by100 force)
    ultimately show ?thesis using False by (by100 blast)
  qed
next
  fix x
  assume "x \<in> (fst ` set w - {old}) \<union> {new}"
  then show "x \<in> fst ` set (map (\<lambda>(l, b). (if l = old then new else l, b)) w)"
  proof
    assume "x \<in> fst ` set w - {old}"
    then obtain l b where hlb: "(l, b) \<in> set w" "x = l" "l \<noteq> old"
      by (by100 fastforce)
    then have "(if l = old then new else l, b) \<in> set (map (\<lambda>(l, b). (if l = old then new else l, b)) w)"
      by (by100 force)
    thus ?thesis using hlb by (by100 force)
  next
    assume "x \<in> {new}"
    then have "x = new" by (by100 simp)
    from assms(1) obtain b where "(old, b) \<in> set w" by (by100 fastforce)
    then have "(new, b) \<in> set (map (\<lambda>(l, b). (if l = old then new else l, b)) w)"
      by (by100 force)
    thus ?thesis using \<open>x = new\<close> by (by100 force)
  qed
qed

\<comment> \<open>Helper: if \<rho> is identity on all labels, map \<rho> is identity.\<close>
lemma map_id_on_labels:
  assumes "\<forall>l \<in> fst ` set w. \<rho> l = l"
  shows "map (\<lambda>(l,b). (\<rho> l, b)) w = w"
  using assms by (induction w) (by100 auto)+

\<comment> \<open>Helper: composing map \<sigma> with single relabel l\<rightarrow>\<rho>(l) gives map \<rho>,
   when \<sigma> is identity on \<rho>(l) and \<rho> on everything else.\<close>
lemma map_sigma_after_relabel:
  fixes w :: "(nat \<times> bool) list"
  assumes "\<rho> l \<notin> fst ` set w"
  shows "map (\<lambda>(la,b). ((if la = \<rho> l then \<rho> l else \<rho> la), b))
           (map (\<lambda>(la,b). (if la = l then \<rho> l else la, b)) w) =
         map (\<lambda>(la,b). (\<rho> la, b)) w"
proof -
  have key: "\<And>a. a \<in> fst ` set w \<Longrightarrow>
    (if (if a = l then \<rho> l else a) = \<rho> l then \<rho> l else \<rho> (if a = l then \<rho> l else a)) = \<rho> a"
  proof -
    fix a assume ha: "a \<in> fst ` set w"
    show "(if (if a = l then \<rho> l else a) = \<rho> l then \<rho> l else \<rho> (if a = l then \<rho> l else a)) = \<rho> a"
    proof (cases "a = l")
      case True then show ?thesis by (by100 simp)
    next
      case False
      have "a \<noteq> \<rho> l" using ha assms by (by100 blast)
      then show ?thesis using False by (by100 simp)
    qed
  qed
  show ?thesis using key by (induction w) (by100 auto)+
qed

\<comment> \<open>Partial relabeling: rename labels in S (\<subseteq> labels(w)) via \<rho>, leaving others fixed.
   Induction on card S. Key enabler for disjoint relabeling.\<close>
lemma valid_scheme_relabel_partial:
  fixes w :: "(nat \<times> bool) list" and S :: "nat set"
  assumes "finite S" "S \<subseteq> fst ` set w"
      "inj_on \<rho> (fst ` set w)" "\<rho> ` S \<inter> fst ` set w = {}"
      "\<forall>l \<in> fst ` set w - S. \<rho> l = l"
  shows "top1_valid_scheme_equiv w (map (\<lambda>(l,b). (\<rho> l, b)) w)"
  using assms
proof (induction "card S" arbitrary: w \<rho> S)
  case 0
  then have "S = {}" by (by100 simp)
  then have "\<forall>l \<in> fst ` set w. \<rho> l = l" using 0 by (by100 auto)
  then have "map (\<lambda>(l,b). (\<rho> l, b)) w = w" by (rule map_id_on_labels)
  then show ?case unfolding top1_valid_scheme_equiv_def by (by100 simp)
next
  case (Suc n)
  have "S \<noteq> {}" using Suc.hyps(2) by (by100 force)
  then obtain l where hl: "l \<in> S" by (by100 blast)
  have hcard_S': "card (S - {l}) = n"
    using Suc.hyps(2) Suc.prems(1) hl by (by100 simp)
  have hl_in: "l \<in> fst ` set w" using hl Suc.prems(2) by (by100 blast)
  have hrl_out: "\<rho> l \<notin> fst ` set w" using hl Suc.prems(4) by (by100 blast)
  have hrl_ne: "\<rho> l \<noteq> l" using hl_in hrl_out by (by100 blast)
  define w' where "w' = map (\<lambda>(la,b). (if la = l then \<rho> l else la, b)) w"
  have step1: "top1_valid_scheme_equiv w w'"
    unfolding w'_def
    using valid_equiv_fresh_relabel[OF hrl_out hrl_ne] .
  have hw'_labels: "fst ` set w' = (fst ` set w - {l}) \<union> {\<rho> l}"
    unfolding w'_def using fst_set_single_relabel[OF hl_in hrl_out hrl_ne[symmetric]] .
  define \<sigma> where "\<sigma> = (\<lambda>la. if la = \<rho> l then \<rho> l else \<rho> la)"
  define S' where "S' = S - {l}"
  have key_eq: "map (\<lambda>(la,b). (\<sigma> la, b)) w' = map (\<lambda>(la,b). (\<rho> la, b)) w"
    unfolding w'_def \<sigma>_def
    using map_sigma_after_relabel[of \<rho> l w] hrl_out by (by100 simp)
  have fin': "finite S'" using Suc.prems(1) S'_def by (by100 simp)
  have sub': "S' \<subseteq> fst ` set w'"
    unfolding S'_def hw'_labels using Suc.prems(2) by (by100 blast)
  have inj': "inj_on \<sigma> (fst ` set w')"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> fst ` set w'" and hy: "y \<in> fst ` set w'" and heq: "\<sigma> x = \<sigma> y"
    \<comment> \<open>Helper: derive x = y by case analysis on whether x or y equals \\<rho> l.\<close>
    have hx_cases: "x = \<rho> l \<or> x \<in> fst ` set w \<and> x \<noteq> l" using hx hw'_labels by (by100 blast)
    have hy_cases: "y = \<rho> l \<or> y \<in> fst ` set w \<and> y \<noteq> l" using hy hw'_labels by (by100 blast)
    have sx_eq: "x \<noteq> \<rho> l \<Longrightarrow> \<sigma> x = \<rho> x" unfolding \<sigma>_def by (by100 simp)
    have sy_eq: "y \<noteq> \<rho> l \<Longrightarrow> \<sigma> y = \<rho> y" unfolding \<sigma>_def by (by100 simp)
    have srl: "\<sigma> (\<rho> l) = \<rho> l" unfolding \<sigma>_def by (by100 simp)
    show "x = y"
    proof (cases "x = \<rho> l")
      case xrl: True
      show ?thesis
      proof (cases "y = \<rho> l")
        case True then show ?thesis using xrl by (by100 simp)
      next
        case yne: False
        then have "y \<in> fst ` set w" using hy_cases by (by100 blast)
        have "\<sigma> y = \<rho> y" using sy_eq yne .
        then have "\<rho> y = \<rho> l" using heq xrl srl by (by100 simp)
        then have "y = l" using Suc.prems(3) \<open>y \<in> fst ` set w\<close> hl_in
          unfolding inj_on_def by (by100 blast)
        then show ?thesis using yne hy hw'_labels by (by100 blast)
      qed
    next
      case xne: False
      then have "x \<in> fst ` set w" using hx_cases by (by100 blast)
      have "\<sigma> x = \<rho> x" using sx_eq xne .
      show ?thesis
      proof (cases "y = \<rho> l")
        case yrl: True
        then have "\<rho> x = \<rho> l" using \<open>\<sigma> x = \<rho> x\<close> heq srl by (by100 simp)
        then have "x = l" using Suc.prems(3) \<open>x \<in> fst ` set w\<close> hl_in
          unfolding inj_on_def by (by100 blast)
        then show ?thesis using xne hx hw'_labels by (by100 blast)
      next
        case yne: False
        then have "y \<in> fst ` set w" using hy_cases by (by100 blast)
        have "\<sigma> y = \<rho> y" using sy_eq yne .
        then have "\<rho> x = \<rho> y" using \<open>\<sigma> x = \<rho> x\<close> heq by (by100 simp)
        then show ?thesis using Suc.prems(3) \<open>x \<in> fst ` set w\<close> \<open>y \<in> fst ` set w\<close>
          unfolding inj_on_def by (by100 blast)
      qed
    qed
  qed
  have disj': "\<sigma> ` S' \<inter> fst ` set w' = {}"
  proof (rule ccontr)
    assume "\<sigma> ` S' \<inter> fst ` set w' \<noteq> {}"
    then obtain x where hx_S: "x \<in> S'" and hsx_w: "\<sigma> x \<in> fst ` set w'" by (by100 blast)
    have hx_w: "x \<in> fst ` set w" and hx_ne: "x \<noteq> l"
      using hx_S Suc.prems(2) unfolding S'_def by (by100 blast)+
    have "x \<noteq> \<rho> l" using hx_w hrl_out by (by100 blast)
    then have hsx: "\<sigma> x = \<rho> x" unfolding \<sigma>_def by (by100 simp)
    have "\<rho> x \<in> \<rho> ` S" using hx_S S'_def by (by100 blast)
    then have "\<rho> x \<notin> fst ` set w" using Suc.prems(4) by (by100 blast)
    then have "\<sigma> x \<notin> fst ` set w" using hsx by (by100 simp)
    have "\<rho> x \<noteq> \<rho> l"
    proof
      assume "\<rho> x = \<rho> l"
      then have "x = l" using Suc.prems(3) hx_w hl_in
        unfolding inj_on_def by (by100 blast)
      then show False using hx_ne by (by100 blast)
    qed
    then have "\<sigma> x \<noteq> \<rho> l" using hsx by (by100 simp)
    then have "\<sigma> x \<notin> fst ` set w'" using \<open>\<sigma> x \<notin> fst ` set w\<close> hw'_labels by (by100 blast)
    then show False using hsx_w by (by100 blast)
  qed
  have id': "\<forall>la \<in> fst ` set w' - S'. \<sigma> la = la"
  proof
    fix la assume hla: "la \<in> fst ` set w' - S'"
    show "\<sigma> la = la"
    proof (cases "la = \<rho> l")
      case True then show ?thesis unfolding \<sigma>_def by (by100 simp)
    next
      case False
      then have "la \<in> fst ` set w - {l}" using hla hw'_labels by (by100 blast)
      then have hla_w: "la \<in> fst ` set w" and hla_ne: "la \<noteq> l" by (by100 blast)+
      have "la \<notin> S'" using hla by (by100 blast)
      then have "la \<notin> S" using hla_ne unfolding S'_def by (by100 blast)
      then have "\<rho> la = la" using hla_w Suc.prems(5) by (by100 blast)
      then show ?thesis using False unfolding \<sigma>_def by (by100 simp)
    qed
  qed
  have step2: "top1_valid_scheme_equiv w' (map (\<lambda>(la,b). (\<sigma> la, b)) w')"
    using Suc.hyps(1)[of S' w' \<sigma>] hcard_S' fin' sub' inj' disj' id'
    unfolding S'_def \<sigma>_def w'_def by (by100 blast)
  from step1 step2 have "top1_valid_scheme_equiv w (map (\<lambda>(la,b). (\<sigma> la, b)) w')"
    by (rule valid_equiv_trans)
  then show ?case using key_eq by (by100 simp)
qed

\<comment> \<open>Disjoint relabeling: if all target labels are fresh (disjoint from source),
   then the relabeling is a valid equivalence. Corollary of partial relabeling.\<close>
lemma valid_scheme_relabel_disjoint:
  fixes w :: "(nat \<times> bool) list"
  assumes "inj_on \<rho> (scheme_labels w)"
      and "\<rho> ` (scheme_labels w) \<inter> scheme_labels w = {}"
  shows "top1_valid_scheme_equiv w (map (\<lambda>(l,b). (\<rho> l, b)) w)"
proof -
  have "finite (fst ` set w)" by (by100 simp)
  moreover have "fst ` set w \<subseteq> fst ` set w" by (by100 blast)
  moreover have "inj_on \<rho> (fst ` set w)" using assms(1) unfolding scheme_labels_def .
  moreover have "\<rho> ` (fst ` set w) \<inter> fst ` set w = {}" using assms(2) unfolding scheme_labels_def .
  moreover have "\<forall>l \<in> fst ` set w - fst ` set w. \<rho> l = l" by (by100 blast)
  ultimately show ?thesis by (rule valid_scheme_relabel_partial)
qed

\<comment> \<open>Alpha-renaming: a bijective relabeling is a valid equivalence (per expert audit 20).
   Proof: induction on the number of labels that differ from identity.\<close>
lemma scheme_labels_map_relabel:
  "scheme_labels (map (\<lambda>(l,b). (\<sigma> l, b)) w) = \<sigma> ` scheme_labels w"
  unfolding scheme_labels_def by (by100 force)

\<comment> \<open>Helper: existence of fresh label set (nat-indexed, above all existing labels).\<close>
lemma fresh_nat_set:
  fixes S :: "nat set"
  assumes "finite S" "finite T"
  shows "\<exists>\<sigma> :: nat \<Rightarrow> nat. inj_on \<sigma> S \<and> \<sigma> ` S \<inter> (S \<union> T) = {} \<and> finite (\<sigma> ` S)"
proof -
  define M where "M = Max (S \<union> T) + 1"
  define \<sigma> where "\<sigma> = (\<lambda>x. x + M)"
  have "inj_on \<sigma> S" unfolding \<sigma>_def inj_on_def by (by100 simp)
  moreover have "\<sigma> ` S \<inter> (S \<union> T) = {}"
  proof (rule ccontr)
    assume "\<sigma> ` S \<inter> (S \<union> T) \<noteq> {}"
    then obtain x where hx: "x \<in> S" and hsx: "\<sigma> x \<in> S \<union> T" by (by100 blast)
    have "\<sigma> x = x + M" unfolding \<sigma>_def by (by100 simp)
    moreover have "x + M > Max (S \<union> T)"
      unfolding M_def by (by100 simp)
    moreover have "\<sigma> x \<le> Max (S \<union> T)"
      using Max_ge_iff[of "S \<union> T"] hsx assms by (by100 simp)
    ultimately show False by (by100 simp)
  qed
  moreover have "finite (\<sigma> ` S)" using assms(1) by (by100 simp)
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Helper: composing two relabelings on a list.\<close>
lemma map_relabel_compose:
  "map (\<lambda>(l,b). (\<sigma>2 l, b)) (map (\<lambda>(l,b). (\<sigma>1 l, b)) w) =
   map (\<lambda>(l,b). (\<sigma>2 (\<sigma>1 l), b)) w"
  by (induction w) (by100 auto)+

\<comment> \<open>Alpha-renaming: a bijective relabeling is a valid equivalence.
   Two-phase proof: w \\<to> (fresh labels) \\<to> map \\<rho> w.\<close>
lemma valid_scheme_alpha_rename:
  fixes w :: "(nat \<times> bool) list"
  assumes "bij_betw \<rho> (scheme_labels w) L"
  shows "top1_valid_scheme_equiv w (map (\<lambda>(l,b). (\<rho> l, b)) w)"
proof -
  define S where "S = scheme_labels w"
  have hfin_S: "finite S" unfolding S_def scheme_labels_def by (by100 simp)
  have "L = \<rho> ` S" using assms unfolding bij_betw_def S_def by (by100 blast)
  then have hfin_L: "finite L" using hfin_S by (by100 simp)
  \<comment> \<open>Phase 1: find fresh labels F disjoint from S \\<union> L.\<close>
  from fresh_nat_set[OF hfin_S hfin_L]
  obtain \<sigma>1 :: "nat \<Rightarrow> nat" where
    h\<sigma>1_inj: "inj_on \<sigma>1 S" and h\<sigma>1_disj: "\<sigma>1 ` S \<inter> (S \<union> L) = {}"
    and h\<sigma>1_fin: "finite (\<sigma>1 ` S)" by (by100 blast)
  define F where "F = \<sigma>1 ` S"
  have hF_disj_S: "F \<inter> S = {}" using h\<sigma>1_disj unfolding F_def by (by100 blast)
  have hF_disj_L: "F \<inter> L = {}" using h\<sigma>1_disj unfolding F_def by (by100 blast)
  \<comment> \<open>Phase 1 application: w \\<sim> map \\<sigma>1 w via disjoint relabeling.\<close>
  have step1: "top1_valid_scheme_equiv w (map (\<lambda>(l,b). (\<sigma>1 l, b)) w)"
  proof (rule valid_scheme_relabel_disjoint)
    show "inj_on \<sigma>1 (scheme_labels w)" using h\<sigma>1_inj S_def by (by100 simp)
    show "\<sigma>1 ` scheme_labels w \<inter> scheme_labels w = {}"
      using h\<sigma>1_disj unfolding S_def by (by100 blast)
  qed
  define w1 where "w1 = map (\<lambda>(l,b). (\<sigma>1 l, b)) w"
  have hw1_labels: "scheme_labels w1 = F"
    unfolding w1_def F_def S_def
    using scheme_labels_map_relabel[of \<sigma>1 w] unfolding scheme_labels_def by (by100 simp)
  \<comment> \<open>Phase 2: define \\<sigma>2 : F \\<to> L via \\<rho> \\<circ> \\<sigma>1\\<inverse>.
     Concretely: \\<sigma>2(f) = \\<rho>(the unique s \\<in> S with \\<sigma>1(s) = f).\<close>
  have hbij_\<sigma>1: "bij_betw \<sigma>1 S F"
    unfolding F_def bij_betw_def using h\<sigma>1_inj by (by100 blast)
  define \<sigma>1_inv where "\<sigma>1_inv = the_inv_into S \<sigma>1"
  have h\<sigma>1_inv_f: "\<And>f. f \<in> F \<Longrightarrow> \<sigma>1 (\<sigma>1_inv f) = f"
    unfolding \<sigma>1_inv_def F_def using f_the_inv_into_f[OF h\<sigma>1_inj] by (by100 blast)
  have h\<sigma>1_inv_in: "\<And>f. f \<in> F \<Longrightarrow> \<sigma>1_inv f \<in> S"
    unfolding \<sigma>1_inv_def F_def using the_inv_into_into[OF h\<sigma>1_inj] by (by100 blast)
  have h\<sigma>1_inv: "\<And>f. f \<in> F \<Longrightarrow> \<sigma>1 (\<sigma>1_inv f) = f \<and> \<sigma>1_inv f \<in> S"
    using h\<sigma>1_inv_f h\<sigma>1_inv_in by (by100 blast)
  define \<sigma>2 where "\<sigma>2 = (\<lambda>f. \<rho> (\<sigma>1_inv f))"
  have h\<sigma>2_on_F: "\<And>f. f \<in> F \<Longrightarrow> \<sigma>2 f = \<rho> (\<sigma>1_inv f)" unfolding \<sigma>2_def by (by100 simp)
  \<comment> \<open>Phase 2: \\<sigma>2 is a disjoint relabeling of w1.\<close>
  have h\<sigma>2_inj: "inj_on \<sigma>2 F"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> F" and hy: "y \<in> F" and heq: "\<sigma>2 x = \<sigma>2 y"
    have "\<rho> (\<sigma>1_inv x) = \<rho> (\<sigma>1_inv y)" using heq unfolding \<sigma>2_def by (by100 simp)
    moreover have "\<sigma>1_inv x \<in> S" using h\<sigma>1_inv hx by (by100 blast)
    moreover have "\<sigma>1_inv y \<in> S" using h\<sigma>1_inv hy by (by100 blast)
    moreover have "inj_on \<rho> S" using assms unfolding bij_betw_def S_def by (by100 blast)
    ultimately have "\<sigma>1_inv x = \<sigma>1_inv y"
      unfolding inj_on_def by (by100 blast)
    then have "\<sigma>1 (\<sigma>1_inv x) = \<sigma>1 (\<sigma>1_inv y)" by (by100 simp)
    then show "x = y" using h\<sigma>1_inv_f hx hy by (by100 simp)
  qed
  have h\<sigma>2_image: "\<sigma>2 ` F = L"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> \<sigma>2 ` F"
    then obtain f where hf: "f \<in> F" and hx: "x = \<sigma>2 f" by (by100 blast)
    have "\<sigma>1_inv f \<in> S" using h\<sigma>1_inv hf by (by100 blast)
    then show "x \<in> L" using hx assms unfolding \<sigma>2_def bij_betw_def S_def by (by100 blast)
  next
    fix x assume "x \<in> L"
    then obtain s where hs: "s \<in> S" and hx: "\<rho> s = x"
      using assms unfolding bij_betw_def S_def by (by100 blast)
    define f where "f = \<sigma>1 s"
    have "f \<in> F" using hs unfolding f_def F_def by (by100 blast)
    moreover have "\<sigma>2 f = x"
    proof -
      have "\<sigma>1_inv f = s"
        unfolding f_def \<sigma>1_inv_def using the_inv_into_f_eq[OF h\<sigma>1_inj] hs by (by100 blast)
      then show ?thesis unfolding \<sigma>2_def using hx by (by100 simp)
    qed
    ultimately show "x \<in> \<sigma>2 ` F" by (by100 blast)
  qed
  have h\<sigma>2_disj: "\<sigma>2 ` F \<inter> F = {}"
    using h\<sigma>2_image hF_disj_L by (by100 blast)
  have step2: "top1_valid_scheme_equiv w1 (map (\<lambda>(l,b). (\<sigma>2 l, b)) w1)"
  proof (rule valid_scheme_relabel_disjoint)
    show "inj_on \<sigma>2 (scheme_labels w1)" using h\<sigma>2_inj hw1_labels by (by100 simp)
    show "\<sigma>2 ` scheme_labels w1 \<inter> scheme_labels w1 = {}"
      using h\<sigma>2_disj hw1_labels by (by100 simp)
  qed
  \<comment> \<open>Key: map \\<sigma>2 (map \\<sigma>1 w) = map \\<rho> w.\<close>
  have key_eq: "map (\<lambda>(l,b). (\<sigma>2 l, b)) w1 = map (\<lambda>(l,b). (\<rho> l, b)) w"
  proof -
    have "map (\<lambda>(l,b). (\<sigma>2 l, b)) w1 = map (\<lambda>(l,b). (\<sigma>2 (\<sigma>1 l), b)) w"
      unfolding w1_def using map_relabel_compose by (by100 simp)
    moreover have "\<And>s. s \<in> S \<Longrightarrow> \<sigma>2 (\<sigma>1 s) = \<rho> s"
    proof -
      fix s assume hs: "s \<in> S"
      have "\<sigma>1 s \<in> F" using hs unfolding F_def by (by100 blast)
      have h\<sigma>1s_F: "\<sigma>1 s \<in> F" using hs unfolding F_def by (by100 blast)
      have "\<sigma>1 (\<sigma>1_inv (\<sigma>1 s)) = \<sigma>1 s" using h\<sigma>1_inv_f h\<sigma>1s_F by (by100 blast)
      moreover have "\<sigma>1_inv (\<sigma>1 s) \<in> S" using h\<sigma>1_inv_in h\<sigma>1s_F by (by100 blast)
      ultimately have "\<sigma>1_inv (\<sigma>1 s) = s"
        using h\<sigma>1_inj hs unfolding inj_on_def by (by100 blast)
      then show "\<sigma>2 (\<sigma>1 s) = \<rho> s" unfolding \<sigma>2_def by (by100 simp)
    qed
    then have "map (\<lambda>(l,b). (\<sigma>2 (\<sigma>1 l), b)) w = map (\<lambda>(l,b). (\<rho> l, b)) w"
      unfolding S_def scheme_labels_def by (induction w) (by100 auto)+
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Combine via transitivity.\<close>
  from step1[folded w1_def] step2 key_eq valid_equiv_trans
  show ?thesis by (by100 force)
qed

\<comment> \<open>Scheme equivalence: transitivity and lifting from elementary operations.
   These avoid the meson/rtranclp\_trans timeout on complex list types.\<close>
lemma scheme_equiv_trans:
  "top1_scheme_equiv a b \<Longrightarrow> top1_scheme_equiv b c \<Longrightarrow> top1_scheme_equiv a c"
  unfolding top1_scheme_equiv_def by (rule rtranclp_trans)

lemma elementary_imp_equiv:
  "top1_elementary_scheme_operation a b \<Longrightarrow> top1_scheme_equiv a b"
  unfolding top1_scheme_equiv_def
  by (rule rtranclp.rtrancl_into_rtrancl[OF rtranclp.rtrancl_refl])

lemma scheme_equiv_refl: "top1_scheme_equiv a a"
  unfolding top1_scheme_equiv_def by (rule rtranclp.rtrancl_refl)

section \<open>\<S>76 Cutting and Pasting\<close>

\<comment> \<open>Quotient uniqueness: two quotient maps on the same space with the same fibres
   give homeomorphic quotient spaces. Follows from Theorem 22.2 applied both ways.\<close>
lemma quotient_same_fibres_homeomorphic:
  fixes X :: "'a set" and TX :: "'a set set"
    and Y1 :: "'b set" and TY1 :: "'b set set"
    and Y2 :: "'c set" and TY2 :: "'c set set"
  assumes hp1: "top1_quotient_map_on X TX Y1 TY1 p1"
      and hp2: "top1_quotient_map_on X TX Y2 TY2 p2"
      and hfibres: "\<forall>x\<in>X. \<forall>y\<in>X. (p1 x = p1 y) \<longleftrightarrow> (p2 x = p2 y)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>p2 is constant on fibres of p1 (from hfibres).\<close>
  have hp2_range: "\<forall>x\<in>X. p2 x \<in> Y2"
    using hp2 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp2_const: "\<forall>x\<in>X. \<forall>y\<in>X. p1 x = p1 y \<longrightarrow> p2 x = p2 y"
    using hfibres by (by100 blast)
  \<comment> \<open>By Theorem 22.2: p2 factors through p1 as f: Y1 \\<to> Y2.\<close>
  from Theorem_22_2[OF hp1 hp2_range hp2_const]
  obtain f where hf_range: "\<forall>y\<in>Y1. f y \<in> Y2"
      and hf_comp: "\<forall>x\<in>X. f (p1 x) = p2 x"
      and hf_cont_iff: "top1_continuous_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_continuous_map_on X TX Y2 TY2 p2"
      and hf_quot_iff: "top1_quotient_map_on Y1 TY1 Y2 TY2 f \<longleftrightarrow> top1_quotient_map_on X TX Y2 TY2 p2"
    by (by100 blast)
  \<comment> \<open>Similarly p1 factors through p2 as g: Y2 \\<to> Y1.\<close>
  have hp1_range: "\<forall>x\<in>X. p1 x \<in> Y1"
    using hp1 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  have hp1_const: "\<forall>x\<in>X. \<forall>y\<in>X. p2 x = p2 y \<longrightarrow> p1 x = p1 y"
    using hfibres by (by100 blast)
  from Theorem_22_2[OF hp2 hp1_range hp1_const]
  obtain g where hg_range: "\<forall>y\<in>Y2. g y \<in> Y1"
      and hg_comp: "\<forall>x\<in>X. g (p2 x) = p1 x"
      and hg_cont_iff: "top1_continuous_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_continuous_map_on X TX Y1 TY1 p1"
      and hg_quot_iff: "top1_quotient_map_on Y2 TY2 Y1 TY1 g \<longleftrightarrow> top1_quotient_map_on X TX Y1 TY1 p1"
    by (by100 blast)
  \<comment> \<open>f is a quotient map (since p2 is).\<close>
  have hf_quot: "top1_quotient_map_on Y1 TY1 Y2 TY2 f"
    using hf_quot_iff hp2 by simp
  \<comment> \<open>f is bijective: injective (from g \\<circ> f = id on Y1) and surjective (quotient maps are surjective).\<close>
  have hf_surj: "f ` Y1 = Y2"
  proof -
    have "p2 ` X = Y2" using hp2 unfolding top1_quotient_map_on_def by (by100 blast)
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    show ?thesis
    proof
      show "f ` Y1 \<subseteq> Y2" using hf_range by (by100 blast)
    next
      show "Y2 \<subseteq> f ` Y1"
      proof
        fix y2 assume "y2 \<in> Y2"
        hence "\<exists>x\<in>X. p2 x = y2" using \<open>p2 ` X = Y2\<close> by (by100 blast)
        then obtain x where "x \<in> X" "p2 x = y2" by (by100 blast)
        hence "f (p1 x) = y2" using hf_comp by simp
        moreover have "p1 x \<in> Y1" using hp1_range \<open>x \<in> X\<close> by (by100 blast)
        ultimately show "y2 \<in> f ` Y1" by (by100 blast)
      qed
    qed
  qed
  have hgf_id: "\<forall>y\<in>Y1. g (f y) = y"
  proof
    fix y1 assume "y1 \<in> Y1"
    have "p1 ` X = Y1" using hp1 unfolding top1_quotient_map_on_def by (by100 blast)
    then obtain x where "x \<in> X" "p1 x = y1" using \<open>y1 \<in> Y1\<close> by (by100 blast)
    have "f y1 = f (p1 x)" using \<open>p1 x = y1\<close> by simp
    also have "\<dots> = p2 x" using hf_comp \<open>x \<in> X\<close> by simp
    finally have "f y1 = p2 x" .
    hence "g (f y1) = g (p2 x)" by simp
    also have "\<dots> = p1 x" using hg_comp \<open>x \<in> X\<close> by simp
    finally show "g (f y1) = y1" using \<open>p1 x = y1\<close> by simp
  qed
  have hf_inj: "inj_on f Y1"
  proof (rule inj_onI)
    fix y1 y1' assume "y1 \<in> Y1" "y1' \<in> Y1" "f y1 = f y1'"
    have "g (f y1) = y1" using hgf_id \<open>y1 \<in> Y1\<close> by simp
    have "g (f y1') = y1'" using hgf_id \<open>y1' \<in> Y1\<close> by simp
    from \<open>f y1 = f y1'\<close> have "g (f y1) = g (f y1')" by simp
    thus "y1 = y1'" using \<open>g (f y1) = y1\<close> \<open>g (f y1') = y1'\<close> by simp
  qed
  have "bij_betw f Y1 Y2" unfolding bij_betw_def using hf_inj hf_surj by simp
  \<comment> \<open>Bijective quotient map = homeomorphism.\<close>
  from top1_bij_quotient_map_on_imp_homeomorphism_on[OF hf_quot this]
  show ?thesis by (by100 blast)
qed

\<comment> \<open>Quotient transport: if P \<sim> P' (homeomorphism) and the boundary identifications
   match (fibre agreement), then the quotient surfaces are homeomorphic.
   This is the main §76 tool: each elementary operation only needs to provide
   a polygon homeomorphism + fibre agreement.\<close>
lemma quotient_transport_by_homeomorphism:
  fixes P :: "'a set" and TP :: "'a set set"
    and P' :: "'a set" and TP' :: "'a set set"
    and Y :: "'b set" and TY :: "'b set set"
    and Y' :: "'c set" and TY' :: "'c set set"
  assumes hq: "top1_quotient_map_on P TP Y TY q"
      and hq': "top1_quotient_map_on P' TP' Y' TY' q'"
      and hh: "top1_homeomorphism_on P TP P' TP' h"
      and hfibres: "\<forall>x\<in>P. \<forall>y\<in>P. (q x = q y) \<longleftrightarrow> (q' (h x) = q' (h y))"
  shows "\<exists>H. top1_homeomorphism_on Y TY Y' TY' H"
proof -
  \<comment> \<open>h is a quotient map P \<to> P'.\<close>
  have hh_quot: "top1_quotient_map_on P TP P' TP' h"
    using top1_homeomorphism_on_imp_quotient_map_on[OF hh] .
  \<comment> \<open>Define p2 = q' \<circ> h : P \<to> Y'. Composition of quotient maps = quotient map.\<close>
  define p2 where "p2 = q' \<circ> h"
  have hp2: "top1_quotient_map_on P TP Y' TY' p2"
    unfolding p2_def using top1_quotient_map_on_comp[OF hh_quot hq'] .
  \<comment> \<open>Fibre agreement: q and p2 have the same fibres on P.\<close>
  have "\<forall>x\<in>P. \<forall>y\<in>P. (q x = q y) \<longleftrightarrow> (p2 x = p2 y)"
    unfolding p2_def comp_def using hfibres by (by100 blast)
  \<comment> \<open>Apply quotient\_same\_fibres\_homeomorphic.\<close>
  from quotient_same_fibres_homeomorphic[OF hq hp2 this]
  show ?thesis .
qed

\<comment> \<open>Cancel/uncancel same-space preservation.
   PROVED versions (quotient\\_of\\_scheme\\_cancel\\_proved, quotient\\_of\\_scheme\\_uncancel\\_proved)
   are defined after quotient\\_of\\_scheme\\_rotate, reducing to cancel\\_front/uncancel\\_front
   via rotation. Original declarations removed (no longer referenced).\<close>

\<comment> \<open>Extract vertices from a polygonal region.\<close>
lemma polygonal_region_extract_vx:
  assumes "top1_is_polygonal_region_on P n"
  obtains vx vy where
    "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    "\<forall>k<n. \<not>(\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i))"
    "P = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using assms unfolding top1_is_polygonal_region_on_def
  apply (elim conjE exE)
  apply (rule that)
  apply assumption+
  done

\<comment> \<open>Full extraction: get P, q, vx, vy with ALL 11 conditions from quotient\_of\_scheme\_on.
   (Moved here from later in the file so invert can use it.)\<close>
lemma quotient_of_scheme_extract_vx:
  assumes "top1_quotient_of_scheme_on X TX scheme"
  obtains P q vx vy where
    "top1_is_polygonal_region_on P (length scheme)"
    "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
    "\<forall>i<length scheme. \<forall>j<length scheme. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    "\<forall>i<length scheme. (vx i, vy i) \<in> P"
    "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
    "\<forall>i<length scheme. \<forall>j<length scheme.
          i \<noteq> j \<longrightarrow> Suc i mod length scheme \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length scheme \<longrightarrow>
          (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
             ((1-s) * vx i + s * vx (Suc i mod length scheme),
              (1-s) * vy i + s * vy (Suc i mod length scheme))
           \<noteq> ((1-t) * vx j + t * vx (Suc j mod length scheme),
               (1-t) * vy j + t * vy (Suc j mod length scheme)))"
    "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
    "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                      (1-t) * vy i + t * vy (Suc i mod length scheme)))
             \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length scheme),
               (1-t) * vy i + t * vy (Suc i mod length scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
               (1-s) * vy j + s * vy (Suc j mod length scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    "\<forall>i<length scheme. let cx = (\<Sum>j<length scheme. vx j) / real (length scheme);
                           cy = (\<Sum>j<length scheme. vy j) / real (length scheme)
         in (vx i - cx) * (vy (Suc i mod length scheme) - cy)
          - (vy i - cy) * (vx (Suc i mod length scheme) - cx) > 0"
    "\<forall>i<length scheme. \<forall>k<length scheme.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length scheme \<longrightarrow>
          (vx k - vx i) * (vy (Suc i mod length scheme) - vy i)
          - (vy k - vy i) * (vx (Suc i mod length scheme) - vx i) < 0"
  using assms unfolding top1_quotient_of_scheme_on_def
  apply (elim conjE exE)
  apply (rule that)
  apply assumption+
  done

\<comment> \<open>Invert: quotient preserved by reversal+inversion. Per the textbook:
   "flipping the polygonal region over": reverse vertex order, reverse edge orientations.
   Reflection \\<rho>(x,y)=(x,-y) reverses both vertex order (from counterclockwise to clockwise)
   and the cross-product signs (making counterclockwise again after reversal).
   Vertex numbering: \\<sigma>(i) = (n-i) mod n. Label at new position i = label at old position (n-1-i).
   New edge i at parameter t = \\<rho>(old edge (n-1-i) at parameter (1-t)).\<close>
\<comment> \<open>Edge set transport under reflection+reversal:
   If p avoids all reflected edges, then \\<rho>(p) avoids all original edges.
   This is the key geometric fact for the C8' interior-injectivity condition of invert.\<close>
lemma reflected_not_on_edges_imp_original:
  fixes n :: nat and vx vy :: "nat \<Rightarrow> real"
  assumes hn: "n \<ge> 3"
  defines "\<sigma> \<equiv> \<lambda>i. (n - i) mod n"
  defines "\<rho> \<equiv> \<lambda>(x::real, y::real). (x, -y)"
  assumes hne: "\<forall>i<n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod n)),
                      (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod n)))))"
  shows "\<forall>j<n. \<forall>t\<in>I_set.
        \<rho> p \<noteq> ((1-t) * vx j + t * vx (Suc j mod n),
              (1-t) * vy j + t * vy (Suc j mod n))"
proof (intro allI impI ballI)
  fix j t assume hj: "j < n" and ht: "t \<in> I_set"
  have hn_pos: "0 < n" using hn by (by100 linarith)
  \<comment> \<open>\\<sigma> properties.\<close>
  have h\<sigma>_lt: "\<And>i. i < n \<Longrightarrow> \<sigma> i < n" unfolding \<sigma>_def using hn_pos by (rule mod_less_divisor)
  have h\<sigma>_0: "\<sigma> 0 = 0" unfolding \<sigma>_def by (by100 simp)
  have h\<sigma>_pos: "\<And>i. 0 < i \<Longrightarrow> i < n \<Longrightarrow> \<sigma> i = n - i" unfolding \<sigma>_def by (by100 simp)
  have h\<sigma>_inv: "\<And>i. i < n \<Longrightarrow> \<sigma> (\<sigma> i) = i"
  proof -
    fix i assume hi: "i < n"
    show "\<sigma> (\<sigma> i) = i"
    proof (cases "i = 0")
      case True thus ?thesis unfolding \<sigma>_def using hn_pos by (by100 simp)
    next
      case False
      have "\<sigma> i = n - i" using h\<sigma>_pos[of i] False hi by (by100 simp)
      hence "\<sigma> (\<sigma> i) = \<sigma> (n - i)" by (by100 simp)
      also have "\<dots> = (n - (n - i)) mod n" unfolding \<sigma>_def by (by100 simp)
      also have "n - (n - i) = i" using hi by (by100 linarith)
      also have "i mod n = i" using hi by (by100 simp)
      finally show ?thesis .
    qed
  qed
  have h\<sigma>_suc: "\<And>i. i < n \<Longrightarrow> \<sigma> (Suc i mod n) = n - 1 - i"
  proof -
    fix i assume hi: "i < n"
    show "\<sigma> (Suc i mod n) = n - 1 - i"
    proof (cases "Suc i < n")
      case True
      have "\<sigma> (Suc i mod n) = \<sigma> (Suc i)" using True by (by100 simp)
      also have "\<dots> = n - Suc i" using h\<sigma>_pos[of "Suc i"] True by (by100 simp)
      also have "\<dots> = n - 1 - i" using True by (by100 linarith)
      finally show ?thesis .
    next
      case False
      hence "i = n - 1" using hi by (by100 linarith)
      have "Suc i = n" using \<open>i = n - 1\<close> hn by (by100 linarith)
      hence "Suc i mod n = 0" by (by100 simp)
      hence "\<sigma> (Suc i mod n) = \<sigma> 0" by (by100 simp)
      also have "\<dots> = 0" using h\<sigma>_0 .
      also have "(0::nat) = n - 1 - i" using \<open>i = n - 1\<close> by (by100 linarith)
      finally show ?thesis .
    qed
  qed
  have hSuc_n1j: "Suc (n - 1 - j) mod n = \<sigma> j"
  proof (cases "j = 0")
    case True thus ?thesis unfolding \<sigma>_def using hn_pos by (by100 simp)
  next
    case False
    have "Suc (n - 1 - j) = n - j" using hj False by (by100 linarith)
    moreover have "n - j < n" using False hj by (by100 linarith)
    ultimately have "Suc (n - 1 - j) mod n = n - j" by (by100 simp)
    also have "n - j = \<sigma> j" using h\<sigma>_pos[of j] False hj by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>\\<rho> properties.\<close>
  have h\<rho>_p: "\<And>a b::real. \<rho> (a, b) = (a, -b)" unfolding \<rho>_def by (by100 simp)
  have h\<rho>_inv: "\<And>q. \<rho> (\<rho> q) = q" unfolding \<rho>_def by (by100 auto)
  \<comment> \<open>1-t \\<in> I\\_set.\<close>
  have h1t: "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 simp)
  \<comment> \<open>k = n-1-j.\<close>
  let ?k = "n - 1 - j"
  have hk: "?k < n" using hj by (by100 linarith)
  have h_sk: "\<sigma> (Suc ?k mod n) = j" using h\<sigma>_suc[OF hk] hj by (by100 linarith)
  \<comment> \<open>From hne at (?k, 1-t): p \\<noteq> reflected edge at (?k, 1-t).\<close>
  from hne[rule_format, OF hk h1t]
  have hp_ne: "p \<noteq> ((1-(1-t)) * vx (\<sigma> ?k) + (1-t) * vx (\<sigma> (Suc ?k mod n)),
              (1-(1-t)) * (-(vy (\<sigma> ?k))) + (1-t) * (-(vy (\<sigma> (Suc ?k mod n)))))" .
  \<comment> \<open>Simplify: 1-(1-t)=t, \\<sigma>(Suc k mod n)=j.\<close>
  hence hp_ne2: "p \<noteq> (t * vx (\<sigma> ?k) + (1-t) * vx j,
              t * (-(vy (\<sigma> ?k))) + (1-t) * (-(vy j)))"
    using h_sk by (by100 simp)
  show "\<rho> p \<noteq> ((1-t) * vx j + t * vx (Suc j mod n),
              (1-t) * vy j + t * vy (Suc j mod n))"
  proof
    assume heq: "\<rho> p = ((1-t) * vx j + t * vx (Suc j mod n),
              (1-t) * vy j + t * vy (Suc j mod n))"
    \<comment> \<open>p = \\<rho>(\\<rho>(p)) = \\<rho>(orig\\_edge(j,t)).\<close>
    have "p = \<rho> (\<rho> p)" using h\<rho>_inv by (by100 metis)
    hence "p = \<rho> ((1-t) * vx j + t * vx (Suc j mod n),
              (1-t) * vy j + t * vy (Suc j mod n))" using heq by (by100 simp)
    hence hp_val: "p = ((1-t) * vx j + t * vx (Suc j mod n),
              -((1-t) * vy j + t * vy (Suc j mod n)))"
      using h\<rho>_p by (by100 simp)
    \<comment> \<open>Replace Suc j mod n with \\<sigma>(?k) via hSuc\\_n1j.\<close>
    have h_Sj_sigma: "Suc j mod n = \<sigma> ?k"
    proof (cases "j < n - 1")
      case True
      have "0 < ?k" using True by (by100 linarith)
      have "\<sigma> ?k = n - ?k" using h\<sigma>_pos[OF \<open>0 < ?k\<close> hk] by (by100 simp)
      also have "n - ?k = Suc j" using True hj by (by100 linarith)
      finally show ?thesis using True by (by100 simp)
    next
      case False
      hence "j = n - 1" using hj by (by100 linarith)
      hence "?k = 0" by (by100 linarith)
      have "Suc j = n" using \<open>j = n - 1\<close> hn by (by100 linarith)
      thus ?thesis using \<open>?k = 0\<close> h\<sigma>_0 by (by100 simp)
    qed
    from hp_val have "p = ((1-t) * vx j + t * vx (\<sigma> ?k),
              -((1-t) * vy j + t * vy (\<sigma> ?k)))" using h_Sj_sigma by (by100 simp)
    \<comment> \<open>Commute and distribute negation to match hp\\_ne2.\<close>
    hence "p = (t * vx (\<sigma> ?k) + (1-t) * vx j,
              t * (-(vy (\<sigma> ?k))) + (1-t) * (-(vy j)))" by (by100 argo)
    with hp_ne2 show False by (by100 simp)
  qed
qed

lemma quotient_of_scheme_invert:
  assumes "top1_quotient_of_scheme_on Y TY w"
  shows "top1_quotient_of_scheme_on Y TY (rev (map top1_inverse_edge w))"
proof -
  let ?n = "length w"
  let ?w' = "rev (map top1_inverse_edge w)"
  have hlen: "length ?w' = ?n" by (by100 simp)
  \<comment> \<open>The inverted scheme: w'!i = inverse\_edge(w!(n-1-i)).\<close>
  have hnth: "\<And>i. i < ?n \<Longrightarrow>
      ?w' ! i = top1_inverse_edge (w ! (?n - 1 - i))"
  proof -
    fix i assume hi: "i < ?n"
    have h1: "rev (map top1_inverse_edge w) ! i
        = (map top1_inverse_edge w) ! (?n - 1 - i)"
      using rev_nth[of i "map top1_inverse_edge w"] hi by (by100 simp)
    have h2: "?n - 1 - i < ?n" using hi by (by100 linarith)
    have "(map top1_inverse_edge w) ! (?n - 1 - i) = top1_inverse_edge (w ! (?n - 1 - i))"
      using h2 by (by100 simp)
    with h1 show "?w' ! i = top1_inverse_edge (w ! (?n - 1 - i))" by (by100 simp)
  qed
  have hfst: "\<And>i. i < ?n \<Longrightarrow> fst (?w' ! i) = fst (w ! (?n - 1 - i))"
    using hnth unfolding top1_inverse_edge_def by (by100 simp)
  have hsnd: "\<And>i. i < ?n \<Longrightarrow> snd (?w' ! i) = (\<not> snd (w ! (?n - 1 - i)))"
    using hnth unfolding top1_inverse_edge_def by (by100 simp)
  \<comment> \<open>Extract ALL 11 conditions from assms using a single extraction.\<close>
  from assms obtain P q vx vy where
      hC1: "top1_is_polygonal_region_on P ?n"
    and hC2: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hvx_dist: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    and hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hP_eq: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<?n. coeffs i) = 1
                       \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
    and hC6: "\<forall>i<?n. \<forall>j<?n.
          i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
          (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
             ((1-s) * vx i + s * vx (Suc i mod ?n),
              (1-s) * vy i + s * vy (Suc i mod ?n))
           \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
               (1-t) * vy j + t * vy (Suc j mod ?n)))"
    and hC7: "\<forall>i<?n. \<forall>j<?n. fst (w!i) = fst (w!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod ?n),
              (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd (w!i) = snd (w!j)
            then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))
            else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                    t * vy j + (1-t) * vy (Suc j mod ?n))))"
    and hC8: "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx i + t * vx (Suc i mod ?n),
                      (1-t) * vy i + t * vy (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    and hC9: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod ?n),
               (1-t) * vy i + t * vy (Suc i mod ?n))
          = q ((1-s) * vx j + s * vx (Suc j mod ?n),
               (1-s) * vy j + s * vy (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (w!i) = fst (w!j) \<and>
               (if snd (w!i) = snd (w!j) then s = t else s = 1 - t))"
    and hC10: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j) / real ?n;
                           cy = (\<Sum>j<?n. vy j) / real ?n
         in (vx i - cx) * (vy (Suc i mod ?n) - cy)
          - (vy i - cy) * (vx (Suc i mod ?n) - cx) > 0"
    and hC11: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx k - vx i) * (vy (Suc i mod ?n) - vy i)
          - (vy k - vy i) * (vx (Suc i mod ?n) - vx i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  have htopo: "is_topology_on_strict Y TY"
    using assms unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hn3: "?n \<ge> 3" using hC1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  \<comment> \<open>General position condition from hC1.\<close>
  \<comment> \<open>General position: extracted from hC1. But hC1 uses the same vx/vy from the
     quotient\_of\_scheme\_extract\_vx call (they share the same underlying witnesses).
     For now: derive from the overall definition.\<close>
  \<comment> \<open>hvx\\_gen from hC11: if vertex k were a convex combination of the others, considering
     edge k gives \\<Sum> c\\_j * cp(j) = 0 but all non-endpoint terms are strictly negative,
     forcing all coefficients to zero except Suc k mod n, contradicting distinctness.\<close>
  have hvx_gen: "\<forall>k<?n. \<not>(\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i))"
  proof (intro allI impI notI)
    fix k assume hk: "k < ?n"
    assume "\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i)"
    then obtain coeffs where
        hcoeff_nn: "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0"
      and hcoeff_k: "coeffs k = 0"
      and hcoeff_sum: "(\<Sum>i<?n. coeffs i) = 1"
      and hvxk: "vx k = (\<Sum>i<?n. coeffs i * vx i)"
      and hvyk: "vy k = (\<Sum>i<?n. coeffs i * vy i)"
      by (by100 blast)
    \<comment> \<open>Edge k \\<to> Suc k mod n. Cross product at vertex j for this edge:\<close>
    let ?sk = "Suc k mod ?n"
    let ?dx = "vx ?sk - vx k"
    let ?dy = "vy ?sk - vy k"
    let ?cp = "\<lambda>j. (vx j - vx k) * ?dy - (vy j - vy k) * ?dx"
    \<comment> \<open>Cross product at k = 0 (k is endpoint).\<close>
    have hcp_k: "?cp k = 0" by (by100 simp)
    \<comment> \<open>Cross product at Suc k mod n = 0 (other endpoint).\<close>
    have hcp_sk: "?cp ?sk = 0" by (by100 simp)
    \<comment> \<open>k \\<noteq> Suc k mod n (since n \\<ge> 3).\<close>
    have hk_neq_sk: "k \<noteq> ?sk"
    proof (cases "Suc k < ?n")
      case True thus ?thesis by (by100 simp)
    next
      case False
      hence "Suc k = ?n" using hk by (by100 simp)
      hence "?sk = 0" by (by100 simp)
      moreover have "k > 0" using \<open>Suc k = ?n\<close> hn3 by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Suc k mod n < n.\<close>
    have hn_pos: "?n > 0" using hn3 by (by100 linarith)
    have hsk_lt: "?sk < ?n"
      by (rule mod_less_divisor) (use hn_pos in \<open>by100 simp\<close>)
    \<comment> \<open>hC11 for edge k: all j with j \\<noteq> k and j \\<noteq> Suc k mod n have cp(j) < 0.\<close>
    have hcp_neg: "\<forall>j<?n. j \<noteq> k \<longrightarrow> j \<noteq> ?sk \<longrightarrow> ?cp j < 0"
      using hC11 hk by (by100 blast)
    \<comment> \<open>Direct proof that \\<Sum> coeffs j * cp(j) = 0.\<close>
    have hsum_zero: "(\<Sum>j<?n. coeffs j * ?cp j) = 0"
    proof -
      \<comment> \<open>Rewrite: cp(j) = (vx j - vx k) * dy - (vy j - vy k) * dx.\<close>
      \<comment> \<open>Decompose into: cp(j) = vx j * dy - vy j * dx - (vx k * dy - vy k * dx).\<close>
      let ?K = "vx k * ?dy - vy k * ?dx"
      have hexpand: "\<And>j. coeffs j * ?cp j = coeffs j * (vx j * ?dy - vy j * ?dx) - coeffs j * ?K"
        by (by100 argo)
      have "(\<Sum>j<?n. coeffs j * ?cp j) =
          (\<Sum>j<?n. coeffs j * (vx j * ?dy - vy j * ?dx) - coeffs j * ?K)"
        using hexpand by (by100 simp)
      \<comment> \<open>Split using sum\\_subtractf.\<close>
      also have "\<dots> = (\<Sum>j<?n. coeffs j * (vx j * ?dy - vy j * ?dx)) - (\<Sum>j<?n. coeffs j * ?K)"
        using sum_subtractf[of "\<lambda>j. coeffs j * (vx j * ?dy - vy j * ?dx)"
                               "\<lambda>j. coeffs j * ?K" "{..<?n}"]
        by (by100 simp)
      \<comment> \<open>Factor constant K out of second sum.\<close>
      also have "(\<Sum>j<?n. coeffs j * ?K) = ?K * (\<Sum>j<?n. coeffs j)"
      proof -
        have "(\<Sum>j<?n. coeffs j * ?K) = (\<Sum>j<?n. ?K * coeffs j)"
          by (intro sum.cong) (by100 simp, by100 argo)
        also have "\<dots> = ?K * (\<Sum>j<?n. coeffs j)"
          by (rule sum_distrib_left[symmetric])
        finally show ?thesis .
      qed
      \<comment> \<open>Expand first sum similarly.\<close>
      also have "(\<Sum>j<?n. coeffs j * (vx j * ?dy - vy j * ?dx))
              = (\<Sum>j<?n. coeffs j * vx j * ?dy - coeffs j * vy j * ?dx)"
        by (intro sum.cong) (by100 simp, by100 argo)
      also have "\<dots> = (\<Sum>j<?n. coeffs j * vx j * ?dy) - (\<Sum>j<?n. coeffs j * vy j * ?dx)"
        using sum_subtractf[of "\<lambda>j. coeffs j * vx j * ?dy" "\<lambda>j. coeffs j * vy j * ?dx" "{..<?n}"]
        by (by100 simp)
      \<comment> \<open>Factor out dy and dx.\<close>
      also have "(\<Sum>j<?n. coeffs j * vx j * ?dy) = (\<Sum>j<?n. coeffs j * vx j) * ?dy"
      proof -
        have "(\<Sum>j<?n. coeffs j * vx j * ?dy) = (\<Sum>j<?n. ?dy * (coeffs j * vx j))"
          by (intro sum.cong) (by100 simp, by100 argo)
        also have "\<dots> = ?dy * (\<Sum>j<?n. coeffs j * vx j)"
          by (rule sum_distrib_left[symmetric])
        finally show ?thesis by (by100 argo)
      qed
      also have "(\<Sum>j<?n. coeffs j * vy j * ?dx) = (\<Sum>j<?n. coeffs j * vy j) * ?dx"
      proof -
        have "(\<Sum>j<?n. coeffs j * vy j * ?dx) = (\<Sum>j<?n. ?dx * (coeffs j * vy j))"
          by (intro sum.cong) (by100 simp, by100 argo)
        also have "\<dots> = ?dx * (\<Sum>j<?n. coeffs j * vy j)"
          by (rule sum_distrib_left[symmetric])
        finally show ?thesis by (by100 argo)
      qed
      \<comment> \<open>Now substitute: \\<Sum> c*vx = vx k, \\<Sum> c*vy = vy k, \\<Sum> c = 1.\<close>
      finally have "(\<Sum>j<?n. coeffs j * ?cp j) =
        (\<Sum>j<?n. coeffs j * vx j) * ?dy - (\<Sum>j<?n. coeffs j * vy j) * ?dx
        - ?K * (\<Sum>j<?n. coeffs j)" by (by100 argo)
      also have "\<dots> = vx k * ?dy - vy k * ?dx - ?K * 1"
        using hvxk hvyk hcoeff_sum by (by100 simp)
      also have "\<dots> = 0" by (by100 argo)
      finally show ?thesis .
    qed
    \<comment> \<open>Each non-endpoint, non-k term \\<le> 0. Sum = 0 forces all = 0.\<close>
    have hcoeff_zero: "\<forall>j<?n. j \<noteq> k \<longrightarrow> j \<noteq> ?sk \<longrightarrow> coeffs j = 0"
    proof (intro allI impI)
      fix j assume hj: "j < ?n" and hjk: "j \<noteq> k" and hjsk: "j \<noteq> ?sk"
      have hcpj_neg: "?cp j < 0" using hcp_neg hj hjk hjsk by (by100 blast)
      have hcj_nn: "coeffs j \<ge> 0" using hcoeff_nn hj hjk by (by100 blast)
      \<comment> \<open>Proof by contradiction: if coeffs j > 0 then the j-th term < 0, and all other terms \\<le> 0,
         so the whole sum < 0, contradicting hsum\\_zero.\<close>
      show "coeffs j = 0"
      proof (rule ccontr)
        assume "coeffs j \<noteq> 0"
        hence "coeffs j > 0" using hcj_nn by (by100 simp)
        hence hj_neg: "coeffs j * ?cp j < 0" using hcpj_neg
          using mult_pos_neg by (by100 blast)
        \<comment> \<open>All other terms are \\<le> 0.\<close>
        have "\<forall>i<?n. i \<noteq> j \<longrightarrow> coeffs i * ?cp i \<le> 0"
        proof (intro allI impI)
          fix i assume "i < ?n" "i \<noteq> j"
          show "coeffs i * ?cp i \<le> 0"
          proof (cases "i = k")
            case True thus ?thesis using hcoeff_k by (by100 simp)
          next
            case False
            hence "coeffs i \<ge> 0" using hcoeff_nn \<open>i < ?n\<close> by (by100 blast)
            show ?thesis
            proof (cases "i = ?sk")
              case True thus ?thesis using hcp_sk by (by100 simp)
            next
              case False
              hence "?cp i < 0" using hcp_neg \<open>i < ?n\<close> \<open>i \<noteq> k\<close> by (by100 blast)
              thus ?thesis using \<open>coeffs i \<ge> 0\<close>
                using mult_nonneg_nonpos by (by100 fastforce)
            qed
          qed
        qed
        \<comment> \<open>Sum of non-positive terms plus one strictly negative term < 0.\<close>
        have hj_in: "j \<in> {..<?n}" using hj by (by100 simp)
        have "(\<Sum>i<?n. coeffs i * ?cp i) = coeffs j * ?cp j + (\<Sum>i\<in>{..<?n}-{j}. coeffs i * ?cp i)"
          using sum.remove[OF _ hj_in, of "\<lambda>i. coeffs i * ?cp i"] by (by100 simp)
        moreover have "(\<Sum>i\<in>{..<?n}-{j}. coeffs i * ?cp i) \<le> 0"
        proof (rule sum_nonpos)
          fix i assume "i \<in> {..<?n} - {j}"
          hence "i < ?n" "i \<noteq> j" by (by100 blast)+
          thus "coeffs i * ?cp i \<le> 0"
            using \<open>\<forall>i<?n. i \<noteq> j \<longrightarrow> coeffs i * ?cp i \<le> 0\<close> by (by100 blast)
        qed
        ultimately have "(\<Sum>i<?n. coeffs i * ?cp i) < 0" using hj_neg by (by100 linarith)
        thus False using hsum_zero by (by100 simp)
      qed
    qed
    \<comment> \<open>Only Suc k mod n can have nonzero coefficient. Since \\<Sum> = 1: coeffs(Suc k mod n) = 1.\<close>
    have hcoeff_sk1: "coeffs ?sk = 1"
    proof -
      have hall_zero: "\<forall>j<?n. j \<noteq> ?sk \<longrightarrow> coeffs j = 0"
      proof (intro allI impI)
        fix j assume "j < ?n" "j \<noteq> ?sk"
        show "coeffs j = 0"
        proof (cases "j = k")
          case True thus ?thesis using hcoeff_k by (by100 simp)
        next
          case False thus ?thesis using hcoeff_zero \<open>j < ?n\<close> \<open>j \<noteq> ?sk\<close> by (by100 blast)
        qed
      qed
      hence "(\<Sum>j<?n. coeffs j) = (\<Sum>j<?n. if j = ?sk then coeffs j else 0)"
      proof -
        have "\<And>j. j \<in> {..<?n} \<Longrightarrow> coeffs j = (if j = ?sk then coeffs j else 0)"
          using \<open>\<forall>j<?n. j \<noteq> ?sk \<longrightarrow> coeffs j = 0\<close> by (by100 auto)
        thus ?thesis by (intro sum.cong) (by100 auto)
      qed
      also have "\<dots> = coeffs ?sk"
        using hsk_lt by (by100 simp)
      finally show ?thesis using hcoeff_sum by (by100 simp)
    qed
    \<comment> \<open>Then vx k = vx(Suc k mod n) and vy k = vy(Suc k mod n).\<close>
    \<comment> \<open>Helper: all coefficients except ?sk are zero.\<close>
    have hall_zero: "\<forall>j<?n. j \<noteq> ?sk \<longrightarrow> coeffs j = 0"
    proof (intro allI impI)
      fix j assume "j < ?n" "j \<noteq> ?sk"
      show "coeffs j = 0"
      proof (cases "j = k")
        case True thus ?thesis using hcoeff_k by (by100 simp)
      next
        case False thus ?thesis using hcoeff_zero \<open>j < ?n\<close> \<open>j \<noteq> ?sk\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>Any sum \\<Sum> coeffs j * f j = f(?sk) when all other coefficients are 0 and coeffs(?sk) = 1.\<close>
    have hsum_single: "\<And>f. (\<Sum>j<?n. coeffs j * f j) = f ?sk"
    proof -
      fix f :: "nat \<Rightarrow> real"
      have "(\<Sum>j<?n. coeffs j * f j) = (\<Sum>j<?n. if j = ?sk then coeffs j * f j else 0)"
      proof (intro sum.cong)
        fix j assume "j \<in> {..<?n}"
        hence "j < ?n" by (by100 blast)
        show "coeffs j * f j = (if j = ?sk then coeffs j * f j else 0)"
          using hall_zero \<open>j < ?n\<close> by (by100 auto)
      qed (by100 simp)
      also have "\<dots> = coeffs ?sk * f ?sk" using hsk_lt by (by100 simp)
      also have "\<dots> = f ?sk" using hcoeff_sk1 by (by100 simp)
      finally show "(\<Sum>j<?n. coeffs j * f j) = f ?sk" .
    qed
    have "vx k = vx ?sk" using hvxk hsum_single[of vx] by (by100 simp)
    moreover have "vy k = vy ?sk" using hvyk hsum_single[of vy] by (by100 simp)
    ultimately have "(vx k, vy k) = (vx ?sk, vy ?sk)" by (by100 simp)
    \<comment> \<open>Contradicts vertex distinctness.\<close>
    thus False using hvx_dist hk hsk_lt hk_neq_sk by (by100 blast)
  qed
  \<comment> \<open>Step 1: Define reflection and witnesses.\<close>
  define \<rho> :: "real \<times> real \<Rightarrow> real \<times> real" where "\<rho> = (\<lambda>(x,y). (x, -y))"
  define P' where "P' = \<rho> ` P"
  define q' where "q' = q \<circ> \<rho>"
  define \<sigma> :: "nat \<Rightarrow> nat" where "\<sigma> = (\<lambda>i. ((?n) - i) mod (?n))"
  define vx' where "vx' = (\<lambda>i. vx (\<sigma> i))"
  define vy' where "vy' = (\<lambda>i. -(vy (\<sigma> i)))"
  \<comment> \<open>Key properties of \\<rho> and \\<sigma>.\<close>
  have h\<rho>_inv: "\<And>p. \<rho> (\<rho> p) = p" unfolding \<rho>_def by (by100 auto)
  have h\<rho>_bij: "bij \<rho>"
  proof (rule bijI)
    show "inj \<rho>" unfolding inj_def \<rho>_def by (by100 auto)
    show "surj \<rho>"
    proof (rule surjI)
      fix y :: "real \<times> real"
      show "\<rho> (\<rho> y) = y" by (rule h\<rho>_inv)
    qed
  qed
  have h\<sigma>_lt: "\<And>i. i < ?n \<Longrightarrow> \<sigma> i < ?n"
    unfolding \<sigma>_def
  proof -
    fix i assume "i < ?n"
    hence "0 < ?n" by (by100 linarith)
    thus "(?n - i) mod ?n < ?n" by (rule mod_less_divisor)
  qed
  \<comment> \<open>Key: for 0 < i < n, \\<sigma>(i) = n-i. For i=0, \\<sigma>(0) = 0.
     And n-1-i gives the label index. \\<sigma>(Suc i mod n) = n-1-i for 0 < i+1 < n.\<close>
  have h\<sigma>_0: "\<sigma> 0 = 0" unfolding \<sigma>_def by (by100 simp)
  have h\<sigma>_pos: "\<And>i. 0 < i \<Longrightarrow> i < ?n \<Longrightarrow> \<sigma> i = ?n - i"
    unfolding \<sigma>_def by (by100 simp)
  \<comment> \<open>Key: Suc(\\<sigma>(i)) mod n relates to the "next vertex" in reversed order.\<close>
  have h\<sigma>_suc: "\<And>i. i < ?n \<Longrightarrow> \<sigma> (Suc i mod ?n) = ?n - 1 - i"
  proof -
    fix i assume hi: "i < ?n"
    show "\<sigma> (Suc i mod ?n) = ?n - 1 - i"
    proof (cases "Suc i < ?n")
      case True
      have "\<sigma> (Suc i mod ?n) = \<sigma> (Suc i)" using True by (by100 simp)
      also have "\<dots> = ?n - Suc i" using h\<sigma>_pos[of "Suc i"] True by (by100 simp)
      also have "\<dots> = ?n - 1 - i" using True by (by100 linarith)
      finally show ?thesis .
    next
      case False
      hence "i = ?n - 1" using hi by (by100 linarith)
      have "Suc i = ?n" using \<open>i = ?n - 1\<close> hn3 by (by100 linarith)
      hence hmod0: "Suc i mod ?n = 0" by (by100 simp)
      have "\<sigma> (Suc i mod ?n) = \<sigma> 0" using hmod0 by (by100 simp)
      also have "\<dots> = 0" using h\<sigma>_0 .
      also have "(0::nat) = ?n - 1 - i" using \<open>i = ?n - 1\<close> by (by100 linarith)
      finally show ?thesis .
    qed
  qed
  \<comment> \<open>Edge point correspondence: new edge i at parameter t uses vertices \\<sigma>(i) and \\<sigma>(Suc i mod n).
     For 0 < Suc i < n: \\<sigma>(Suc i mod n) = n-1-i, \\<sigma>(i) = n-i [for i>0] or 0 [for i=0].
     The new edge i at parameter t = \\<rho>(original edge (n-1-i) at parameter (1-t)).\<close>
  \<comment> \<open>Suc(n-1-i) mod n = \\<sigma>(i): the "next vertex" after n-1-i wraps around.\<close>
  have hSuc_n1i: "\<And>i. i < ?n \<Longrightarrow> Suc (?n - 1 - i) mod ?n = \<sigma> i"
  proof -
    fix i assume hi: "i < ?n"
    show "Suc (?n - 1 - i) mod ?n = \<sigma> i"
    proof (cases "i = 0")
      case True
      hence "Suc (?n - 1 - i) = ?n" using hn3 by (by100 linarith)
      thus ?thesis unfolding \<sigma>_def using True by (by100 simp)
    next
      case False
      hence "Suc (?n - 1 - i) = ?n - i" using hi by (by100 linarith)
      moreover have "?n - i < ?n" using False hi by (by100 linarith)
      ultimately have "Suc (?n - 1 - i) mod ?n = ?n - i" by (by100 simp)
      also have "?n - i = \<sigma> i" using h\<sigma>_pos[of i] False hi by (by100 simp)
      finally show ?thesis .
    qed
  qed
  \<comment> \<open>n-1-i < n when i < n.\<close>
  have hn1i_lt: "\<And>i. i < ?n \<Longrightarrow> ?n - 1 - i < ?n" by (by100 linarith)
  \<comment> \<open>vx'/vy' in terms of \\<rho> and \\<sigma>.\<close>
  have hv'_eq: "\<And>i. (vx' i, vy' i) = (vx (\<sigma> i), -(vy (\<sigma> i)))"
    unfolding vx'_def vy'_def by (by100 simp)
  \<comment> \<open>Step 2: Show all 11 conditions for w' with witnesses P', q', vx', vy'.
     Each condition transfers via \\<rho> reflection and vertex reversal.\<close>
  have hn_pos: "0 < ?n"
    using hC1 unfolding top1_is_polygonal_region_on_def by (by100 linarith)
  \<comment> \<open>\\<sigma> is its own inverse: \\<sigma>(\\<sigma>(i)) = i when i < n.\<close>
  have h\<sigma>_inv: "\<And>i. i < ?n \<Longrightarrow> \<sigma> (\<sigma> i) = i"
  proof -
    fix i assume hi: "i < ?n"
    show "\<sigma> (\<sigma> i) = i"
    proof (cases "i = 0")
      case True thus ?thesis unfolding \<sigma>_def using hn_pos by (by100 simp)
    next
      case False
      hence hi_pos: "0 < i" by (by100 simp)
      have h1: "\<sigma> i = ?n - i" using h\<sigma>_pos[OF hi_pos hi] .
      have h2: "0 < ?n - i" using hi by (by100 linarith)
      have h3: "?n - i < ?n" using hi_pos hi by (by100 linarith)
      have "\<sigma> (\<sigma> i) = \<sigma> (?n - i)" using h1 by (by100 simp)
      also have "\<dots> = (?n - (?n - i)) mod ?n"
        unfolding \<sigma>_def by (by100 simp)
      also have "?n - (?n - i) = i" using hi by (by100 linarith)
      also have "i mod ?n = i" using hi by (by100 simp)
      finally show "\<sigma> (\<sigma> i) = i" .
    qed
  qed
  have h\<sigma>_inj: "inj_on \<sigma> {..<?n}"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> {..<?n}" and hy: "y \<in> {..<?n}" and hxy: "\<sigma> x = \<sigma> y"
    have "x = \<sigma> (\<sigma> x)" using h\<sigma>_inv hx by (by100 simp)
    also have "\<dots> = \<sigma> (\<sigma> y)" using hxy by (by100 simp)
    also have "\<dots> = y" using h\<sigma>_inv hy by (by100 simp)
    finally show "x = y" .
  qed
  have h\<sigma>_bij: "bij_betw \<sigma> {..<?n} {..<?n}"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on \<sigma> {..<?n}" by (rule h\<sigma>_inj)
    show "\<sigma> ` {..<?n} = {..<?n}"
    proof
      show "\<sigma> ` {..<?n} \<subseteq> {..<?n}" using h\<sigma>_lt by (by100 blast)
      show "{..<?n} \<subseteq> \<sigma> ` {..<?n}"
      proof
        fix x assume "x \<in> {..<?n}"
        hence "\<sigma> x \<in> {..<?n}" using h\<sigma>_lt by (by100 blast)
        moreover have "\<sigma> (\<sigma> x) = x" using h\<sigma>_inv \<open>x \<in> {..<?n}\<close> by (by100 simp)
        ultimately have "\<sigma> x \<in> {..<?n} \<and> \<sigma> (\<sigma> x) = x" by (by100 blast)
        thus "x \<in> \<sigma> ` {..<?n}" by (by100 force)
      qed
    qed
  qed
  have hsum_reindex: "\<And>g :: nat \<Rightarrow> real. (\<Sum>j<?n. g (\<sigma> j)) = (\<Sum>j<?n. g j)"
    using sum.reindex_bij_betw[OF h\<sigma>_bij] by (by100 simp)
  \<comment> \<open>C1: P' = \\<rho>(P) is a polygonal region with the same number of vertices.
     Vertices: (vx(\\<sigma>(i)), -vy(\\<sigma>(i))). Since \\<sigma> permutes {..<n} and \\<rho> is linear,
     the convex hull is \\<rho>(P).\<close>
  have hC1': "top1_is_polygonal_region_on P' ?n"
    unfolding top1_is_polygonal_region_on_def
  proof (intro conjI)
    show "?n \<ge> 3" using hn3 .
    \<comment> \<open>Witnesses: vx\\<circ>\\<sigma>, -(vy\\<circ>\\<sigma>). Need distinct + general position + P' = convex hull.\<close>
    show "\<exists>(vx'::nat\<Rightarrow>real) vy'. (\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx' i, vy' i) \<noteq> (vx' j, vy' j))
       \<and> (\<forall>k<?n. \<not>(\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> vx' k = (\<Sum>i<?n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<?n. coeffs i * vy' i)))
       \<and> P' = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx' i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy' i)}"
    proof (rule exI[of _ "\<lambda>i. vx (\<sigma> i)"], rule exI[of _ "\<lambda>i. -(vy (\<sigma> i))"])
      \<comment> \<open>Distinct: follows from \\<sigma> injective + original distinct.\<close>
      have hdist': "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow>
          (vx (\<sigma> i), -(vy (\<sigma> i))) \<noteq> (vx (\<sigma> j), -(vy (\<sigma> j)))"
      proof (intro allI impI)
        fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
        have "\<sigma> i \<noteq> \<sigma> j" using h\<sigma>_inj hi hj hij unfolding inj_on_def by (by100 blast)
        moreover have "\<sigma> i < ?n" using h\<sigma>_lt[OF hi] .
        moreover have "\<sigma> j < ?n" using h\<sigma>_lt[OF hj] .
        ultimately have "(vx (\<sigma> i), vy (\<sigma> i)) \<noteq> (vx (\<sigma> j), vy (\<sigma> j))"
          using hvx_dist by (by100 blast)
        thus "(vx (\<sigma> i), -(vy (\<sigma> i))) \<noteq> (vx (\<sigma> j), -(vy (\<sigma> j)))"
          by (by100 fastforce)
      qed
      \<comment> \<open>General position: follows from \\<sigma> bijection + original general position.\<close>
      have hgenpos': "\<forall>k<?n. \<not>(\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> vx (\<sigma> k) = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                \<and> -(vy (\<sigma> k)) = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i)))))"
      proof (intro allI impI notI)
        fix k assume hk: "k < ?n"
        assume "\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
                \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> vx (\<sigma> k) = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                \<and> -(vy (\<sigma> k)) = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))"
        then obtain coeffs where hcoeffs:
          "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0" "coeffs k = 0"
          "(\<Sum>i<?n. coeffs i) = 1"
          "vx (\<sigma> k) = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))"
          "-(vy (\<sigma> k)) = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))"
          by (by100 blast)
        \<comment> \<open>The y-condition simplifies: vy(\\<sigma> k) = \\<Sum> coeffs i * vy(\\<sigma> i).\<close>
        have hvy_eq: "vy (\<sigma> k) = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))"
        proof -
          have "(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i)))) = -(\<Sum>i<?n. coeffs i * vy (\<sigma> i))"
            using sum_negf by (by100 simp)
          with hcoeffs(5) show ?thesis by (by100 linarith)
        qed
        \<comment> \<open>Reindex: define coeffs' j = coeffs(\\<sigma> j) for j < n.
           Then coeffs' maps {..<n}\\{\\<sigma> k} nonnegatively, coeffs'(\\<sigma> k) = 0,
           and vx(\\<sigma> k) = \\<Sum> coeffs' j * vx j, vy(\\<sigma> k) = \\<Sum> coeffs' j * vy j.
           This contradicts hvx\\_gen at position \\<sigma> k.\<close>
        define coeffs' where "coeffs' = coeffs \<circ> \<sigma>"
        have hsk: "\<sigma> k < ?n" using h\<sigma>_lt[OF hk] .
        have hcoeffs'_nn: "\<forall>j<?n. j \<noteq> \<sigma> k \<longrightarrow> coeffs' j \<ge> 0"
        proof (intro allI impI)
          fix j assume hj: "j < ?n" and hjk: "j \<noteq> \<sigma> k"
          \<comment> \<open>j = \\<sigma>(\\<sigma>\\<inverse>(j)), and \\<sigma>\\<inverse>(j) \\<noteq> k since j \\<noteq> \\<sigma> k.\<close>
          have "\<exists>i<?n. \<sigma> i = j \<and> i \<noteq> k"
          proof -
            have "j \<in> \<sigma> ` {..<?n}" using hj h\<sigma>_bij unfolding bij_betw_def by (by100 blast)
            then obtain i where "i < ?n" "\<sigma> i = j" by (by100 blast)
            moreover have "i \<noteq> k" using \<open>\<sigma> i = j\<close> hjk by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          then obtain i where hi: "i < ?n" and hsi: "\<sigma> i = j" and hik: "i \<noteq> k" by (by100 blast)
          have "coeffs' j = coeffs (\<sigma> j)" unfolding coeffs'_def by (by100 simp)
          also have "\<sigma> j = \<sigma> (\<sigma> i)" using hsi h\<sigma>_inv[OF hi] by (by100 simp)
          also have "\<dots> = i" using h\<sigma>_inv[OF hi] .
          finally have heq: "coeffs' j = coeffs i" .
          have "coeffs i \<ge> 0" using hcoeffs(1)[rule_format, OF hi hik] .
          thus "coeffs' j \<ge> 0" using heq by (by100 simp)
        qed
        have hcoeffs'_k: "coeffs' (\<sigma> k) = 0"
        proof -
          have "coeffs' (\<sigma> k) = coeffs (\<sigma> (\<sigma> k))" unfolding coeffs'_def by (by100 simp)
          also have "\<sigma> (\<sigma> k) = k" using h\<sigma>_inv[OF hk] .
          finally show ?thesis using hcoeffs(2) by (by100 simp)
        qed
        have hcoeffs'_sum: "(\<Sum>j<?n. coeffs' j) = 1"
        proof -
          have "(\<Sum>j<?n. coeffs' j) = (\<Sum>j<?n. coeffs (\<sigma> j))"
            unfolding coeffs'_def by (by100 simp)
          also have "\<dots> = (\<Sum>j<?n. coeffs j)" using hsum_reindex by (by100 blast)
          finally show ?thesis using hcoeffs(3) by (by100 simp)
        qed
        have hcoeffs'_vx: "vx (\<sigma> k) = (\<Sum>j<?n. coeffs' j * vx j)"
        proof -
          have "(\<Sum>j<?n. coeffs' j * vx j) = (\<Sum>j<?n. coeffs (\<sigma> j) * vx j)"
            unfolding coeffs'_def by (by100 simp)
          also have "\<dots> = (\<Sum>i<?n. coeffs (\<sigma> (\<sigma> i)) * vx (\<sigma> i))"
            using sum.reindex_bij_betw[OF h\<sigma>_bij, of "\<lambda>j. coeffs (\<sigma> j) * vx j"]
            by (by100 simp)
          also have "\<dots> = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))"
          proof (rule sum.cong)
            fix i assume "i \<in> {..<?n}" thus "coeffs (\<sigma> (\<sigma> i)) * vx (\<sigma> i) = coeffs i * vx (\<sigma> i)"
              using h\<sigma>_inv by (by100 simp)
          qed (by100 simp)
          finally show ?thesis using hcoeffs(4) by (by100 simp)
        qed
        have hcoeffs'_vy: "vy (\<sigma> k) = (\<Sum>j<?n. coeffs' j * vy j)"
        proof -
          have "(\<Sum>j<?n. coeffs' j * vy j) = (\<Sum>j<?n. coeffs (\<sigma> j) * vy j)"
            unfolding coeffs'_def by (by100 simp)
          also have "\<dots> = (\<Sum>i<?n. coeffs (\<sigma> (\<sigma> i)) * vy (\<sigma> i))"
            using sum.reindex_bij_betw[OF h\<sigma>_bij, of "\<lambda>j. coeffs (\<sigma> j) * vy j"]
            by (by100 simp)
          also have "\<dots> = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))"
          proof (rule sum.cong)
            fix i assume "i \<in> {..<?n}" thus "coeffs (\<sigma> (\<sigma> i)) * vy (\<sigma> i) = coeffs i * vy (\<sigma> i)"
              using h\<sigma>_inv by (by100 simp)
          qed (by100 simp)
          finally show ?thesis using hvy_eq by (by100 simp)
        qed
        from hvx_gen[rule_format, OF hsk]
        show False
          using hcoeffs'_nn hcoeffs'_k hcoeffs'_sum hcoeffs'_vx hcoeffs'_vy by (by100 blast)
      qed
      \<comment> \<open>P' = convex hull: P' = \\<rho>(P) = \\<rho>(conv hull {v\\_i}) = conv hull {\\<rho>(v\\_i)}.\<close>
      have hconv': "P' = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                     \<and> y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))}"
      proof (rule set_eqI)
        fix p :: "real \<times> real"
        show "(p \<in> P') = (p \<in> {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                     \<and> y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))})"
        proof
          \<comment> \<open>Forward: p \\<in> P' \\<Longrightarrow> p \\<in> convex hull of reflected vertices.\<close>
          assume "p \<in> P'"
          hence "\<exists>q. q \<in> P \<and> p = \<rho> q" unfolding P'_def by (by100 blast)
          then obtain a b where hab: "(a, b) \<in> P" "p = (a, -b)" unfolding \<rho>_def by (by100 auto)
          from hab(1)[unfolded hP_eq] obtain coeffs where
            hc: "(\<forall>i<?n. coeffs i \<ge> 0)" "(\<Sum>i<?n. coeffs i) = 1"
                "a = (\<Sum>i<?n. coeffs i * vx i)" "b = (\<Sum>i<?n. coeffs i * vy i)"
            by (by100 blast)
          \<comment> \<open>Reindex: coeffs'(i) = coeffs(\\<sigma>(i)). Then sums reindex.\<close>
          define coeffs' where "coeffs' = coeffs \<circ> \<sigma>"
          have hc'_nn: "\<forall>i<?n. coeffs' i \<ge> 0"
            using hc(1) h\<sigma>_lt unfolding coeffs'_def by (by100 fastforce)
          have hc'_sum: "(\<Sum>i<?n. coeffs' i) = 1"
            using hsum_reindex[of coeffs] hc(2) unfolding coeffs'_def by (by100 simp)
          have hc'_vx: "a = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))"
          proof -
            have "(\<Sum>i<?n. coeffs' i * vx (\<sigma> i)) = (\<Sum>i<?n. coeffs (\<sigma> i) * vx (\<sigma> i))"
              unfolding coeffs'_def by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs j * vx j)"
              using hsum_reindex[of "\<lambda>j. coeffs j * vx j"] by (by100 simp)
            finally show ?thesis using hc(3) by (by100 simp)
          qed
          have hc'_vy: "-b = (\<Sum>i<?n. coeffs' i * (-(vy (\<sigma> i))))"
          proof -
            have "(\<Sum>i<?n. coeffs' i * (-(vy (\<sigma> i)))) = -(\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
              using sum_negf by (by100 simp)
            also have "(\<Sum>i<?n. coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs (\<sigma> i) * vy (\<sigma> i))"
              unfolding coeffs'_def by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs j * vy j)"
              using hsum_reindex[of "\<lambda>j. coeffs j * vy j"] by (by100 simp)
            finally show ?thesis using hc(4) by (by100 simp)
          qed
          have "fst p = a" "snd p = -b" using hab(2) by (by100 simp)+
          show "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                     \<and> y = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))}"
            using hab(2) hc'_nn hc'_sum hc'_vx hc'_vy by (by100 blast)
        next
          \<comment> \<open>Backward: same argument in reverse.\<close>
          assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                     \<and> y = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))}"
          then obtain x y coeffs where hp_xy: "p = (x, y)"
            and hc: "(\<forall>i<?n. 0 \<le> coeffs i)" "(\<Sum>i<?n. coeffs i) = 1"
                "x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))"
                "y = (\<Sum>i<?n. coeffs i * (- vy (\<sigma> i)))"
            by (by100 blast)
          \<comment> \<open>The point (x, -y) is in P (via reindexed coefficients).\<close>
          define coeffs0 where "coeffs0 = coeffs \<circ> \<sigma>"
          have hc0_nn: "\<forall>i<?n. coeffs0 i \<ge> 0"
            using hc(1) h\<sigma>_lt unfolding coeffs0_def by (by100 fastforce)
          have hc0_sum: "(\<Sum>i<?n. coeffs0 i) = 1"
            using hsum_reindex[of coeffs] hc(2) unfolding coeffs0_def by (by100 simp)
          have hc0_vx: "x = (\<Sum>i<?n. coeffs0 i * vx i)"
          proof -
            have "(\<Sum>i<?n. coeffs0 i * vx i) = (\<Sum>i<?n. coeffs (\<sigma> i) * vx i)"
              unfolding coeffs0_def by (by100 simp)
          also have "\<dots> = (\<Sum>j<?n. coeffs (\<sigma> (\<sigma> j)) * vx (\<sigma> j))"
              using sum.reindex_bij_betw[OF h\<sigma>_bij, of "\<lambda>j. coeffs (\<sigma> j) * vx j"] by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs j * vx (\<sigma> j))"
            proof (rule sum.cong)
              fix j assume "j \<in> {..<?n}" thus "coeffs (\<sigma> (\<sigma> j)) * vx (\<sigma> j) = coeffs j * vx (\<sigma> j)"
                using h\<sigma>_inv by (by100 simp)
            qed (by100 simp)
            finally show ?thesis using hc(3) by (by100 simp)
          qed
          have hc0_vy: "-y = (\<Sum>i<?n. coeffs0 i * vy i)"
          proof -
            have "y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))" using hc(4) .
            hence "-y = -(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))" by (by100 simp)
            also have "-(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i)))) = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))"
            proof -
              have "(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i)))) = (\<Sum>i<?n. -(coeffs i * vy (\<sigma> i)))"
                by (rule sum.cong) (by100 simp)+
              also have "\<dots> = -(\<Sum>i<?n. coeffs i * vy (\<sigma> i))"
                by (rule sum_negf)
              finally show ?thesis by (by100 linarith)
            qed
            also have "\<dots> = (\<Sum>i<?n. coeffs0 (\<sigma> i) * vy (\<sigma> i))"
            proof (rule sum.cong)
              fix i assume "i \<in> {..<?n}"
              have "coeffs0 (\<sigma> i) = coeffs (\<sigma> (\<sigma> i))" unfolding coeffs0_def by (by100 simp)
              also have "\<dots> = coeffs i" using h\<sigma>_inv \<open>i \<in> {..<?n}\<close> by (by100 simp)
              finally show "coeffs i * vy (\<sigma> i) = coeffs0 (\<sigma> i) * vy (\<sigma> i)" by (by100 simp)
            qed (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs0 j * vy j)"
              using hsum_reindex[of "\<lambda>j. coeffs0 j * vy j"] by (by100 simp)
            finally show ?thesis .
          qed
          have "(x, -y) \<in> P" unfolding hP_eq
            using hc0_nn hc0_sum hc0_vx hc0_vy by (by100 blast)
          hence "\<rho> (x, -y) \<in> P'" unfolding P'_def by (by100 blast)
          moreover have "\<rho> (x, -y) = (x, y)" unfolding \<rho>_def by (by100 simp)
          ultimately show "p \<in> P'" using hp_xy by (by100 simp)
        qed
      qed
      show "(\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow>
            (vx (\<sigma> i), - vy (\<sigma> i)) \<noteq> (vx (\<sigma> j), - vy (\<sigma> j)))
         \<and> (\<forall>k<?n. \<not>(\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> 0 \<le> coeffs i) \<and> coeffs k = 0
                  \<and> (\<Sum>i<?n. coeffs i) = 1
                  \<and> vx (\<sigma> k) = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                  \<and> - vy (\<sigma> k) = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))))
         \<and> P' = {(x, y) |x y.
                    \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                           \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                           \<and> y = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))}"
        using hdist' hgenpos' hconv' by (by100 blast)
    qed
  qed
  \<comment> \<open>C2: q' is a quotient map from P' to Y.\<close>
  \<comment> \<open>\\<rho> is continuous on R² (linear map), so continuous on P'.\<close>
  have h\<rho>_eq: "\<rho> = (\<lambda>p. (fst p, -(snd p)))"
    unfolding \<rho>_def by (by100 auto)
  have h\<rho>_cont_all: "continuous_on UNIV \<rho>"
    unfolding h\<rho>_eq
    by (intro continuous_intros)
  have h\<rho>_cont_std: "continuous_on P' \<rho>"
    using continuous_on_subset[OF h\<rho>_cont_all] by (by100 blast)
  have h\<rho>_range: "\<And>p. p \<in> P' \<Longrightarrow> \<rho> p \<in> P"
  proof -
    fix p assume "p \<in> P'"
    then obtain q where "q \<in> P" "p = \<rho> q" unfolding P'_def by (by100 blast)
    thus "\<rho> p \<in> P" using h\<rho>_inv by (by100 simp)
  qed
  have h\<rho>_cont: "top1_continuous_map_on P'
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P')
      P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) \<rho>"
    by (rule top1_continuous_map_on_real2_subspace_general[OF h\<rho>_range h\<rho>_cont_std])
  \<comment> \<open>\\<rho> is a homeomorphism P'\\<to>P. It's self-inverse, continuous, and bijective.\<close>
  have h\<rho>_bij_PP: "bij_betw \<rho> P' P"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on \<rho> P'"
    proof (rule inj_onI)
      fix x y assume "x \<in> P'" "y \<in> P'" "\<rho> x = \<rho> y"
      hence "\<rho> (\<rho> x) = \<rho> (\<rho> y)" by (by100 simp)
      thus "x = y" using h\<rho>_inv by (by100 simp)
    qed
    show "\<rho> ` P' = P"
    proof
      show "\<rho> ` P' \<subseteq> P" using h\<rho>_range by (by100 blast)
      show "P \<subseteq> \<rho> ` P'"
      proof
        fix p assume "p \<in> P"
        hence "\<rho> p \<in> P'" unfolding P'_def by (by100 blast)
        moreover have "\<rho> (\<rho> p) = p" using h\<rho>_inv by (by100 blast)
        ultimately show "p \<in> \<rho> ` P'" by (by100 force)
      qed
    qed
  qed
  have h\<rho>_cont_P: "continuous_on P \<rho>"
    using continuous_on_subset[OF h\<rho>_cont_all] by (by100 blast)
  have h\<rho>_cont_rev: "top1_continuous_map_on P
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
      P' (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P') \<rho>"
  proof -
    have "\<And>p. p \<in> P \<Longrightarrow> \<rho> p \<in> P'" unfolding P'_def by (by100 blast)
    thus ?thesis by (rule top1_continuous_map_on_real2_subspace_general[OF _ h\<rho>_cont_P])
  qed
  \<comment> \<open>inv\_into P' \\<rho> = \\<rho> on P (since \\<rho> is self-inverse).\<close>
  have h_inv_into: "\<And>p. p \<in> P \<Longrightarrow> inv_into P' \<rho> p = \<rho> p"
  proof -
    fix p assume hp: "p \<in> P"
    have h\<rho>p: "\<rho> p \<in> P'" unfolding P'_def using hp by (by100 blast)
    have "\<rho> (\<rho> p) = p" using h\<rho>_inv by (by100 blast)
    thus "inv_into P' \<rho> p = \<rho> p"
    proof -
      have hinj: "inj_on \<rho> P'" using h\<rho>_bij_PP unfolding bij_betw_def by (by100 blast)
      have "inv_into P' \<rho> (\<rho> (\<rho> p)) = \<rho> p"
        by (rule inv_into_f_f[OF hinj h\<rho>p])
      moreover have "\<rho> (\<rho> p) = p" using h\<rho>_inv by (by100 blast)
      ultimately show "inv_into P' \<rho> p = \<rho> p" by (by100 simp)
    qed
  qed
  have h_inv_cont: "top1_continuous_map_on P
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
      P' (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P')
      (inv_into P' \<rho>)"
  proof -
    \<comment> \<open>inv\_into P' \\<rho> agrees with \\<rho> on P.\<close>
    have "\<And>p. p \<in> P \<Longrightarrow> inv_into P' \<rho> p = \<rho> p" using h_inv_into .
    \<comment> \<open>Since they agree on P, continuity transfers from h\\<rho>\\_cont\\_rev.\<close>
    show ?thesis
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> P"
      have "inv_into P' \<rho> p = \<rho> p" using h_inv_into[OF hp] .
      moreover have "\<rho> p \<in> P'" unfolding P'_def using hp by (by100 blast)
      ultimately show "inv_into P' \<rho> p \<in> P'" by (by100 simp)
    next
      fix V assume "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P'"
      \<comment> \<open>Preimage of V under inv\_into = preimage of V under \\<rho> (agree on P).\<close>
      have "{x \<in> P. inv_into P' \<rho> x \<in> V} = {x \<in> P. \<rho> x \<in> V}"
      proof
        show "{x \<in> P. inv_into P' \<rho> x \<in> V} \<subseteq> {x \<in> P. \<rho> x \<in> V}"
          using h_inv_into by (by100 auto)
        show "{x \<in> P. \<rho> x \<in> V} \<subseteq> {x \<in> P. inv_into P' \<rho> x \<in> V}"
          using h_inv_into by (by100 auto)
      qed
      moreover have "{x \<in> P. \<rho> x \<in> V} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
        using h\<rho>_cont_rev[unfolded top1_continuous_map_on_def]
            \<open>V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P'\<close>
        by (by100 blast)
      ultimately show "{x \<in> P. inv_into P' \<rho> x \<in> V} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
        by (by100 simp)
    qed
  qed
  let ?TP' = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P'"
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  have hR2_top_local: "is_topology_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
          top1_open_sets_is_topology_on_UNIV] by (by100 simp)
  have hTP': "is_topology_on P' ?TP'"
    using subspace_topology_is_topology_on[OF hR2_top_local] by (by100 blast)
  have hTP_P: "is_topology_on P ?TP"
    using subspace_topology_is_topology_on[OF hR2_top_local] by (by100 blast)
  have h\<rho>_homeo: "top1_homeomorphism_on P' ?TP' P ?TP \<rho>"
    unfolding top1_homeomorphism_on_def
    using hTP' hTP_P h\<rho>_bij_PP h\<rho>_cont h_inv_cont by (by100 blast)
  have h\<rho>_quot: "top1_quotient_map_on P'
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P')
      P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) \<rho>"
    by (rule top1_homeomorphism_on_imp_quotient_map_on[OF h\<rho>_homeo])
  have hC2': "top1_quotient_map_on P' (subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) P') Y TY q'"
    unfolding q'_def
    by (rule top1_quotient_map_on_comp[OF h\<rho>_quot hC2])
  \<comment> \<open>Assemble: provide P', q', vx\\<circ>\\<sigma>, -(vy\\<circ>\\<sigma>) as witnesses.
     Conditions C3-C11 need to be proved for the inverted scheme.
     C1 and C2 are already proved (hC1', hC2').
     C3-C11 require relating the reflected/reversed conditions to the original ones.
     For now: gap in the full assembly (11 conditions).\<close>
  \<comment> \<open>Extract all 11 conditions from assms(1) and build with shifted witnesses.
     The shifted conditions use vx\\<circ>\\<sigma>, -(vy\\<circ>\\<sigma>) with the inverted scheme w'.
     Each condition transfers via the reflection \\<rho> and vertex reversal \\<sigma>.\<close>
  \<comment> \<open>All 11 original conditions are now in hC1..hC11 with consistent P, q, vx, vy.
     Prove each shifted condition C3'-C11' for the inverted scheme.\<close>
  \<comment> \<open>C3': shifted vertices distinct.\<close>
  have hC3': "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow>
      (vx (\<sigma> i), -(vy (\<sigma> i))) \<noteq> (vx (\<sigma> j), -(vy (\<sigma> j)))"
  proof (intro allI impI)
    fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
    have "\<sigma> i \<noteq> \<sigma> j" using h\<sigma>_inj hi hj hij unfolding inj_on_def by (by100 blast)
    hence hneq: "(vx (\<sigma> i), vy (\<sigma> i)) \<noteq> (vx (\<sigma> j), vy (\<sigma> j))"
      using hvx_dist h\<sigma>_lt[OF hi] h\<sigma>_lt[OF hj] by (by100 blast)
    show "(vx (\<sigma> i), -(vy (\<sigma> i))) \<noteq> (vx (\<sigma> j), -(vy (\<sigma> j)))"
    proof
      assume "(vx (\<sigma> i), - vy (\<sigma> i)) = (vx (\<sigma> j), - vy (\<sigma> j))"
      hence "vx (\<sigma> i) = vx (\<sigma> j)" "vy (\<sigma> i) = vy (\<sigma> j)" by (by100 simp)+
      with hneq show False by (by100 simp)
    qed
  qed
  \<comment> \<open>C4': shifted vertices in P'.\<close>
  have hC4': "\<forall>i<?n. (vx (\<sigma> i), -(vy (\<sigma> i))) \<in> P'"
  proof (intro allI impI)
    fix i assume hi: "i < ?n"
    have "(vx (\<sigma> i), vy (\<sigma> i)) \<in> P" using hC4 h\<sigma>_lt[OF hi] by (by100 blast)
    hence "\<rho> (vx (\<sigma> i), vy (\<sigma> i)) \<in> P'" unfolding P'_def by (by100 blast)
    thus "(vx (\<sigma> i), -(vy (\<sigma> i))) \<in> P'"
    proof -
      have "\<rho> (vx (\<sigma> i), vy (\<sigma> i)) = (vx (\<sigma> i), -(vy (\<sigma> i)))"
        unfolding \<rho>_def by (by100 simp)
      with \<open>\<rho> (vx (\<sigma> i), vy (\<sigma> i)) \<in> P'\<close> show ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>C5': P' = convex hull — already proved as hconv' inside hC1'. Reprove for assembly.\<close>
  have hC5': "P' = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))
                     \<and> y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))}"
  proof (rule set_eqI)
    fix p :: "real \<times> real"
    have hq': "\<And>a b::real. \<rho> (a, b) = (a, -b)" unfolding \<rho>_def by (by100 simp)
    show "(p \<in> P') = (p \<in> {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))})"
    proof
      assume "p \<in> P'"
      then obtain a b where hab: "(a, b) \<in> P" "p = (a, -b)"
        unfolding P'_def \<rho>_def by (by100 auto)
      from hab(1)[unfolded hP_eq] obtain coeffs where
        hc: "(\<forall>i<?n. coeffs i \<ge> 0)" "(\<Sum>i<?n. coeffs i) = 1"
            "a = (\<Sum>i<?n. coeffs i * vx i)" "b = (\<Sum>i<?n. coeffs i * vy i)"
        by (by100 blast)
      define coeffs' where "coeffs' = coeffs \<circ> \<sigma>"
      have hnn: "\<forall>i<?n. coeffs' i \<ge> 0"
        using hc(1) h\<sigma>_lt unfolding coeffs'_def by (by100 fastforce)
      have hsum: "(\<Sum>i<?n. coeffs' i) = 1"
        using hsum_reindex[of coeffs] hc(2) unfolding coeffs'_def by (by100 simp)
      have hvx: "a = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))"
        using hsum_reindex[of "\<lambda>j. coeffs j * vx j"] hc(3)
        unfolding coeffs'_def by (by100 simp)
      have hvy: "-b = (\<Sum>i<?n. coeffs' i * (-(vy (\<sigma> i))))"
      proof -
        have "(\<Sum>i<?n. coeffs' i * (-(vy (\<sigma> i)))) = (\<Sum>i<?n. -(coeffs' i * vy (\<sigma> i)))"
          by (rule sum.cong) (by100 simp)+
        also have "\<dots> = -(\<Sum>i<?n. coeffs' i * vy (\<sigma> i))" by (rule sum_negf)
        finally have "(\<Sum>i<?n. coeffs' i * (-(vy (\<sigma> i)))) = -(\<Sum>i<?n. coeffs' i * vy (\<sigma> i))" .
        also have "(\<Sum>i<?n. coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs (\<sigma> i) * vy (\<sigma> i))"
          unfolding coeffs'_def by (by100 simp)
        also have "\<dots> = (\<Sum>j<?n. coeffs j * vy j)"
          using hsum_reindex[of "\<lambda>j. coeffs j * vy j"] by (by100 simp)
        finally show ?thesis using hc(4) by (by100 simp)
      qed
      show "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))}"
        using hab(2) hnn hsum hvx hvy by (by100 blast)
    next
      assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * - vy (\<sigma> i))}"
      then obtain x y coeffs where hp: "p = (x, y)"
        and hc: "(\<forall>i<?n. 0 \<le> coeffs i)" "(\<Sum>i<?n. coeffs i) = 1"
            "x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i))" "y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))"
        by (by100 blast)
      define coeffs0 where "coeffs0 = coeffs \<circ> \<sigma>"
      have hnn: "\<forall>i<?n. coeffs0 i \<ge> 0"
        using hc(1) h\<sigma>_lt unfolding coeffs0_def by (by100 fastforce)
      have hsum: "(\<Sum>i<?n. coeffs0 i) = 1"
        using hsum_reindex[of coeffs] hc(2) unfolding coeffs0_def by (by100 simp)
      have hx: "x = (\<Sum>i<?n. coeffs0 i * vx i)"
      proof -
        have "(\<Sum>i<?n. coeffs0 i * vx i) = (\<Sum>i<?n. coeffs (\<sigma> i) * vx i)"
          unfolding coeffs0_def by (by100 simp)
        also have "\<dots> = (\<Sum>j<?n. coeffs (\<sigma> (\<sigma> j)) * vx (\<sigma> j))"
          using sum.reindex_bij_betw[OF h\<sigma>_bij, of "\<lambda>i. coeffs (\<sigma> i) * vx i"] by (by100 simp)
        also have "\<dots> = (\<Sum>j<?n. coeffs j * vx (\<sigma> j))"
        proof (rule sum.cong)
          fix j assume "j \<in> {..<?n}" thus "coeffs (\<sigma> (\<sigma> j)) * vx (\<sigma> j) = coeffs j * vx (\<sigma> j)"
            using h\<sigma>_inv by (by100 simp)
        qed (by100 simp)
        finally show ?thesis using hc(3) by (by100 simp)
      qed
      have hy_neg: "-y = (\<Sum>i<?n. coeffs0 i * vy i)"
      proof -
        have "y = (\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))" using hc(4) .
        hence "-y = -(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i))))" by (by100 simp)
        also have "(\<Sum>i<?n. coeffs i * (-(vy (\<sigma> i)))) = (\<Sum>i<?n. -(coeffs i * vy (\<sigma> i)))"
          by (rule sum.cong) (by100 simp)+
        also have "\<dots> = -(\<Sum>i<?n. coeffs i * vy (\<sigma> i))" by (rule sum_negf)
        finally have "-y = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))" by (by100 linarith)
        also have "\<dots> = (\<Sum>i<?n. coeffs (\<sigma> (\<sigma> i)) * vy (\<sigma> i))"
        proof (rule sum.cong)
          fix i assume "i \<in> {..<?n}" thus "coeffs i * vy (\<sigma> i) = coeffs (\<sigma> (\<sigma> i)) * vy (\<sigma> i)"
            using h\<sigma>_inv by (by100 simp)
        qed (by100 simp)
        also have "\<dots> = (\<Sum>j<?n. coeffs (\<sigma> j) * vy j)"
          using sum.reindex_bij_betw[OF h\<sigma>_bij, of "\<lambda>i. coeffs (\<sigma> i) * vy i"] by (by100 simp)
        finally show ?thesis unfolding coeffs0_def by (by100 simp)
      qed
      have "(x, -y) \<in> P" unfolding hP_eq using hnn hsum hx hy_neg by (by100 blast)
      hence "\<rho> (x, -y) \<in> P'" unfolding P'_def by (by100 blast)
      moreover have "\<rho> (x, -y) = (x, y)" unfolding \<rho>_def by (by100 simp)
      ultimately show "p \<in> P'" using hp by (by100 simp)
    qed
  qed
  \<comment> \<open>C6'-C11': For these conditions, the key insight is:
     New edge i at parameter t corresponds to \\<rho>(original edge (n-1-i) at parameter (1-t)).
     The label at new position i comes from original position (n-1-i).
     With \\<sigma>(Suc i mod n) giving the "next vertex" index in the reversed ordering.

     Key relation: for i < n,
       (1-t)*vx(\\<sigma> i) + t*vx(\\<sigma>(Suc i mod n)) = (1-t)*vx(\\<sigma> i) + t*vx(n-1-i)
       and the corresponding y-component is negated.
       This equals \\<rho>(original edge point at (n-1-i) with parameter (1-t)).\<close>
  \<comment> \<open>C6': non-adjacent edges don't share interior points.\<close>
  have hC6': "\<forall>i<?n. \<forall>j<?n.
          i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
          (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
             ((1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n)),
              (1-s) * (-(vy (\<sigma> i))) + s * (-(vy (\<sigma> (Suc i mod ?n)))))
           \<noteq> ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
               (1-t) * (-(vy (\<sigma> j))) + t * (-(vy (\<sigma> (Suc j mod ?n))))))"
  proof (intro allI impI ballI)
    fix i j and s t :: real
    assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
      and hSij: "Suc i mod ?n \<noteq> j" and hijS: "i \<noteq> Suc j mod ?n"
      and hs: "s \<in> {0<..<1::real}" and ht: "t \<in> {0<..<1::real}"
    let ?i' = "?n - 1 - i" and ?j' = "?n - 1 - j"
    have hi': "?i' < ?n" using hn1i_lt[OF hi] .
    have hj': "?j' < ?n" using hn1i_lt[OF hj] .
    have hij': "?i' \<noteq> ?j'"
    proof
      assume "?i' = ?j'"
      hence "i = j" using hi hj by (by100 linarith)
      with hij show False by (by100 simp)
    qed
    \<comment> \<open>Non-adjacency at original positions.\<close>
    have hSij': "Suc ?i' mod ?n \<noteq> ?j'"
    proof -
      have "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
      have "?j' = \<sigma> (Suc j mod ?n)" using h\<sigma>_suc[OF hj] by (by100 simp)
      have "Suc j mod ?n < ?n" using hn_pos by (rule mod_less_divisor)
      hence "\<sigma> i \<noteq> \<sigma> (Suc j mod ?n)"
        using h\<sigma>_inj hi hijS unfolding inj_on_def by (by100 blast)
      thus ?thesis using \<open>Suc ?i' mod ?n = \<sigma> i\<close> \<open>?j' = \<sigma> (Suc j mod ?n)\<close> by (by100 simp)
    qed
    have hijS': "?i' \<noteq> Suc ?j' mod ?n"
    proof -
      have "Suc ?j' mod ?n = \<sigma> j" using hSuc_n1i[OF hj] .
      have "?i' = \<sigma> (Suc i mod ?n)" using h\<sigma>_suc[OF hi] by (by100 simp)
      have "Suc i mod ?n < ?n" using hn_pos by (rule mod_less_divisor)
      hence "\<sigma> (Suc i mod ?n) \<noteq> \<sigma> j"
        using h\<sigma>_inj hj hSij unfolding inj_on_def by (by100 blast)
      thus ?thesis using \<open>?i' = \<sigma> (Suc i mod ?n)\<close> \<open>Suc ?j' mod ?n = \<sigma> j\<close> by (by100 simp)
    qed
    \<comment> \<open>Original C6 at (i',j') with parameters (1-s,1-t) \\<in> (0,1).\<close>
    have h1s: "1-s \<in> {0<..<1::real}" using hs by (by100 auto)
    have h1t: "1-t \<in> {0<..<1::real}" using ht by (by100 auto)
    from hC6[rule_format, OF hi' hj' hij' hSij' hijS' h1s h1t]
    have hne_orig: "((1-(1-s)) * vx ?i' + (1-s) * vx (Suc ?i' mod ?n),
              (1-(1-s)) * vy ?i' + (1-s) * vy (Suc ?i' mod ?n))
           \<noteq> ((1-(1-t)) * vx ?j' + (1-t) * vx (Suc ?j' mod ?n),
               (1-(1-t)) * vy ?j' + (1-t) * vy (Suc ?j' mod ?n))" .
    \<comment> \<open>Simplify: 1-(1-s) = s, Suc i' mod n = \\<sigma> i, i' = \\<sigma>(Si).\<close>
    have hne_simp: "(s * vx ?i' + (1-s) * vx (\<sigma> i), s * vy ?i' + (1-s) * vy (\<sigma> i))
           \<noteq> (t * vx ?j' + (1-t) * vx (\<sigma> j), t * vy ?j' + (1-t) * vy (\<sigma> j))"
      using hne_orig hSuc_n1i[OF hi] hSuc_n1i[OF hj] by (by100 simp)
    \<comment> \<open>The reflected edge point: x-same, y-negated. If original \\<noteq>, reflected \\<noteq>.\<close>
    have h_si: "\<sigma> (Suc i mod ?n) = ?i'" using h\<sigma>_suc[OF hi] by (by100 simp)
    have h_sj: "\<sigma> (Suc j mod ?n) = ?j'" using h\<sigma>_suc[OF hj] by (by100 simp)
    \<comment> \<open>The new edge at (i,s) has x = (1-s)*vx(\\<sigma> i) + s*vx(i') and y negated.\<close>
    have hx_eq_i: "(1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n))
                 = (1-s) * vx (\<sigma> i) + s * vx ?i'" using h_si by (by100 simp)
    have hx_eq_j: "(1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n))
                 = (1-t) * vx (\<sigma> j) + t * vx ?j'" using h_sj by (by100 simp)
    \<comment> \<open>The x-components are: (1-s)*vx(\\<sigma> i) + s*vx(i') vs s*vx(i') + (1-s)*vx(\\<sigma> i) — same.\<close>
    have hx_match_i: "(1-s) * vx (\<sigma> i) + s * vx ?i' = s * vx ?i' + (1-s) * vx (\<sigma> i)"
      by (by100 linarith)
    have hx_match_j: "(1-t) * vx (\<sigma> j) + t * vx ?j' = t * vx ?j' + (1-t) * vx (\<sigma> j)"
      by (by100 linarith)
    \<comment> \<open>If the x-components match (commuted), the points differ iff the original differs.\<close>
    show "((1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n)),
           (1-s) * (-(vy (\<sigma> i))) + s * (-(vy (\<sigma> (Suc i mod ?n)))))
        \<noteq> ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
            (1-t) * (-(vy (\<sigma> j))) + t * (-(vy (\<sigma> (Suc j mod ?n)))))"
    proof
      assume "((1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n)),
           (1-s) * (-(vy (\<sigma> i))) + s * (-(vy (\<sigma> (Suc i mod ?n)))))
        = ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
            (1-t) * (-(vy (\<sigma> j))) + t * (-(vy (\<sigma> (Suc j mod ?n)))))"
      hence "(1-s) * vx (\<sigma> i) + s * vx ?i' = (1-t) * vx (\<sigma> j) + t * vx ?j'
        \<and> (1-s) * (-(vy (\<sigma> i))) + s * (-(vy ?i')) = (1-t) * (-(vy (\<sigma> j))) + t * (-(vy ?j'))"
        using h_si h_sj by (by100 simp)
      hence "s * vx ?i' + (1-s) * vx (\<sigma> i) = t * vx ?j' + (1-t) * vx (\<sigma> j)
        \<and> s * vy ?i' + (1-s) * vy (\<sigma> i) = t * vy ?j' + (1-t) * vy (\<sigma> j)"
        by (by100 argo)
      with hne_simp show False by (by100 simp)
    qed
  qed
  \<comment> \<open>C7': identification pattern for the inverted scheme.\<close>
  have hC7': "\<forall>i<?n. \<forall>j<?n. fst (?w'!i) = fst (?w'!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q' ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
              (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n)))))
         = (if snd (?w'!i) = snd (?w'!j)
            then q' ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
                    (1-t) * (-(vy (\<sigma> j))) + t * (-(vy (\<sigma> (Suc j mod ?n)))))
            else q' (t * vx (\<sigma> j) + (1-t) * vx (\<sigma> (Suc j mod ?n)),
                    t * (-(vy (\<sigma> j))) + (1-t) * (-(vy (\<sigma> (Suc j mod ?n)))))))"
  proof (intro allI impI ballI)
    fix i j t assume hi: "i < ?n" and hj: "j < ?n" and ht: "t \<in> I_set"
      and hfst_eq: "fst (?w' ! i) = fst (?w' ! j)"
    let ?i' = "?n - 1 - i" and ?j' = "?n - 1 - j"
    have hi': "?i' < ?n" and hj': "?j' < ?n" using hi hj by (by100 linarith)+
    have hfst_orig: "fst (w ! ?i') = fst (w ! ?j')"
      using hfst_eq hfst[OF hi] hfst[OF hj] by (by100 simp)
    have hsnd_iff: "(snd (?w' ! i) = snd (?w' ! j)) = (snd (w ! ?i') = snd (w ! ?j'))"
      using hsnd[OF hi] hsnd[OF hj] by (by100 simp)
    have h_si: "\<sigma> (Suc i mod ?n) = ?i'" using h\<sigma>_suc[OF hi] by (by100 simp)
    have h_sj: "\<sigma> (Suc j mod ?n) = ?j'" using h\<sigma>_suc[OF hj] by (by100 simp)
    have hSi': "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
    have hSj': "Suc ?j' mod ?n = \<sigma> j" using hSuc_n1i[OF hj] .
    have h1t: "1-t \<in> I_set" using ht unfolding top1_unit_interval_def by (by100 simp)
    \<comment> \<open>q'(a,b) = q(a,-b).\<close>
    have hq': "\<And>a b::real. q' (a, b) = q (a, -b)"
      unfolding q'_def \<rho>_def by (by100 simp)
    \<comment> \<open>Apply orig C7 at (i', j') with param (1-t), then rewrite.\<close>
    from hC7[rule_format, OF hi' hj' hfst_orig h1t]
    have horig: "q ((1-(1-t)) * vx ?i' + (1-t) * vx (Suc ?i' mod ?n),
                    (1-(1-t)) * vy ?i' + (1-t) * vy (Suc ?i' mod ?n))
      = (if snd (w!?i') = snd (w!?j')
         then q ((1-(1-t)) * vx ?j' + (1-t) * vx (Suc ?j' mod ?n),
                 (1-(1-t)) * vy ?j' + (1-t) * vy (Suc ?j' mod ?n))
         else q ((1-t) * vx ?j' + (1-(1-t)) * vx (Suc ?j' mod ?n),
                 (1-t) * vy ?j' + (1-(1-t)) * vy (Suc ?j' mod ?n)))" .
    have horig2: "q (t * vx ?i' + (1-t) * vx (\<sigma> i), t * vy ?i' + (1-t) * vy (\<sigma> i))
      = (if snd (w!?i') = snd (w!?j')
         then q (t * vx ?j' + (1-t) * vx (\<sigma> j), t * vy ?j' + (1-t) * vy (\<sigma> j))
         else q ((1-t) * vx ?j' + t * vx (\<sigma> j), (1-t) * vy ?j' + t * vy (\<sigma> j)))"
      using horig hSi' hSj' by (by100 simp)
    \<comment> \<open>The final step: convert q expressions to q' using hq' and h\\_si, h\\_sj.\<close>
    show "q' ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
              (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n)))))
         = (if snd (?w'!i) = snd (?w'!j)
            then q' ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
                    (1-t) * (-(vy (\<sigma> j))) + t * (-(vy (\<sigma> (Suc j mod ?n)))))
            else q' (t * vx (\<sigma> j) + (1-t) * vx (\<sigma> (Suc j mod ?n)),
                    t * (-(vy (\<sigma> j))) + (1-t) * (-(vy (\<sigma> (Suc j mod ?n))))))"
    proof -
      \<comment> \<open>Convert q' to q: LHS.\<close>
      have hLHS: "q' ((1-t) * vx (\<sigma> i) + t * vx ?i',
                      (1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i')))
        = q (t * vx ?i' + (1-t) * vx (\<sigma> i), t * vy ?i' + (1-t) * vy (\<sigma> i))"
      proof -
        have "q' ((1-t) * vx (\<sigma> i) + t * vx ?i',
                   (1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i')))
          = q ((1-t) * vx (\<sigma> i) + t * vx ?i',
               -((1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i'))))"
          using hq' by (by100 simp)
        also have "-((1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i')))
          = t * vy ?i' + (1-t) * vy (\<sigma> i)" by (by100 argo)
        finally show ?thesis by (by100 argo)
      qed
      \<comment> \<open>Convert q' to q: RHS same-direction case.\<close>
      have hRHS_same: "q' ((1-t) * vx (\<sigma> j) + t * vx ?j',
                      (1-t) * (-(vy (\<sigma> j))) + t * (-(vy ?j')))
        = q (t * vx ?j' + (1-t) * vx (\<sigma> j), t * vy ?j' + (1-t) * vy (\<sigma> j))"
      proof -
        have "q' ((1-t) * vx (\<sigma> j) + t * vx ?j',
                   (1-t) * (-(vy (\<sigma> j))) + t * (-(vy ?j')))
          = q ((1-t) * vx (\<sigma> j) + t * vx ?j',
               -((1-t) * (-(vy (\<sigma> j))) + t * (-(vy ?j'))))"
          using hq' by (by100 simp)
        also have "-((1-t) * (-(vy (\<sigma> j))) + t * (-(vy ?j')))
          = t * vy ?j' + (1-t) * vy (\<sigma> j)" by (by100 argo)
        finally show ?thesis by (by100 argo)
      qed
      \<comment> \<open>Convert q' to q: RHS opposite-direction case.\<close>
      have hRHS_opp: "q' (t * vx (\<sigma> j) + (1-t) * vx ?j',
                      t * (-(vy (\<sigma> j))) + (1-t) * (-(vy ?j')))
        = q ((1-t) * vx ?j' + t * vx (\<sigma> j), (1-t) * vy ?j' + t * vy (\<sigma> j))"
      proof -
        have "q' (t * vx (\<sigma> j) + (1-t) * vx ?j',
                   t * (-(vy (\<sigma> j))) + (1-t) * (-(vy ?j')))
          = q (t * vx (\<sigma> j) + (1-t) * vx ?j',
               -(t * (-(vy (\<sigma> j))) + (1-t) * (-(vy ?j'))))"
          using hq' by (by100 simp)
        also have "-(t * (-(vy (\<sigma> j))) + (1-t) * (-(vy ?j')))
          = (1-t) * vy ?j' + t * vy (\<sigma> j)" by (by100 argo)
        finally show ?thesis by (by100 argo)
      qed
      show ?thesis using horig2 hLHS hRHS_same hRHS_opp h_si h_sj hsnd_iff by (by100 presburger)
    qed
  qed
  \<comment> \<open>Helpers for edge set transfer.\<close>
  have h_1t_I: "\<And>t::real. t \<in> I_set \<Longrightarrow> 1-t \<in> I_set"
    unfolding top1_unit_interval_def by (by100 simp)
  have h_Suc_j_sigma: "\<And>j. j < ?n \<Longrightarrow> Suc j mod ?n = \<sigma> (?n - 1 - j)"
  proof -
    fix j assume hj: "j < ?n"
    show "Suc j mod ?n = \<sigma> (?n - 1 - j)"
    proof (cases "j < ?n - 1")
      case True
      have "0 < ?n - 1 - j" using True by (by100 linarith)
      have "?n - 1 - j < ?n" using True hj by (by100 linarith)
      have "\<sigma> (?n - 1 - j) = ?n - (?n - 1 - j)"
        using h\<sigma>_pos[OF \<open>0 < ?n - 1 - j\<close> \<open>?n - 1 - j < ?n\<close>] by (by100 simp)
      also have "?n - (?n - 1 - j) = Suc j" using True hj by (by100 linarith)
      finally show ?thesis using True by (by100 simp)
    next
      case False
      hence "j = ?n - 1" using hj by (by100 linarith)
      hence "?n - 1 - j = 0" by (by100 linarith)
      have "Suc j = ?n" using \<open>j = ?n - 1\<close> hn3 by (by100 linarith)
      hence "Suc j mod ?n = 0" by (by100 simp)
      also have "0 = \<sigma> 0" using h\<sigma>_0 by (by100 simp)
      finally show ?thesis using \<open>?n - 1 - j = 0\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Edge set transfer via standalone lemma.\<close>
  have h_edge_transfer: "\<And>p. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                      (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n))))))
    \<Longrightarrow> (\<forall>j<?n. \<forall>t\<in>I_set.
        \<rho> p \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
              (1-t) * vy j + t * vy (Suc j mod ?n)))"
    using reflected_not_on_edges_imp_original[OF hn3]
    unfolding \<sigma>_def \<rho>_def by (by100 blast)
  \<comment> \<open>C8': interior injectivity.\<close>
  have hC8': "\<forall>p\<in>P'. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                      (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n))))))
             \<longrightarrow> (\<forall>p'\<in>P'. q' p = q' p' \<longrightarrow> p = p')"
  proof (intro ballI impI allI)
    fix p p' assume hp: "p \<in> P'" and hp': "p' \<in> P'" and hq: "q' p = q' p'"
      and hne: "\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                      (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n)))))"
    \<comment> \<open>\\<rho>(p) \\<in> P and \\<rho>(p') \\<in> P.\<close>
    have h\<rho>p: "\<rho> p \<in> P" using hp h\<rho>_range by (by100 blast)
    have h\<rho>p': "\<rho> p' \<in> P" using hp' h\<rho>_range by (by100 blast)
    \<comment> \<open>q(\\<rho>(p)) = q(\\<rho>(p')) from q' definition.\<close>
    have hq_rho: "q (\<rho> p) = q (\<rho> p')" using hq unfolding q'_def by (by100 simp)
    \<comment> \<open>\\<rho>(p) is not on any original edge — use edge set equality via \\<sigma>.\<close>
    have hne_orig: "\<forall>j<?n. \<forall>t\<in>I_set.
        \<rho> p \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
              (1-t) * vy j + t * vy (Suc j mod ?n))"
      by (rule h_edge_transfer[OF hne])
    \<comment> \<open>Apply original C8: \\<rho>(p) = \\<rho>(p').\<close>
    have "\<rho> p = \<rho> p'"
      using hC8 h\<rho>p hne_orig h\<rho>p' hq_rho by (by100 blast)
    \<comment> \<open>\\<rho> injective \\<Longrightarrow> p = p'.\<close>
    thus "p = p'" using h\<rho>_inv by (by100 metis)
  qed
  \<comment> \<open>C9': boundary injectivity.\<close>
  have hC9': "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q' ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
               (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n)))))
          = q' ((1-s) * vx (\<sigma> j) + s * vx (\<sigma> (Suc j mod ?n)),
               (1-s) * (-(vy (\<sigma> j))) + s * (-(vy (\<sigma> (Suc j mod ?n)))))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (?w'!i) = fst (?w'!j) \<and>
               (if snd (?w'!i) = snd (?w'!j) then s = t else s = 1 - t))"
  proof (intro allI impI ballI)
    fix i j t s assume hi: "i < ?n" and hj: "j < ?n" and ht: "t \<in> I_set" and hs: "s \<in> I_set"
      and hq_eq: "q' ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
               (1-t) * (-(vy (\<sigma> i))) + t * (-(vy (\<sigma> (Suc i mod ?n)))))
          = q' ((1-s) * vx (\<sigma> j) + s * vx (\<sigma> (Suc j mod ?n)),
               (1-s) * (-(vy (\<sigma> j))) + s * (-(vy (\<sigma> (Suc j mod ?n)))))"
    let ?i' = "?n - 1 - i" and ?j' = "?n - 1 - j"
    have hi': "?i' < ?n" and hj': "?j' < ?n" using hi hj by (by100 linarith)+
    have h_si: "\<sigma> (Suc i mod ?n) = ?i'" using h\<sigma>_suc[OF hi] by (by100 simp)
    have h_sj: "\<sigma> (Suc j mod ?n) = ?j'" using h\<sigma>_suc[OF hj] by (by100 simp)
    have hSi': "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
    have hSj': "Suc ?j' mod ?n = \<sigma> j" using hSuc_n1i[OF hj] .
    have hq': "\<And>a b::real. q' (a, b) = q (a, -b)"
      unfolding q'_def \<rho>_def by (by100 simp)
    have h1t: "1-t \<in> I_set" and h1s: "1-s \<in> I_set"
      using ht hs unfolding top1_unit_interval_def by (by100 simp)+
    \<comment> \<open>Convert q' equality to q equality via hq'.\<close>
    have hq_orig: "q (t * vx ?i' + (1-t) * vx (\<sigma> i), t * vy ?i' + (1-t) * vy (\<sigma> i))
        = q (s * vx ?j' + (1-s) * vx (\<sigma> j), s * vy ?j' + (1-s) * vy (\<sigma> j))"
    proof -
      have hqi: "q' ((1-t) * vx (\<sigma> i) + t * vx ?i', (1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i')))
        = q ((1-t) * vx (\<sigma> i) + t * vx ?i', -((1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i'))))"
        using hq' by (by100 simp)
      have hqj: "q' ((1-s) * vx (\<sigma> j) + s * vx ?j', (1-s) * (-(vy (\<sigma> j))) + s * (-(vy ?j')))
        = q ((1-s) * vx (\<sigma> j) + s * vx ?j', -((1-s) * (-(vy (\<sigma> j))) + s * (-(vy ?j'))))"
        using hq' by (by100 simp)
      from hq_eq have "q ((1-t) * vx (\<sigma> i) + t * vx ?i', -((1-t) * (-(vy (\<sigma> i))) + t * (-(vy ?i'))))
        = q ((1-s) * vx (\<sigma> j) + s * vx ?j', -((1-s) * (-(vy (\<sigma> j))) + s * (-(vy ?j'))))"
        using hqi hqj h_si h_sj by (by100 simp)
      thus ?thesis by (by100 argo)
    qed
    \<comment> \<open>Apply orig C9 at (i', j') with params (1-t, 1-s).\<close>
    have hq_orig2: "q ((1-(1-t)) * vx ?i' + (1-t) * vx (Suc ?i' mod ?n),
               (1-(1-t)) * vy ?i' + (1-t) * vy (Suc ?i' mod ?n))
          = q ((1-(1-s)) * vx ?j' + (1-s) * vx (Suc ?j' mod ?n),
               (1-(1-s)) * vy ?j' + (1-s) * vy (Suc ?j' mod ?n))"
      using hq_orig hSi' hSj' by (by100 simp)
    from hC9[rule_format, OF hi' hj' h1t h1s hq_orig2]
    have hC9_result: "(?i' = ?j' \<and> (1-t) = (1-s))
            \<or> (fst (w!?i') = fst (w!?j') \<and>
               (if snd (w!?i') = snd (w!?j') then (1-s) = (1-t) else (1-s) = 1 - (1-t)))" .
    \<comment> \<open>Convert back: i'=j' \\<Longleftrightarrow> i=j, 1-t=1-s \\<Longleftrightarrow> t=s, fst/snd transfer.\<close>
    show "(i = j \<and> t = s)
            \<or> (fst (?w'!i) = fst (?w'!j) \<and>
               (if snd (?w'!i) = snd (?w'!j) then s = t else s = 1 - t))"
    proof (cases "?i' = ?j'")
      case True
      hence hij: "i = j" using hi hj by (by100 linarith)
      from hC9_result True have "1 - t = 1 - s" by (by100 force)
      hence hts: "t = s" by (by100 linarith)
      show ?thesis using hij hts by (by100 blast)
    next
      case False
      with hC9_result have "fst (w!?i') = fst (w!?j') \<and>
               (if snd (w!?i') = snd (w!?j') then (1-s) = (1-t) else (1-s) = 1 - (1-t))"
        by (by100 blast)
      hence hfst_w: "fst (w!?i') = fst (w!?j')"
        and hsnd_w: "if snd (w!?i') = snd (w!?j') then (1-s) = (1-t) else (1-s) = 1 - (1-t)"
        by (by100 blast)+
      have hfst_w': "fst (?w'!i) = fst (?w'!j)"
        using hfst_w hfst[OF hi] hfst[OF hj] by (by100 simp)
      have hsnd_iff: "(snd (?w'!i) = snd (?w'!j)) = (snd (w!?i') = snd (w!?j'))"
        using hsnd[OF hi] hsnd[OF hj] by (by100 simp)
      have "if snd (?w'!i) = snd (?w'!j) then s = t else s = 1 - t"
      proof (cases "snd (w!?i') = snd (w!?j')")
        case True with hsnd_w have "1-s = 1-t" by (by100 simp)
        hence "s = t" by (by100 linarith)
        thus ?thesis using True hsnd_iff by (by100 simp)
      next
        case False with hsnd_w have "1-s = 1-(1-t)" by (by100 simp)
        hence "s = 1-t" by (by100 linarith)
        thus ?thesis using False hsnd_iff by (by100 simp)
      qed
      with hfst_w' show ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>C10': counterclockwise.\<close>
  have hC10': "\<forall>i<?n. let cx = (\<Sum>j<?n. vx (\<sigma> j)) / real ?n;
                           cy = (\<Sum>j<?n. (-(vy (\<sigma> j)))) / real ?n
         in (vx (\<sigma> i) - cx) * ((-(vy (\<sigma> (Suc i mod ?n)))) - cy)
          - ((-(vy (\<sigma> i))) - cy) * (vx (\<sigma> (Suc i mod ?n)) - cx) > 0"
  proof (intro allI impI)
    fix i assume hi: "i < ?n"
    let ?i' = "?n - 1 - i"
    \<comment> \<open>Centroids: cx' = cx (sum reindexing), cy' = -cy.\<close>
    have hcx: "(\<Sum>j<?n. vx (\<sigma> j)) = (\<Sum>j<?n. vx j)" using hsum_reindex by (by100 blast)
    have hcy: "(\<Sum>j<?n. (-(vy (\<sigma> j)))) = -(\<Sum>j<?n. vy j)"
    proof -
      have "(\<Sum>j<?n. (-(vy (\<sigma> j)))) = -(\<Sum>j<?n. vy (\<sigma> j))" by (rule sum_negf)
      also have "(\<Sum>j<?n. vy (\<sigma> j)) = (\<Sum>j<?n. vy j)" using hsum_reindex by (by100 blast)
      finally show ?thesis .
    qed
    \<comment> \<open>Apply original C10 at position n-1-i.\<close>
    have hi': "?i' < ?n" using hn1i_lt[OF hi] .
    from hC10[rule_format, OF hi']
    have horig: "let cx = (\<Sum>j<?n. vx j) / real ?n; cy = (\<Sum>j<?n. vy j) / real ?n
         in (vx ?i' - cx) * (vy (Suc ?i' mod ?n) - cy) - (vy ?i' - cy) * (vx (Suc ?i' mod ?n) - cx) > 0" .
    have h1: "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
    have h2: "?i' = \<sigma> (Suc i mod ?n)" using h\<sigma>_suc[OF hi] by (by100 simp)
    \<comment> \<open>The original expression at i' with cx,cy = the reflected expression at i with cx,-cy.\<close>
    let ?cx = "(\<Sum>j<?n. vx j) / real ?n"
    let ?cy = "(\<Sum>j<?n. vy j) / real ?n"
    let ?a = "vx (\<sigma> i)" and ?b = "vy (\<sigma> i)" and ?c = "vx ?i'" and ?d = "vy ?i'"
    \<comment> \<open>The original C10 at i' gives the cross product > 0.
       After substitution h1 (Suc i' mod n = \\<sigma> i): uses \\<sigma> i and i'.\<close>
    have horig2: "(vx ?i' - ?cx) * (vy (\<sigma> i) - ?cy)
        - (vy ?i' - ?cy) * (vx (\<sigma> i) - ?cx) > 0"
      using horig h1 by (by100 simp)
    \<comment> \<open>The reflected cross product = original cross product (algebraic identity).\<close>
    have halg: "(?a - ?cx) * ((-?d) - (-?cy)) - ((-?b) - (-?cy)) * (?c - ?cx)
             = (?c - ?cx) * (?b - ?cy) - (?d - ?cy) * (?a - ?cx)"
      by (by100 argo)
    have hresult: "(?a - ?cx) * ((-?d) - (-?cy)) - ((-?b) - (-?cy)) * (?c - ?cx) > 0"
      using horig2 halg by (by100 linarith)
    show "let cx = (\<Sum>j<?n. vx (\<sigma> j)) / real ?n;
              cy = (\<Sum>j<?n. (-(vy (\<sigma> j)))) / real ?n
         in (vx (\<sigma> i) - cx) * ((-(vy (\<sigma> (Suc i mod ?n)))) - cy)
          - ((-(vy (\<sigma> i))) - cy) * (vx (\<sigma> (Suc i mod ?n)) - cx) > 0"
      using hresult hcx hcy h2 by (by100 simp)
  qed
  \<comment> \<open>C11': strict edge-side.\<close>
  have hC11': "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx (\<sigma> k) - vx (\<sigma> i)) * ((-(vy (\<sigma> (Suc i mod ?n)))) - (-(vy (\<sigma> i))))
          - ((-(vy (\<sigma> k))) - (-(vy (\<sigma> i)))) * (vx (\<sigma> (Suc i mod ?n)) - vx (\<sigma> i)) < 0"
  proof (intro allI impI)
    fix i k assume hi: "i < ?n" and hk: "k < ?n" and hki: "k \<noteq> i"
      and hkSi: "k \<noteq> Suc i mod ?n"
    \<comment> \<open>Map to original C11 at (n-1-i, \\<sigma> k).\<close>
    let ?i' = "?n - 1 - i"
    have hi': "?i' < ?n" using hn1i_lt[OF hi] .
    have hsk: "\<sigma> k < ?n" using h\<sigma>_lt[OF hk] .
    \<comment> \<open>Non-adjacency: \\<sigma> k \\<noteq> n-1-i and \\<sigma> k \\<noteq> Suc(n-1-i) mod n.\<close>
    have hsk_ne_i': "\<sigma> k \<noteq> ?i'"
    proof -
      have "?i' = \<sigma> (Suc i mod ?n)" using h\<sigma>_suc[OF hi] by (by100 simp)
      moreover have "Suc i mod ?n < ?n"
      proof -
        have "0 < ?n" using hn_pos .
        thus ?thesis by (rule mod_less_divisor)
      qed
      moreover have "\<sigma> k \<noteq> \<sigma> (Suc i mod ?n)"
        using h\<sigma>_inj hk \<open>Suc i mod ?n < ?n\<close> hkSi
        unfolding inj_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hsk_ne_Si': "\<sigma> k \<noteq> Suc ?i' mod ?n"
    proof -
      have "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
      moreover have "\<sigma> k \<noteq> \<sigma> i"
        using h\<sigma>_inj hi hk hki unfolding inj_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Apply original C11.\<close>
    from hC11[rule_format, OF hi' hsk hsk_ne_i' hsk_ne_Si']
    have horig: "(vx (\<sigma> k) - vx ?i') * (vy (Suc ?i' mod ?n) - vy ?i')
        - (vy (\<sigma> k) - vy ?i') * (vx (Suc ?i' mod ?n) - vx ?i') < 0" .
    \<comment> \<open>Rewrite using Suc(n-1-i) mod n = \\<sigma>(i) and n-1-i = \\<sigma>(Suc i mod n).\<close>
    have h1: "Suc ?i' mod ?n = \<sigma> i" using hSuc_n1i[OF hi] .
    have h2: "?i' = \<sigma> (Suc i mod ?n)" using h\<sigma>_suc[OF hi] by (by100 simp)
    \<comment> \<open>The LHS of the goal equals the original expression (algebraic identity).
       Substitute \\<sigma>(Suc i mod n) = n-1-i and Suc(n-1-i) mod n = \\<sigma>(i).\<close>
    \<comment> \<open>The LHS equals the original expression after substitution + algebraic identity.\<close>
    let ?a = "vx (\<sigma> i)" and ?b = "vy (\<sigma> i)" and ?c = "vx ?i'" and ?d = "vy ?i'"
        and ?e = "vx (\<sigma> k)" and ?f = "vy (\<sigma> k)"
    have hLHS: "(vx (\<sigma> k) - vx (\<sigma> i)) * ((-(vy (\<sigma> (Suc i mod ?n)))) - (-(vy (\<sigma> i))))
        - ((-(vy (\<sigma> k))) - (-(vy (\<sigma> i)))) * (vx (\<sigma> (Suc i mod ?n)) - vx (\<sigma> i))
        = (?e - ?a) * (?b - ?d) - (?b - ?f) * (?c - ?a)" using h2 by (by100 simp)
    have hRHS: "(?e - ?c) * (?b - ?d) - (?f - ?d) * (?a - ?c) < 0" using horig h1 by (by100 simp)
    \<comment> \<open>Algebraic identity: (e-a)(b-d) - (b-f)(c-a) = (e-c)(b-d) - (f-d)(a-c).\<close>
    have halg: "(?e - ?a) * (?b - ?d) - (?b - ?f) * (?c - ?a)
             = (?e - ?c) * (?b - ?d) - (?f - ?d) * (?a - ?c)"
      by (by100 argo)
    show "(vx (\<sigma> k) - vx (\<sigma> i)) * ((-(vy (\<sigma> (Suc i mod ?n)))) - (-(vy (\<sigma> i))))
        - ((-(vy (\<sigma> k))) - (-(vy (\<sigma> i)))) * (vx (\<sigma> (Suc i mod ?n)) - vx (\<sigma> i)) < 0"
      using hLHS hRHS halg by (by100 linarith)
  qed
  show ?thesis
    unfolding top1_quotient_of_scheme_on_def hlen
    apply (intro conjI)
    apply (rule htopo)
    apply (rule exI[of _ P'])
    apply (rule exI[of _ q'])
    apply (rule exI[of _ "\<lambda>i. vx (\<sigma> i)"])
    apply (rule exI[of _ "\<lambda>i. -(vy (\<sigma> i))"])
    apply (intro conjI)
    subgoal using hC1' by assumption
    subgoal using hC2' by assumption
    subgoal using hC3' by assumption
    subgoal using hC4' by assumption
    subgoal using hC5' by assumption
    subgoal using hC6' by assumption
    subgoal using hC7' by assumption
    subgoal using hC8' by assumption
    subgoal using hC9' by assumption
    subgoal using hC10' by assumption
    subgoal using hC11' by assumption
    done
qed

\<comment> \<open>Relabel with fresh label: proved via same witnesses, fst-equality pattern preserved.\<close>
lemma quotient_of_scheme_relabel_fresh:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "new \<notin> fst ` set w"
      and "new \<noteq> old"
  shows "top1_quotient_of_scheme_on Y TY (map (\<lambda>(l,b). (if l = old then new else l, b)) w)"
proof -
  let ?w' = "map (\<lambda>(l,b). (if l = old then new else l, b)) w"
  have hlen: "length ?w' = length w" by (by100 simp)
  have hfst: "\<And>i. i < length w \<Longrightarrow> fst (?w'!i) = (if fst (w!i) = old then new else fst (w!i))"
  proof -
    fix i assume hi: "i < length w"
    obtain l b where hlb: "w ! i = (l, b)" by (cases "w ! i")
    have "?w' ! i = (\<lambda>(l,b). (if l = old then new else l, b)) (w ! i)"
      using hi by (by100 simp)
    also have "\<dots> = (if l = old then new else l, b)" using hlb by (by100 simp)
    finally show "fst (?w' ! i) = (if fst (w ! i) = old then new else fst (w ! i))"
      using hlb by (by100 simp)
  qed
  \<comment> \<open>fst equality pattern is preserved: since 'new' is fresh, relabeling old\\<to>new
     doesn't create new equalities or destroy existing ones.\<close>
  have hfst_eq: "\<And>i j. \<lbrakk>i < length w; j < length w\<rbrakk> \<Longrightarrow>
      (fst (?w'!i) = fst (?w'!j)) = (fst (w!i) = fst (w!j))"
  proof -
    fix i j assume hi: "i < length w" and hj: "j < length w"
    have h_new_i: "fst (w!i) \<noteq> new" using assms(2) hi by (by100 fastforce)
    have h_new_j: "fst (w!j) \<noteq> new" using assms(2) hj by (by100 fastforce)
    have hfi: "fst (?w'!i) = (if fst (w!i) = old then new else fst (w!i))" using hfst[OF hi] .
    have hfj: "fst (?w'!j) = (if fst (w!j) = old then new else fst (w!j))" using hfst[OF hj] .
    show "(fst (?w'!i) = fst (?w'!j)) = (fst (w!i) = fst (w!j))"
      unfolding hfi hfj using h_new_i h_new_j assms(3) by (by100 auto)
  qed
  \<comment> \<open>snd equality pattern: snd is unchanged, and the fst-equality condition is preserved.\<close>
  have hsnd_nth: "\<And>i. i < length w \<Longrightarrow> snd (?w'!i) = snd (w!i)"
  proof -
    fix i assume hi: "i < length w"
    obtain l b where hlb: "w ! i = (l, b)" by (cases "w ! i")
    have "?w' ! i = (\<lambda>(l,b). (if l = old then new else l, b)) (w ! i)"
      using hi by (by100 simp)
    also have "\<dots> = (if l = old then new else l, b)" using hlb by (by100 simp)
    finally show "snd (?w' ! i) = snd (w ! i)" using hlb by (by100 simp)
  qed
  have hsnd: "\<And>i j. \<lbrakk>i < length w; j < length w; fst (w!i) = fst (w!j)\<rbrakk> \<Longrightarrow>
      (snd (?w'!i) = snd (?w'!j)) = (snd (w!i) = snd (w!j))"
    using hsnd_nth by (by100 simp)
  \<comment> \<open>fst at each position: NOT the same as original (old\\<to>new), so can't use transfer directly.
     But we can still use transfer by noting the fst-equality pattern is preserved.\<close>
  \<comment> \<open>For the transfer, we need fst(?w'!i) = fst(w!i). This is FALSE (old\\<to>new).
     But transfer only needs fst-EQUALITY preservation + snd-EQUALITY preservation.
     Actually, looking at the transfer lemma, it requires fst(?w'!i) = fst(w!i) at each position.
     Since relabel changes fst, we can't use transfer. But the original definition's
     C7 and C9 conditions only depend on the EQUALITY PATTERN of fst and snd,
     not on the actual values. So we can prove this by showing the same witnesses work.\<close>
  \<comment> \<open>Actually, the quotient\_of\_scheme\_on definition's conditions C7 and C9 reference
     fst(scheme!i) and snd(scheme!i) directly. With relabeled scheme, these change.
     But C7 says: if fst(w'!i) = fst(w'!j), then identify edges i and j.
     Since the fst-equality pattern is preserved (hfst\_eq), this holds iff the original C7 holds.
     The snd direction is also preserved by hsnd. So the proof should work.\<close>
  show ?thesis
    unfolding top1_quotient_of_scheme_on_def hlen
    using assms(1)[unfolded top1_quotient_of_scheme_on_def]
    apply (elim conjE exE)
    apply (intro conjI)
    apply assumption  \<comment> \<open>is\_topology\_on\_strict\<close>
    apply (rule_tac x=P in exI)
    apply (rule_tac x=q in exI)
    apply (rule_tac x=vx in exI)
    apply (rule_tac x=vy in exI)
    apply (intro conjI)
    apply assumption  \<comment> \<open>C1\<close>
    apply assumption  \<comment> \<open>C2\<close>
    apply assumption  \<comment> \<open>C3\<close>
    apply assumption  \<comment> \<open>C4\<close>
    apply assumption  \<comment> \<open>C5\<close>
    apply assumption  \<comment> \<open>C6\<close>
    \<comment> \<open>C7: identification. Rewrite fst/snd equality via hfst\_eq/hsnd.\<close>
    subgoal premises prems
      using prems(8) hfst_eq hsnd by (by100 presburger)
    apply assumption  \<comment> \<open>C8\<close>
    \<comment> \<open>C9: boundary injectivity. Rewrite using hfst\_eq and hsnd.\<close>
    subgoal premises prems for P q vx vy
    proof (intro allI ballI impI)
      fix i j ta s
      assume hi: "i < length w" and hj: "j < length w" and hta: "ta \<in> I_set" and hs: "s \<in> I_set"
        and hq_eq: "q ((1 - ta) * vx i + ta * vx (Suc i mod length w),
              (1 - ta) * vy i + ta * vy (Suc i mod length w)) =
             q ((1 - s) * vx j + s * vx (Suc j mod length w),
              (1 - s) * vy j + s * vy (Suc j mod length w))"
      \<comment> \<open>prems(10) is original C9 with 'w' scheme. OF instantiation to get conclusion.\<close>
      have hC9_w: "(i = j \<and> ta = s) \<or> (fst (w!i) = fst (w!j) \<and>
             (if snd (w!i) = snd (w!j) then s = ta else s = 1 - ta))"
        using prems(10) hi hj hta hs hq_eq by (by100 blast)
      show "(i = j \<and> ta = s) \<or> (fst (?w'!i) = fst (?w'!j) \<and>
             (if snd (?w'!i) = snd (?w'!j) then s = ta else s = 1 - ta))"
      proof (cases "i = j \<and> ta = s")
        case True thus ?thesis by (by100 blast)
      next
        case False
        with hC9_w have "fst (w!i) = fst (w!j) \<and>
             (if snd (w!i) = snd (w!j) then s = ta else s = 1 - ta)" by (by100 blast)
        moreover have "(fst (?w'!i) = fst (?w'!j)) = (fst (w!i) = fst (w!j))"
          using hfst_eq[OF hi hj] .
        moreover have "(snd (?w'!i) = snd (?w'!j)) = (snd (w!i) = snd (w!j))"
          using hsnd_nth[OF hi] hsnd_nth[OF hj] by (by100 simp)
        ultimately show ?thesis by (by100 presburger)
      qed
    qed
    apply assumption  \<comment> \<open>C10\<close>
    apply assumption  \<comment> \<open>C11\<close>
    done
qed

\<comment> \<open>WARNING: quotient\\_of\\_scheme\\_relabel WITHOUT freshness is FALSE in general.
   If new already labels another edge pair, relabeling merges edge classes.
   The CORRECT version is quotient\\_of\\_scheme\\_relabel\\_fresh (above) with freshness.
   This gap should NOT be filled — it should be replaced by using valid operations
   or adding freshness to the elementary relabel constructor (per expert audit step 5).\<close>
\<comment> \<open>quotient\\_of\\_scheme\\_relabel: REMOVED. Was FALSE without freshness.
   The correct version is quotient\\_of\\_scheme\\_relabel\\_fresh (above).
   No live code depends on this lemma (elementary\\_operation\\_preserves\\_quotient is dead).\<close>


\<comment> \<open>quotient\\_of\\_scheme\\_context\\_left: REMOVED. Was dead code (only called by
   elementary\\_operation\\_preserves\\_quotient which is dead). Context-left is handled
   directly in valid\\_operation\\_preserves\\_quotient\\_homeo as closure infrastructure.\<close>

\<comment> \<open>Helper: a mod n < n for n > 0. Needed because by100 simp can't fire mod\_less\_divisor
   in the large AlgTop simpset within 1s.\<close>
lemma mod_less_n: "(0::nat) < n \<Longrightarrow> (a :: nat) mod n < n"
  by simp

\<comment> \<open>If a mod n = (a+d) mod n then n dvd d.\<close>
lemma mod_eq_dvd: "\<lbrakk>(0::nat) < n; a mod n = (a + d) mod n\<rbrakk> \<Longrightarrow> n dvd d"
proof -
  assume hn: "0 < n" and heq: "a mod n = (a + d) mod n"
  \<comment> \<open>div/mod decomposition: a = q*n + r, a+d = q'*n + r with same r.
     So d = (q'-q)*n, hence n dvd d.\<close>
  define q where "q = a div n"
  define q' where "q' = (a + d) div n"
  define r where "r = a mod n"
  have ha: "a = q * n + r" unfolding q_def r_def by simp
  have had: "a + d = q' * n + r" unfolding q'_def r_def using heq by simp
  have "q * n + r + d = q' * n + r" using ha had by (by100 linarith)
  hence heq2: "q * n + d = q' * n" by (by100 linarith)
  hence hle_prod: "q * n \<le> q' * n" by (by100 linarith)
  have hle: "q \<le> q'"
  proof (rule ccontr)
    assume "\<not> q \<le> q'"
    hence "q > q'" by (by100 linarith)
    hence "q * n > q' * n" using hn by (by100 simp)
    with hle_prod show False by (by100 linarith)
  qed
  from heq2 hle have hd: "d = (q' - q) * n" by (simp add: diff_mult_distrib)
  show "n dvd d" unfolding hd by (by100 simp)
qed

\<comment> \<open>Shift injectivity: (x+k) mod n = (y+k) mod n implies x=y for x,y < n.\<close>
lemma shift_mod_inj: "\<lbrakk>(0::nat) < n; x < n; y < n; (x + k) mod n = (y + k) mod n\<rbrakk> \<Longrightarrow> x = y"
proof -
  assume h: "0 < n" "x < n" "y < n" "(x + k) mod n = (y + k) mod n"
  \<comment> \<open>Proof by basic nat arithmetic: x mod n = x, y mod n = y since x,y < n.\<close>
  from h(4) have "(x + k) mod n = (y + k) mod n" .
  \<comment> \<open>x < n, y < n \\<Longrightarrow> (x + k) mod n determines x uniquely.\<close>
  \<comment> \<open>If x \\<le> y: (y-x) + (x+k) = (y+k). Mod n: (y-x) = 0 mod n. Since y-x < n: y-x=0.\<close>
  show "x = y"
  proof (rule ccontr)
    assume "x \<noteq> y"
    show False
    proof (cases "x < y")
      case True
      hence "y + k = x + k + (y - x)" by (by100 linarith)
      hence "(y + k) mod n = (x + k + (y - x)) mod n" by (by100 metis)
      hence "(x + k) mod n = (x + k + (y - x)) mod n" using h(4) by (by100 metis)
      hence "(x + k + (y - x)) mod n = (x + k) mod n" by (by100 metis)
      hence "n dvd (y - x)" using mod_eq_dvd[OF h(1)] by (by100 metis)
      moreover have "0 < y - x" "y - x < n" using True h(3) by (by100 linarith)+
      ultimately show False using nat_dvd_not_less by (by100 blast)
    next
      case False
      hence "x > y" using \<open>x \<noteq> y\<close> by (by100 linarith)
      hence "x + k = y + k + (x - y)" by (by100 linarith)
      hence "(x + k) mod n = (y + k + (x - y)) mod n" by (by100 metis)
      hence "(y + k) mod n = (y + k + (x - y)) mod n" using h(4) by (by100 metis)
      hence "n dvd (x - y)" using mod_eq_dvd[OF h(1)] by (by100 metis)
      moreover have "0 < x - y" "x - y < n" using \<open>x > y\<close> h(2) by (by100 linarith)+
      ultimately show False using nat_dvd_not_less by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Key property: Suc((i+k) mod n) mod n = (Suc i + k) mod n.\<close>
lemma suc_mod_shift: "(0::nat) < n \<Longrightarrow> Suc ((i + k) mod n) mod n = (Suc i + k) mod n"
  by presburger \<comment> \<open>raw presburger needed; by100 times out in AlgTop context\<close>

\<comment> \<open>Mod add left: (a + b) mod n = (a mod n + b) mod n.\<close>
lemma mod_add_left: "((a::nat) + b) mod n = (a mod n + b) mod n"
  by (rule mod_add_left_eq[symmetric])

\<comment> \<open>Shifted distinctness: if vertices are distinct, they're still distinct after cyclic shift.\<close>
lemma shifted_distinct:
  assumes "(0::nat) < n" and "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
  shows "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx ((i+k) mod n), vy ((i+k) mod n)) \<noteq> (vx ((j+k) mod n), vy ((j+k) mod n))"
proof (intro allI impI)
  fix i j assume hi: "i < n" and hj: "j < n" and hne: "i \<noteq> j"
  have h1: "(i+k) mod n < n" by (rule mod_less_n[OF assms(1)])
  have h2: "(j+k) mod n < n" by (rule mod_less_n[OF assms(1)])
  have h3: "(i+k) mod n \<noteq> (j+k) mod n" using shift_mod_inj[OF assms(1) hi hj] hne by (by100 metis)
  show "(vx ((i+k) mod n), vy ((i+k) mod n)) \<noteq> (vx ((j+k) mod n), vy ((j+k) mod n))"
    using assms(2) h1 h2 h3 by (by100 blast)
qed

\<comment> \<open>Shifted membership: if vertex i is in P, then vertex (i+k) mod n is in P.\<close>
lemma shifted_in_P:
  assumes "(0::nat) < n" and "\<forall>i<n. (vx i, vy i) \<in> P"
  shows "\<forall>i<n. (vx ((i+k) mod n), vy ((i+k) mod n)) \<in> P"
proof (intro allI impI)
  fix i assume "i < n"
  have hlt: "(i+k) mod n < n" using mod_less_n[OF assms(1)] .
  from assms(2)[rule_format, OF hlt] show "(vx ((i+k) mod n), vy ((i+k) mod n)) \<in> P" .
qed

\<comment> \<open>Transfer lemma: if two schemes have the same length, same fst at each position,
   and the same snd-equality pattern for same-label pairs, then quotient\_of\_scheme\_on
   is equivalent for both. This factors out the geometric conditions from the scheme-specific ones.\<close>
lemma quotient_of_scheme_transfer:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w' = length w"
      and "\<And>i. i < length w \<Longrightarrow> fst (w'!i) = fst (w!i)"
      and "\<And>i j. \<lbrakk>i < length w; j < length w; fst (w!i) = fst (w!j)\<rbrakk> \<Longrightarrow>
           (snd (w'!i) = snd (w'!j)) = (snd (w!i) = snd (w!j))"
  shows "top1_quotient_of_scheme_on Y TY w'"
proof -
  \<comment> \<open>Rewriting rule: (fst(w'!i) = fst(w'!j)) = (fst(w!i) = fst(w!j)).\<close>
  have hfst_eq: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow>
      (fst (w'!i) = fst (w'!j)) = (fst (w!i) = fst (w!j))"
    using assms(3) by (by100 metis)
  \<comment> \<open>Strategy: unfold definition for both sides. The formula for w' differs from w only
     in terms involving fst(scheme!i)/snd(scheme!i). Use hfst\_eq and assms(4) to rewrite.\<close>
  from assms(1) show ?thesis
    unfolding top1_quotient_of_scheme_on_def assms(2)
    apply (elim conjE exE)
    apply (intro conjI)
    apply assumption  \<comment> \<open>is\_topology\_on\_strict\<close>
    apply (rule_tac x=P in exI)
    apply (rule_tac x=q in exI)
    apply (rule_tac x=vx in exI)
    apply (rule_tac x=vy in exI)
    apply (intro conjI)
    \<comment> \<open>C1-C6: geometric conditions. Don't reference scheme. Same witnesses + same length.\<close>
    \<comment> \<open>11 subgoals (one per condition). Close each:\<close>
    subgoal by assumption \<comment> \<open>C1: polygonal region\<close>
    subgoal by assumption \<comment> \<open>C2: quotient map\<close>
    subgoal by assumption \<comment> \<open>C3: vertices distinct\<close>
    subgoal by assumption \<comment> \<open>C4: vertices in P\<close>
    subgoal by assumption \<comment> \<open>C5: P = convex hull\<close>
    subgoal by assumption \<comment> \<open>C6: non-adjacent\<close>
    \<comment> \<open>C7: identification. Rewrite fst(w'!i) to fst(w!i), snd equality similarly.\<close>
    subgoal premises prems for P q vx vy
      using prems assms(3) assms(4) by (by100 presburger)
    \<comment> \<open>C8: interior injectivity\<close>
    subgoal by assumption
    \<comment> \<open>C9: boundary injectivity. Rewrite fst/snd.\<close>
    subgoal premises prems for P q vx vy
    proof (intro allI ballI impI)
      fix i j ta s
      assume hi: "i < length w" and hj: "j < length w" and hta: "ta \<in> I_set" and hs: "s \<in> I_set"
          and hq_eq: "q ((1 - ta) * vx i + ta * vx (Suc i mod length w),
                (1 - ta) * vy i + ta * vy (Suc i mod length w)) =
               q ((1 - s) * vx j + s * vx (Suc j mod length w),
                (1 - s) * vy j + s * vy (Suc j mod length w))"
      \<comment> \<open>From the old C9 (prems) with the same q equality: get the conclusion for w.\<close>
      from prems have hC9_w: "\<forall>i<length w. \<forall>j<length w. \<forall>ta\<in>I_set. \<forall>s\<in>I_set.
          q ((1-ta)*vx i+ta*vx(Suc i mod length w),(1-ta)*vy i+ta*vy(Suc i mod length w))
        = q ((1-s)*vx j+s*vx(Suc j mod length w),(1-s)*vy j+s*vy(Suc j mod length w))
        \<longrightarrow> (i=j \<and> ta=s) \<or> (fst(w!i)=fst(w!j) \<and> (if snd(w!i)=snd(w!j) then s=ta else s=1-ta))"
        by (by100 blast)
      from hC9_w[rule_format, OF hi hj hta hs hq_eq]
      have "(i = j \<and> ta = s) \<or>
            (fst (w!i) = fst (w!j) \<and> (if snd (w!i) = snd (w!j) then s = ta else s = 1 - ta))" .
      thus "(i = j \<and> ta = s) \<or>
            (fst (w'!i) = fst (w'!j) \<and> (if snd (w'!i) = snd (w'!j) then s = ta else s = 1 - ta))"
      proof (elim disjE conjE)
        assume "i = j" "ta = s" thus ?thesis by (by100 blast)
      next
        assume hfst_w: "fst (w!i) = fst (w!j)"
            and hbranch: "if snd (w!i) = snd (w!j) then s = ta else s = 1 - ta"
        have "fst (w'!i) = fst (w'!j)" using assms(3)[OF hi] assms(3)[OF hj] hfst_w by (by100 simp)
        moreover have "(if snd (w'!i) = snd (w'!j) then s = ta else s = 1 - ta)"
        proof -
          have hsnd_iff: "(snd (w'!i) = snd (w'!j)) = (snd (w!i) = snd (w!j))"
            using assms(4)[OF hi hj hfst_w] .
          show ?thesis using hbranch hsnd_iff by (by100 presburger)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>C10: counterclockwise\<close>
    subgoal by assumption
    \<comment> \<open>C11: strict edge-side\<close>
    subgoal by assumption
    done
  qed

\<comment> \<open>Placeholder: quotient\_of\_scheme\_transfer\_bij was moved before quotient\_of\_scheme\_rotate.\<close>

\<comment> \<open>Flipping the orientation of all edges with a given label preserves quotient\_of\_scheme\_on.
   Same polygon P, same quotient map q, same vertex positions vx/vy.
   The identification conditions use snd(scheme!i) = snd(scheme!j) which is preserved
   when both i and j have the same label (both flip or neither does).\<close>
lemma quotient_scheme_flip_label:
  assumes "top1_quotient_of_scheme_on Y TY w"
  shows "top1_quotient_of_scheme_on Y TY (map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) w)"
proof -
  let ?f = "\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)"
  let ?w' = "map ?f w"
  have hlen: "length ?w' = length w" by (by100 simp)
  have hfst: "\<And>i. i < length w \<Longrightarrow> fst (?w'!i) = fst (w!i)"
  proof -
    fix i assume "i < length w"
    obtain l bo where "w!i = (l, bo)" by (cases "w!i")
    thus "fst (?w'!i) = fst (w!i)" using \<open>i < length w\<close> by (by100 simp)
  qed
  have hsnd_eq: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow> fst (w!i) = fst (w!j) \<Longrightarrow>
      (snd (?w'!i) = snd (?w'!j)) = (snd (w!i) = snd (w!j))"
  proof -
    fix i j assume hi: "i < length w" and hj: "j < length w" and hfst_eq: "fst (w!i) = fst (w!j)"
    obtain li bi where hlbi: "w!i = (li, bi)" by (cases "w!i")
    obtain lj bj where hlbj: "w!j = (lj, bj)" by (cases "w!j")
    have "li = lj" using hfst_eq hlbi hlbj by (by100 simp)
    show "(snd (?w'!i) = snd (?w'!j)) = (snd (w!i) = snd (w!j))"
      using hi hj hlbi hlbj \<open>li = lj\<close> by (by100 simp)
  qed
  \<comment> \<open>The definition for w' is the same as for w (same P, q, vx, vy witnesses).
     Conditions not referencing snd transfer via hlen. Conditions referencing snd
     transfer via hfst+hsnd\_eq.\<close>
  \<comment> \<open>Extract topology from old quotient.\<close>
  from assms have htopo: "is_topology_on_strict Y TY"
    unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>The old quotient's existential witnesses work for the new scheme too.
     All conditions either don't reference scheme!i at all, or reference fst/snd
     which transfer via hfst and hsnd\_eq.\<close>
  \<comment> \<open>The flip doesn't change fst, and the snd equality is preserved (by hsnd\_eq).
     So the identification pattern is the same. Therefore the same witnesses work.\<close>
  have hfst_map: "\<And>i. i < length w \<Longrightarrow>
      fst (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w ! i) = fst (w ! i)"
    using hfst by (by100 blast)
  have hsnd_map: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow> fst (w!i) = fst (w!j) \<Longrightarrow>
      (snd (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w ! i)
       = snd (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w ! j))
    = (snd (w ! i) = snd (w ! j))"
    using hsnd_eq by (by100 blast)
  \<comment> \<open>Proof: the definition for ?w' holds with the SAME witnesses as for w.\<close>
  \<comment> \<open>Key: after unfolding, the goal's fst/snd terms can be rewritten to match the assumption's.\<close>
  have hfst_eq_full: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow>
      (fst (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w ! i)
       = fst (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w ! j))
    = (fst (w ! i) = fst (w ! j))"
    using hfst_map by (by100 simp)
  \<comment> \<open>The proof strategy: unfold the biconditional definition, extract topology + existential,
     then show the existential for w' using the same witnesses.
     For geometric conditions (not referencing scheme!i): they're identical.
     For conditions 7,9 (referencing fst/snd of scheme): rewrite via hfst\_map/hsnd\_map.\<close>
  show ?thesis
    by (rule quotient_of_scheme_transfer[OF assms hlen hfst hsnd_eq])
qed
\<comment> \<open>Generalized transfer: quotient\_of\_scheme\_on is preserved when the EQUALITY PATTERN
   of fst/snd is preserved via a bijection sigma on vertex indices.
   Witnesses: vx'(i) = vx(sigma(i)), vy'(i) = vy(sigma(i)).
   Covers rotate (cyclic shift), invert (reversal), relabel (injective rename).\<close>
lemma quotient_of_scheme_transfer_bij:
  assumes "top1_quotient_of_scheme_on Y TY w"
      and "length w' = length w"
      and "bij_betw \<sigma> {..<length w} {..<length w}"
      and "\<And>i. i < length w \<Longrightarrow> fst (w'!i) = fst (w!(\<sigma> i))"
      and "\<And>i. i < length w \<Longrightarrow> snd (w'!i) = snd (w!(\<sigma> i))"
      and "\<And>i. i < length w \<Longrightarrow> Suc (\<sigma> i) mod (length w) = \<sigma> (Suc i mod (length w))"
  shows "top1_quotient_of_scheme_on Y TY w'"
proof -
  \<comment> \<open>Key: fst equality pattern is preserved via sigma.\<close>
  have hfst_eq: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow>
      (fst (w'!i) = fst (w'!j)) = (fst (w!(\<sigma> i)) = fst (w!(\<sigma> j)))"
    using assms(4) by (by100 metis)
  have hsnd_eq: "\<And>i j. i < length w \<Longrightarrow> j < length w \<Longrightarrow>
      fst (w!(\<sigma> i)) = fst (w!(\<sigma> j)) \<Longrightarrow>
      (snd (w'!i) = snd (w'!j)) = (snd (w!(\<sigma> i)) = snd (w!(\<sigma> j)))"
    using assms(5) by (by100 metis)
  \<comment> \<open>Since sigma is a bijection, (fst(w!(sigma i)) = fst(w!(sigma j))) = (fst(w!i') = fst(w!j'))
     where i'=sigma(i), j'=sigma(j). So the fst/snd equality pattern over w' at positions i,j
     equals the pattern over w at positions sigma(i), sigma(j).\<close>
  have h\<sigma>_lt: "\<And>i. i < length w \<Longrightarrow> \<sigma> i < length w"
    using assms(3) unfolding bij_betw_def by (by100 blast)
  have h\<sigma>_inj: "inj_on \<sigma> {..<length w}"
    using assms(3) unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Extract topology.\<close>
  from assms(1) have htopo: "is_topology_on_strict Y TY"
    unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  \<comment> \<open>The quotient has the form: is\_topo \\<and> (\\<exists>P q vx vy. C1\\<and>...\\<and>C11).
     Extract the existential part, then rebuild with shifted witnesses.\<close>
  \<comment> \<open>Key idea: define w\_sigma = map (\\<lambda>i. w!(sigma i)) [0..<n], which is w permuted by sigma.
     Then w\_sigma has the SAME identification pattern as w (just at different positions).
     And w' has fst/snd matching w\_sigma at each position (by assms 4,5).
     So quotient\_of\_scheme\_transfer can convert from w\_sigma to w'.
     And w and w\_sigma have the same quotient (sigma is just a relabeling of vertex positions).\<close>
  have h\<sigma>_lt: "\<And>i. i < length w \<Longrightarrow> \<sigma> i < length w"
    using assms(3) unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Two-step: w \\<to> w\_sigma \\<to> w'.\<close>
  define w_\<sigma> where "w_\<sigma> = map (\<lambda>i. w ! (\<sigma> i)) [0..<length w]"
  have hlen_w\<sigma>: "length w_\<sigma> = length w" unfolding w_\<sigma>_def by (by100 simp)
  have hnth_w\<sigma>: "\<And>i. i < length w \<Longrightarrow> w_\<sigma> ! i = w ! (\<sigma> i)"
    unfolding w_\<sigma>_def by (by100 simp)
  \<comment> \<open>Step 1: w \\<to> w\_sigma (reindexing with shifted witnesses).
     Same P, q. Witnesses: vx' = vx\\<circ>\\<sigma>, vy' = vy\\<circ>\\<sigma>.
     All conditions transfer because \\<sigma> is a bijection with the Suc-shift property.\<close>
  \<comment> \<open>Step 1: reindexing w \\<to> w\_sigma.
     The key: both sides of the definition have the SAME structure with 11 conditions.
     We provide witnesses P, q, vx\\<circ>\\<sigma>, vy\\<circ>\\<sigma> and show each condition transfers
     via the bijection \\<sigma>.\<close>
  have h_step1: "top1_quotient_of_scheme_on Y TY w_\<sigma>"
  proof -
    \<comment> \<open>Extract all 11 conditions from the original quotient.\<close>
    from assms(1) obtain P q vx vy where
        hC1: "top1_is_polygonal_region_on P (length w)"
      and hC2: "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
      and hC3: "\<forall>i<length w. \<forall>j<length w. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
      and hC4: "\<forall>i<length w. (vx i, vy i) \<in> P"
      and hC5: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length w. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length w. coeffs i) = 1
                       \<and> x = (\<Sum>i<length w. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length w. coeffs i * vy i)}"
      and hC6: "\<forall>i<length w. \<forall>j<length w.
          i \<noteq> j \<longrightarrow> Suc i mod length w \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length w \<longrightarrow>
          (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
             ((1-s) * vx i + s * vx (Suc i mod length w),
              (1-s) * vy i + s * vy (Suc i mod length w))
           \<noteq> ((1-t) * vx j + t * vx (Suc j mod length w),
               (1-t) * vy j + t * vy (Suc j mod length w)))"
      and hC7: "\<forall>i<length w. \<forall>j<length w. fst (w!i) = fst (w!j) \<longrightarrow>
          (\<forall>t\<in>I_set.
             q ((1-t) * vx i + t * vx (Suc i mod length w),
                (1-t) * vy i + t * vy (Suc i mod length w))
           = (if snd (w!i) = snd (w!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length w),
                      (1-t) * vy j + t * vy (Suc j mod length w))
              else q (t * vx j + (1-t) * vx (Suc j mod length w),
                      t * vy j + (1-t) * vy (Suc j mod length w))))"
      and hC8: "\<forall>p\<in>P. (\<forall>i<length w. \<forall>t\<in>I_set.
                  p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length w),
                        (1-t) * vy i + t * vy (Suc i mod length w)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      and hC9: "\<forall>i<length w. \<forall>j<length w. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length w),
                 (1-t) * vy i + t * vy (Suc i mod length w))
            = q ((1-s) * vx j + s * vx (Suc j mod length w),
                 (1-s) * vy j + s * vy (Suc j mod length w))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (w!i) = fst (w!j) \<and>
                 (if snd (w!i) = snd (w!j) then s = t else s = 1 - t))"
      and hC10: "\<forall>i<length w. let cx = (\<Sum>j<length w. vx j) / real (length w);
                                 cy = (\<Sum>j<length w. vy j) / real (length w)
           in (vx i - cx) * (vy (Suc i mod length w) - cy)
            - (vy i - cy) * (vx (Suc i mod length w) - cx) > 0"
      and hC11: "\<forall>i<length w. \<forall>k<length w.
            k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length w \<longrightarrow>
            (vx k - vx i) * (vy (Suc i mod length w) - vy i)
            - (vy k - vy i) * (vx (Suc i mod length w) - vx i) < 0"
      by (rule quotient_of_scheme_extract_vx)
    \<comment> \<open>Prove shifted versions of C3 and C4.\<close>
    have hC3': "\<forall>i<length w. \<forall>j<length w. i \<noteq> j \<longrightarrow>
        (vx (\<sigma> i), vy (\<sigma> i)) \<noteq> (vx (\<sigma> j), vy (\<sigma> j))"
      using hC3 h\<sigma>_lt h\<sigma>_inj unfolding inj_on_def by (by100 blast)
    have hC4': "\<forall>i<length w. (vx (\<sigma> i), vy (\<sigma> i)) \<in> P"
      using hC4 h\<sigma>_lt by (by100 blast)
    \<comment> \<open>Key helpers for shifted conditions.\<close>
    let ?n = "length w"
    have hSuc_shift: "\<And>i. i < ?n \<Longrightarrow> \<sigma> (Suc i mod ?n) = Suc (\<sigma> i) mod ?n"
      using assms(6) by (by100 simp)
    have hSuc_mod_lt: "\<And>i. i < ?n \<Longrightarrow> Suc i mod ?n < ?n"
    proof -
      fix i assume "i < ?n"
      hence "0 < ?n" by (by100 linarith)
      thus "Suc i mod ?n < ?n" by (rule mod_less_divisor)
    qed
    have h\<sigma>_surj: "\<And>j. j < ?n \<Longrightarrow> \<exists>i<?n. \<sigma> i = j"
    proof -
      fix j assume hj: "j < ?n"
      have "\<sigma> ` {..<?n} = {..<?n}" using assms(3) unfolding bij_betw_def by (by100 blast)
      hence "j \<in> \<sigma> ` {..<?n}" using hj by (by100 blast)
      thus "\<exists>i<?n. \<sigma> i = j" by (by100 blast)
    qed
    \<comment> \<open>Sum reindexing via bijection: \\<Sum>j<n. f(\\<sigma> j) = \\<Sum>j<n. f j.\<close>
    have hsum_reindex: "\<And>g :: nat \<Rightarrow> real. (\<Sum>j<?n. g (\<sigma> j)) = (\<Sum>j<?n. g j)"
      using sum.reindex_bij_betw[OF assms(3)] by (by100 simp)
    \<comment> \<open>Key pattern: each shifted condition uses \\<sigma>(Suc i mod n) in the goal (from the witness
       \\<lambda>i. vx(\\<sigma> i) applied to Suc i mod n). Internally we convert to Suc(\\<sigma> i) mod n
       via hSuc\_shift to match the original condition at position \\<sigma> i.\<close>
    \<comment> \<open>Non-adjacency transfer helper: i \\<noteq> j \\<and> Suc i \\<noteq> j \\<and> i \\<noteq> Suc j implies the same for \\<sigma> i, \\<sigma> j.\<close>
    have h_nonadj: "\<And>i j. \<lbrakk>i < ?n; j < ?n; i \<noteq> j; Suc i mod ?n \<noteq> j; i \<noteq> Suc j mod ?n\<rbrakk> \<Longrightarrow>
        \<sigma> i \<noteq> \<sigma> j \<and> Suc (\<sigma> i) mod ?n \<noteq> \<sigma> j \<and> \<sigma> i \<noteq> Suc (\<sigma> j) mod ?n"
    proof (intro conjI)
      fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
        and hSij: "Suc i mod ?n \<noteq> j" and hijS: "i \<noteq> Suc j mod ?n"
      show "\<sigma> i \<noteq> \<sigma> j"
        using h\<sigma>_inj hi hj hij unfolding inj_on_def by (by100 blast)
      show "Suc (\<sigma> i) mod ?n \<noteq> \<sigma> j"
      proof
        assume "Suc (\<sigma> i) mod ?n = \<sigma> j"
        hence "\<sigma> (Suc i mod ?n) = \<sigma> j" using hSuc_shift[OF hi] by (by100 simp)
        hence "Suc i mod ?n = j"
          using h\<sigma>_inj hSuc_mod_lt[OF hi] hj unfolding inj_on_def by (by100 blast)
        with hSij show False by (by100 simp)
      qed
      show "\<sigma> i \<noteq> Suc (\<sigma> j) mod ?n"
      proof
        assume "\<sigma> i = Suc (\<sigma> j) mod ?n"
        hence "\<sigma> i = \<sigma> (Suc j mod ?n)" using hSuc_shift[OF hj] by (by100 simp)
        hence "i = Suc j mod ?n"
          using h\<sigma>_inj hi hSuc_mod_lt[OF hj] unfolding inj_on_def by (by100 blast)
        with hijS show False by (by100 simp)
      qed
    qed
    \<comment> \<open>Prove shifted C11 in \\<sigma>-composed form (matching the goal after \\<lambda>-witness).\<close>
    have hC11': "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx (\<sigma> k) - vx (\<sigma> i)) * (vy (\<sigma> (Suc i mod ?n)) - vy (\<sigma> i))
          - (vy (\<sigma> k) - vy (\<sigma> i)) * (vx (\<sigma> (Suc i mod ?n)) - vx (\<sigma> i)) < 0"
    proof (intro allI impI)
      fix i k assume hi: "i < ?n" and hk: "k < ?n" and hki: "k \<noteq> i"
        and hksuc: "k \<noteq> Suc i mod ?n"
      have hski: "\<sigma> k \<noteq> \<sigma> i"
        using h\<sigma>_inj hi hk hki unfolding inj_on_def by (by100 blast)
      have hsksuc: "\<sigma> k \<noteq> Suc (\<sigma> i) mod ?n"
      proof
        assume "\<sigma> k = Suc (\<sigma> i) mod ?n"
        hence "\<sigma> k = \<sigma> (Suc i mod ?n)" using hSuc_shift[OF hi] by (by100 simp)
        hence "k = Suc i mod ?n"
          using h\<sigma>_inj hk hSuc_mod_lt[OF hi] unfolding inj_on_def by (by100 blast)
        with hksuc show False by (by100 simp)
      qed
      have "vy (\<sigma> (Suc i mod ?n)) = vy (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      moreover have "vx (\<sigma> (Suc i mod ?n)) = vx (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      ultimately show "(vx (\<sigma> k) - vx (\<sigma> i)) * (vy (\<sigma> (Suc i mod ?n)) - vy (\<sigma> i))
          - (vy (\<sigma> k) - vy (\<sigma> i)) * (vx (\<sigma> (Suc i mod ?n)) - vx (\<sigma> i)) < 0"
        using hC11[rule_format, OF h\<sigma>_lt[OF hi] h\<sigma>_lt[OF hk] hski hsksuc] by (by100 simp)
    qed
    \<comment> \<open>Prove shifted C6 in \\<sigma>-composed form.\<close>
    have hC6': "\<forall>i<?n. \<forall>j<?n.
        i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
        (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
           ((1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n)),
            (1-s) * vy (\<sigma> i) + s * vy (\<sigma> (Suc i mod ?n)))
         \<noteq> ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
             (1-t) * vy (\<sigma> j) + t * vy (\<sigma> (Suc j mod ?n))))"
    proof (intro allI impI ballI)
      fix i j and s t :: real
      assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
        and hSij: "Suc i mod ?n \<noteq> j" and hijS: "i \<noteq> Suc j mod ?n"
        and hs: "s \<in> {0<..<1::real}" and ht: "t \<in> {0<..<1::real}"
      from h_nonadj[OF hi hj hij hSij hijS]
      obtain hsij: "\<sigma> i \<noteq> \<sigma> j" and hsSij: "Suc (\<sigma> i) mod ?n \<noteq> \<sigma> j"
        and hsijS: "\<sigma> i \<noteq> Suc (\<sigma> j) mod ?n" by (by100 blast)
      have hri: "vx (\<sigma> (Suc i mod ?n)) = vx (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      have hrj: "vx (\<sigma> (Suc j mod ?n)) = vx (Suc (\<sigma> j) mod ?n)"
        using hSuc_shift[OF hj] by (by100 simp)
      have hri2: "vy (\<sigma> (Suc i mod ?n)) = vy (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      have hrj2: "vy (\<sigma> (Suc j mod ?n)) = vy (Suc (\<sigma> j) mod ?n)"
        using hSuc_shift[OF hj] by (by100 simp)
      show "((1-s) * vx (\<sigma> i) + s * vx (\<sigma> (Suc i mod ?n)),
             (1-s) * vy (\<sigma> i) + s * vy (\<sigma> (Suc i mod ?n)))
          \<noteq> ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
              (1-t) * vy (\<sigma> j) + t * vy (\<sigma> (Suc j mod ?n)))"
        using hC6[rule_format, OF h\<sigma>_lt[OF hi] h\<sigma>_lt[OF hj] hsij hsSij hsijS hs ht]
              hri hrj hri2 hrj2 by (by100 simp)
    qed
    \<comment> \<open>Prove shifted C8 in \\<sigma>-composed form.\<close>
    have hC8': "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
                  p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                        (1-t) * vy (\<sigma> i) + t * vy (\<sigma> (Suc i mod ?n))))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    proof (intro ballI impI allI)
      fix p p' assume hp: "p \<in> P" and hp': "p' \<in> P" and hq: "q p = q p'"
        and hne: "\<forall>i<?n. \<forall>t\<in>I_set.
                  p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                        (1-t) * vy (\<sigma> i) + t * vy (\<sigma> (Suc i mod ?n)))"
      have hne_orig: "\<forall>j<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))"
      proof (intro allI impI ballI)
        fix j t assume hj: "j < ?n" and ht: "t \<in> I_set"
        from h\<sigma>_surj[OF hj] obtain i where hi: "i < ?n" and hsij: "\<sigma> i = j" by (by100 blast)
        have "p \<noteq> ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                    (1-t) * vy (\<sigma> i) + t * vy (\<sigma> (Suc i mod ?n)))"
          using hne[rule_format, OF hi ht] .
        moreover have "\<sigma> (Suc i mod ?n) = Suc j mod ?n"
          using hSuc_shift[OF hi] hsij by (by100 simp)
        ultimately show "p \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))"
          using hsij by (by100 simp)
      qed
      show "p = p'" using hC8[rule_format, OF hp] hne_orig hp' hq by (by100 blast)
    qed
    \<comment> \<open>Prove shifted C10 in \\<sigma>-composed form.\<close>
    have hC10': "\<forall>i<?n. let cx = (\<Sum>j<?n. vx (\<sigma> j)) / real ?n;
                             cy = (\<Sum>j<?n. vy (\<sigma> j)) / real ?n
         in (vx (\<sigma> i) - cx) * (vy (\<sigma> (Suc i mod ?n)) - cy)
          - (vy (\<sigma> i) - cy) * (vx (\<sigma> (Suc i mod ?n)) - cx) > 0"
    proof (intro allI impI)
      fix i assume hi: "i < ?n"
      have hcx: "(\<Sum>j<?n. vx (\<sigma> j)) = (\<Sum>j<?n. vx j)" using hsum_reindex by (by100 blast)
      have hcy: "(\<Sum>j<?n. vy (\<sigma> j)) = (\<Sum>j<?n. vy j)" using hsum_reindex by (by100 blast)
      have hri: "vx (\<sigma> (Suc i mod ?n)) = vx (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      have hri2: "vy (\<sigma> (Suc i mod ?n)) = vy (Suc (\<sigma> i) mod ?n)"
        using hSuc_shift[OF hi] by (by100 simp)
      show "let cx = (\<Sum>j<?n. vx (\<sigma> j)) / real ?n;
                cy = (\<Sum>j<?n. vy (\<sigma> j)) / real ?n
           in (vx (\<sigma> i) - cx) * (vy (\<sigma> (Suc i mod ?n)) - cy)
            - (vy (\<sigma> i) - cy) * (vx (\<sigma> (Suc i mod ?n)) - cx) > 0"
        using hC10[rule_format, OF h\<sigma>_lt[OF hi]] hcx hcy hri hri2 by (by100 simp)
    qed
    \<comment> \<open>Build the goal from shifted witnesses.\<close>
    show ?thesis
      unfolding top1_quotient_of_scheme_on_def hlen_w\<sigma>
      apply (intro conjI)
      apply (rule htopo)
      apply (rule exI[of _ P])
      apply (rule exI[of _ q])
      apply (rule exI[of _ "\<lambda>i. vx (\<sigma> i)"])
      apply (rule exI[of _ "\<lambda>i. vy (\<sigma> i)"])
      apply (intro conjI)
      subgoal using hC1 by assumption \<comment> \<open>C1: polygonal region\<close>
      subgoal using hC2 by assumption \<comment> \<open>C2: quotient map\<close>
      subgoal using hC3' by assumption \<comment> \<open>C3: shifted vertices distinct\<close>
      subgoal using hC4' by assumption \<comment> \<open>C4: shifted vertices in P\<close>
      subgoal \<comment> \<open>C5: convex hull — reindexing coefficients via bij.\<close>
      proof -
        \<comment> \<open>Key: for any coeffs, \\<Sum>coeffs i * vx(\\<sigma> i) = \\<Sum>(coeffs\\<circ>\\<sigma>) i * vx(\\<sigma> i)
           which by reindexing = \\<Sum>j. (coeffs\\<circ>\\<sigma>)(\\<sigma>\\<inverse> j) * vx j = \\<Sum>j. coeffs j * vx j.
           So we transform coefficients: coeffs \\<mapsto> coeffs\\<circ>\\<sigma> gives \\<supseteq>, coeffs\\<circ>\\<sigma>\\<inverse> gives \\<subseteq>.\<close>
        \<comment> \<open>Direction 1 (original \\<to> shifted): given coeffs for vx, use coeffs\\<circ>\\<sigma> for vx\\<circ>\\<sigma>.\<close>
        have hdir1: "\<And>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<Longrightarrow> (\<Sum>i<?n. coeffs i) = 1 \<Longrightarrow>
          \<exists>coeffs'. (\<forall>i<?n. 0 \<le> coeffs' i) \<and> (\<Sum>i<?n. coeffs' i) = 1
            \<and> (\<Sum>i<?n. coeffs' i * vx (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vx i)
            \<and> (\<Sum>i<?n. coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vy i)"
        proof -
          fix coeffs :: "nat \<Rightarrow> real"
          assume hnn: "\<forall>i<?n. 0 \<le> coeffs i" and hsum: "(\<Sum>i<?n. coeffs i) = 1"
          let ?coeffs' = "coeffs \<circ> \<sigma>"
          have hnn': "\<forall>i<?n. 0 \<le> ?coeffs' i" using hnn h\<sigma>_lt by (by100 fastforce)
          have hsum': "(\<Sum>i<?n. ?coeffs' i) = 1"
            using hsum_reindex[of "coeffs"] hsum by (by100 simp)
          have "(\<Sum>i<?n. ?coeffs' i * vx (\<sigma> i)) = (\<Sum>i<?n. coeffs (\<sigma> i) * vx (\<sigma> i))"
            by (by100 simp)
          also have "\<dots> = (\<Sum>j<?n. coeffs j * vx j)"
            using sum.reindex_bij_betw[OF assms(3), of "\<lambda>j. coeffs j * vx j"] by (by100 simp)
          finally have hvx: "(\<Sum>i<?n. ?coeffs' i * vx (\<sigma> i)) = (\<Sum>j<?n. coeffs j * vx j)" .
          have "(\<Sum>i<?n. ?coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs (\<sigma> i) * vy (\<sigma> i))"
            by (by100 simp)
          also have "\<dots> = (\<Sum>j<?n. coeffs j * vy j)"
            using sum.reindex_bij_betw[OF assms(3), of "\<lambda>j. coeffs j * vy j"] by (by100 simp)
          finally have hvy: "(\<Sum>i<?n. ?coeffs' i * vy (\<sigma> i)) = (\<Sum>j<?n. coeffs j * vy j)" .
          show "\<exists>coeffs'. (\<forall>i<?n. 0 \<le> coeffs' i) \<and> (\<Sum>i<?n. coeffs' i) = 1
            \<and> (\<Sum>i<?n. coeffs' i * vx (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vx i)
            \<and> (\<Sum>i<?n. coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vy i)"
            using hnn' hsum' hvx hvy by (by100 blast)
        qed
        \<comment> \<open>Direction 2 (shifted \\<to> original): given coeffs' for vx\\<circ>\\<sigma>, reindex via \\<sigma>.
           Key: \\<Sum>coeffs'(inv(\\<sigma>) i) * vx i = \\<Sum>coeffs' j * vx(\\<sigma> j) by reindexing with \\<sigma>.\<close>
        have h_inv_lt: "\<And>i. i < ?n \<Longrightarrow> inv_into {..<?n} \<sigma> i < ?n"
          using bij_betw_inv_into[OF assms(3)] unfolding bij_betw_def by (by100 blast)
        have h_inv_\<sigma>: "\<And>j. j < ?n \<Longrightarrow> inv_into {..<?n} \<sigma> (\<sigma> j) = j"
          using inv_into_f_f[OF h\<sigma>_inj] by (by100 simp)
        have hdir2: "\<And>coeffs'. (\<forall>i<?n. 0 \<le> coeffs' i) \<Longrightarrow> (\<Sum>i<?n. coeffs' i) = 1 \<Longrightarrow>
          \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> (\<Sum>i<?n. coeffs i * vx i) = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))
            \<and> (\<Sum>i<?n. coeffs i * vy i) = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
        proof -
          fix coeffs' :: "nat \<Rightarrow> real"
          assume hnn: "\<forall>i<?n. 0 \<le> coeffs' i" and hsum: "(\<Sum>i<?n. coeffs' i) = 1"
          let ?coeffs = "coeffs' \<circ> (inv_into {..<?n} \<sigma>)"
          have hnn': "\<forall>i<?n. 0 \<le> ?coeffs i"
            using hnn h_inv_lt by (by100 fastforce)
          have hsum': "(\<Sum>i<?n. ?coeffs i) = 1"
          proof -
            have "(\<Sum>i<?n. ?coeffs i) = (\<Sum>j<?n. coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)))"
              using sum.reindex_bij_betw[OF assms(3), of "\<lambda>i. coeffs' (inv_into {..<?n} \<sigma> i)"]
              by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs' j)"
            proof (rule sum.cong)
              fix j assume "j \<in> {..<?n}" thus "coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)) = coeffs' j"
                using h_inv_\<sigma> by (by100 simp)
            qed (by100 simp)
            finally show ?thesis using hsum by (by100 simp)
          qed
          have hvx: "(\<Sum>i<?n. ?coeffs i * vx i) = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))"
          proof -
            have "(\<Sum>i<?n. ?coeffs i * vx i)
                = (\<Sum>j<?n. coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)) * vx (\<sigma> j))"
              using sum.reindex_bij_betw[OF assms(3),
                of "\<lambda>i. coeffs' (inv_into {..<?n} \<sigma> i) * vx i"] by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs' j * vx (\<sigma> j))"
            proof (rule sum.cong)
              fix j assume "j \<in> {..<?n}"
              thus "coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)) * vx (\<sigma> j) = coeffs' j * vx (\<sigma> j)"
                using h_inv_\<sigma> by (by100 simp)
            qed (by100 simp)
            finally show ?thesis .
          qed
          have hvy: "(\<Sum>i<?n. ?coeffs i * vy i) = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
          proof -
            have "(\<Sum>i<?n. ?coeffs i * vy i)
                = (\<Sum>j<?n. coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)) * vy (\<sigma> j))"
              using sum.reindex_bij_betw[OF assms(3),
                of "\<lambda>i. coeffs' (inv_into {..<?n} \<sigma> i) * vy i"] by (by100 simp)
            also have "\<dots> = (\<Sum>j<?n. coeffs' j * vy (\<sigma> j))"
            proof (rule sum.cong)
              fix j assume "j \<in> {..<?n}"
              thus "coeffs' (inv_into {..<?n} \<sigma> (\<sigma> j)) * vy (\<sigma> j) = coeffs' j * vy (\<sigma> j)"
                using h_inv_\<sigma> by (by100 simp)
            qed (by100 simp)
            finally show ?thesis .
          qed
          show "\<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> (\<Sum>i<?n. coeffs i * vx i) = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))
            \<and> (\<Sum>i<?n. coeffs i * vy i) = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
            using hnn' hsum' hvx hvy by (by100 blast)
        qed
        \<comment> \<open>Combine both directions to show set equality.\<close>
        show ?thesis
        proof (rule set_eqI)
          fix p :: "real \<times> real"
          obtain x y where hxy: "p = (x, y)" by (cases p)
          show "(p \<in> P) = (p \<in> {(x, y) |x y.
                \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1 \<and>
                   x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))})"
          proof
            assume "p \<in> P"
            hence "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                       \<and> x = (\<Sum>i<?n. coeffs i * vx i) \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
              using hC5 by (by100 blast)
            then obtain coeffs where hcoeffs:
              "(\<forall>i<?n. 0 \<le> coeffs i)" "(\<Sum>i<?n. coeffs i) = 1"
              "x = (\<Sum>i<?n. coeffs i * vx i)" "y = (\<Sum>i<?n. coeffs i * vy i)"
              using hxy by (by100 blast)
            from hdir1[OF hcoeffs(1) hcoeffs(2)] obtain coeffs' where hcoeffs':
              "(\<forall>i<?n. 0 \<le> coeffs' i)" "(\<Sum>i<?n. coeffs' i) = 1"
              "(\<Sum>i<?n. coeffs' i * vx (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vx i)"
              "(\<Sum>i<?n. coeffs' i * vy (\<sigma> i)) = (\<Sum>i<?n. coeffs i * vy i)"
              by (by100 blast)
            have hx': "x = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))"
              using hcoeffs(3) hcoeffs'(3) by (by100 simp)
            have hy': "y = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
              using hcoeffs(4) hcoeffs'(4) by (by100 simp)
            show "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))}"
              using hxy hcoeffs'(1,2) hx' hy' by (by100 blast)
          next
            assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
                \<and> x = (\<Sum>i<?n. coeffs i * vx (\<sigma> i)) \<and> y = (\<Sum>i<?n. coeffs i * vy (\<sigma> i))}"
            then obtain coeffs' where hcoeffs':
              "(\<forall>i<?n. 0 \<le> coeffs' i)" "(\<Sum>i<?n. coeffs' i) = 1"
              "x = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))" "y = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
              using hxy by (by100 blast)
            from hdir2[OF hcoeffs'(1) hcoeffs'(2)] obtain coeffs where hcoeffs:
              "(\<forall>i<?n. 0 \<le> coeffs i)" "(\<Sum>i<?n. coeffs i) = 1"
              "(\<Sum>i<?n. coeffs i * vx i) = (\<Sum>i<?n. coeffs' i * vx (\<sigma> i))"
              "(\<Sum>i<?n. coeffs i * vy i) = (\<Sum>i<?n. coeffs' i * vy (\<sigma> i))"
              by (by100 blast)
            have hx: "x = (\<Sum>i<?n. coeffs i * vx i)"
              using hcoeffs(3) hcoeffs'(3) by (by100 simp)
            have hy: "y = (\<Sum>i<?n. coeffs i * vy i)"
              using hcoeffs(4) hcoeffs'(4) by (by100 simp)
            show "p \<in> P" using hC5 hxy hcoeffs(1,2) hx hy by (by100 blast)
          qed
        qed
      qed
      subgoal using hC6' by assumption \<comment> \<open>C6: non-adjacent edges\<close>
      subgoal \<comment> \<open>C7: identification\<close>
      proof (intro allI impI ballI)
        fix i j t
        assume hi: "i < ?n" and hj: "j < ?n" and ht: "t \<in> I_set"
          and hfst: "fst (w_\<sigma> ! i) = fst (w_\<sigma> ! j)"
        have hfst_w: "fst (w ! (\<sigma> i)) = fst (w ! (\<sigma> j))"
          using hfst hnth_w\<sigma>[OF hi] hnth_w\<sigma>[OF hj] by (by100 simp)
        have hSuc_i: "\<sigma> (Suc i mod ?n) = Suc (\<sigma> i) mod ?n" using hSuc_shift[OF hi] .
        have hSuc_j: "\<sigma> (Suc j mod ?n) = Suc (\<sigma> j) mod ?n" using hSuc_shift[OF hj] .
        have hsnd_eq: "(snd (w_\<sigma> ! i) = snd (w_\<sigma> ! j)) = (snd (w ! (\<sigma> i)) = snd (w ! (\<sigma> j)))"
          using hnth_w\<sigma>[OF hi] hnth_w\<sigma>[OF hj] by (by100 simp)
        have hfact: "q ((1-t) * vx (\<sigma> i) + t * vx (Suc (\<sigma> i) mod ?n),
                        (1-t) * vy (\<sigma> i) + t * vy (Suc (\<sigma> i) mod ?n))
             = (if snd (w ! (\<sigma> i)) = snd (w ! (\<sigma> j))
                then q ((1-t) * vx (\<sigma> j) + t * vx (Suc (\<sigma> j) mod ?n),
                        (1-t) * vy (\<sigma> j) + t * vy (Suc (\<sigma> j) mod ?n))
                else q (t * vx (\<sigma> j) + (1-t) * vx (Suc (\<sigma> j) mod ?n),
                        t * vy (\<sigma> j) + (1-t) * vy (Suc (\<sigma> j) mod ?n)))"
          using hC7[rule_format, OF h\<sigma>_lt[OF hi] h\<sigma>_lt[OF hj] hfst_w ht] .
        show "q ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                  (1-t) * vy (\<sigma> i) + t * vy (\<sigma> (Suc i mod ?n)))
             = (if snd (w_\<sigma> ! i) = snd (w_\<sigma> ! j)
                then q ((1-t) * vx (\<sigma> j) + t * vx (\<sigma> (Suc j mod ?n)),
                        (1-t) * vy (\<sigma> j) + t * vy (\<sigma> (Suc j mod ?n)))
                else q (t * vx (\<sigma> j) + (1-t) * vx (\<sigma> (Suc j mod ?n)),
                        t * vy (\<sigma> j) + (1-t) * vy (\<sigma> (Suc j mod ?n))))"
          using hfact hSuc_i hSuc_j hsnd_eq by (by100 simp)
      qed
      subgoal using hC8' by assumption \<comment> \<open>C8: interior injectivity\<close>
      subgoal \<comment> \<open>C9: boundary injectivity\<close>
      proof (intro allI impI ballI)
        fix i j t s
        assume hi: "i < ?n" and hj: "j < ?n" and ht: "t \<in> I_set" and hs: "s \<in> I_set"
          and hq: "q ((1-t) * vx (\<sigma> i) + t * vx (\<sigma> (Suc i mod ?n)),
                      (1-t) * vy (\<sigma> i) + t * vy (\<sigma> (Suc i mod ?n)))
                 = q ((1-s) * vx (\<sigma> j) + s * vx (\<sigma> (Suc j mod ?n)),
                      (1-s) * vy (\<sigma> j) + s * vy (\<sigma> (Suc j mod ?n)))"
        have hSuc_i: "\<sigma> (Suc i mod ?n) = Suc (\<sigma> i) mod ?n" using hSuc_shift[OF hi] .
        have hSuc_j: "\<sigma> (Suc j mod ?n) = Suc (\<sigma> j) mod ?n" using hSuc_shift[OF hj] .
        have hq_orig: "q ((1-t) * vx (\<sigma> i) + t * vx (Suc (\<sigma> i) mod ?n),
                          (1-t) * vy (\<sigma> i) + t * vy (Suc (\<sigma> i) mod ?n))
                     = q ((1-s) * vx (\<sigma> j) + s * vx (Suc (\<sigma> j) mod ?n),
                          (1-s) * vy (\<sigma> j) + s * vy (Suc (\<sigma> j) mod ?n))"
          using hq hSuc_i hSuc_j by (by100 simp)
        have hfact: "((\<sigma> i) = (\<sigma> j) \<and> t = s)
          \<or> (fst (w ! (\<sigma> i)) = fst (w ! (\<sigma> j)) \<and>
             (if snd (w ! (\<sigma> i)) = snd (w ! (\<sigma> j)) then s = t else s = 1 - t))"
          using hC9[rule_format, OF h\<sigma>_lt[OF hi] h\<sigma>_lt[OF hj] ht hs hq_orig] .
        show "(i = j \<and> t = s)
          \<or> (fst (w_\<sigma> ! i) = fst (w_\<sigma> ! j) \<and>
             (if snd (w_\<sigma> ! i) = snd (w_\<sigma> ! j) then s = t else s = 1 - t))"
        proof (cases "\<sigma> i = \<sigma> j")
          case True
          hence "i = j" using h\<sigma>_inj hi hj unfolding inj_on_def by (by100 blast)
          with hfact True show ?thesis
            using hnth_w\<sigma>[OF hi] hnth_w\<sigma>[OF hj] by (by100 simp)
        next
          case False
          with hfact have "fst (w ! (\<sigma> i)) = fst (w ! (\<sigma> j)) \<and>
             (if snd (w ! (\<sigma> i)) = snd (w ! (\<sigma> j)) then s = t else s = 1 - t)"
            by (by100 blast)
          thus ?thesis using hnth_w\<sigma>[OF hi] hnth_w\<sigma>[OF hj] by (by100 simp)
        qed
      qed
      subgoal using hC10' by assumption \<comment> \<open>C10: counterclockwise\<close>
      subgoal using hC11' by assumption \<comment> \<open>C11: strict edge-side\<close>
      done
  qed
  \<comment> \<open>Step 2: w\_sigma \\<to> w' via original transfer (fst/snd match at each position).\<close>
  have hfst_ws: "\<And>i. i < length w_\<sigma> \<Longrightarrow> fst (w'!i) = fst (w_\<sigma>!i)"
  proof -
    fix i assume "i < length w_\<sigma>"
    hence hi: "i < length w" using hlen_w\<sigma> by (by100 simp)
    have "fst (w'!i) = fst (w!(\<sigma> i))" using assms(4)[OF hi] .
    also have "\<dots> = fst (w_\<sigma>!i)" using hnth_w\<sigma>[OF hi] by (by100 simp)
    finally show "fst (w'!i) = fst (w_\<sigma>!i)" .
  qed
  have hsnd_ws: "\<And>i j. \<lbrakk>i < length w_\<sigma>; j < length w_\<sigma>; fst (w_\<sigma>!i) = fst (w_\<sigma>!j)\<rbrakk> \<Longrightarrow>
      (snd (w'!i) = snd (w'!j)) = (snd (w_\<sigma>!i) = snd (w_\<sigma>!j))"
  proof -
    fix i j assume hi: "i < length w_\<sigma>" and hj: "j < length w_\<sigma>"
    have hi': "i < length w" using hi hlen_w\<sigma> by (by100 simp)
    have hj': "j < length w" using hj hlen_w\<sigma> by (by100 simp)
    show "(snd (w'!i) = snd (w'!j)) = (snd (w_\<sigma>!i) = snd (w_\<sigma>!j))"
      using assms(5)[OF hi'] assms(5)[OF hj'] hnth_w\<sigma>[OF hi'] hnth_w\<sigma>[OF hj'] by (by100 metis)
  qed
  show ?thesis
    by (rule quotient_of_scheme_transfer[OF h_step1 _ hfst_ws hsnd_ws]) (simp add: assms(2) hlen_w\<sigma>)
qed

\<comment> \<open>Edge preservation for composed disk homeomorphisms: if \\<psi>1 and \\<psi>2 both map
   edge i at parameter t to the same S¹ point, then inv(\\<psi>2) \\<circ> \\<psi>1 maps edge i of P1
   to edge i of P2. This is the core argument for scheme\\_quotient\\_uniqueness.\<close>
lemma composed_disk_homeo_edge_preserving:
  fixes \<psi>1 \<psi>2 :: "'a \<Rightarrow> 'b" and P2 :: "'a set"
  assumes h\<psi>2_inj: "inj_on \<psi>2 P2"
      and h_eq: "\<psi>1 p1 = \<psi>2 p2"
      and h_in: "p2 \<in> P2"
  shows "(inv_into P2 \<psi>2 \<circ> \<psi>1) p1 = p2"
  using assms inv_into_f_f[OF h\<psi>2_inj h_in] unfolding comp_def
  by (by100 simp)

\<comment> \<open>Helper: split a sum over {..<n} at two distinct positions i,j.\<close>
lemma sum_split_two:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "i < n" "j < n" "i \<noteq> j"
  shows "(\<Sum>k<n. f k) = f i + f j + (\<Sum>k\<in>{..<n}-{i}-{j}. f k)"
proof -
  have "i \<in> {..<n}" "j \<in> {..<n}" using assms by (by100 simp)+
  have h1: "(\<Sum>k<n. f k) = f i + (\<Sum>k\<in>{..<n}-{i}. f k)"
    using sum.remove[OF _ \<open>i \<in> {..<n}\<close>, of f] by (by100 simp)
  have hji: "j \<in> {..<n}-{i}" using \<open>j \<in> {..<n}\<close> assms(3) by (by100 blast)
  have hfin2: "finite ({..<n}-{i})" by (by100 simp)
  have h2: "(\<Sum>k\<in>{..<n}-{i}. f k) = f j + (\<Sum>k\<in>({..<n}-{i})-{j}. f k)"
    using sum.remove[OF hfin2 hji] .
  have "({..<n}-{i})-{j} = {..<n}-{i}-{j}" by (by100 blast)
  hence h2': "(\<Sum>k\<in>{..<n}-{i}. f k) = f j + (\<Sum>k\<in>{..<n}-{i}-{j}. f k)"
    using h2 by (by100 simp)
  from h1 h2' have "(\<Sum>k<n. f k) = f i + (f j + (\<Sum>k\<in>{..<n}-{i}-{j}. f k))" by (by100 simp)
  thus ?thesis using add.assoc[of "f i" "f j"] by (by100 simp)
qed

\<comment> \<open>Edge point is in the polygon: the convex combination (1-t)*v\\_i + t*v\\_{i+1} is in P
   when P is the convex hull of the vertices. Witness: coeffs(i) = 1-t, coeffs(Suc i mod n) = t,
   rest 0. Uses n \\<ge> 3 to ensure i \\<noteq> Suc i mod n.\<close>
lemma edge_point_in_polygon_witness:
  assumes "n \<ge> 3" and "i < n" and "t \<in> I_set"
      and hP: "P = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  shows "((1-t) * vx i + t * vx (Suc i mod n),
          (1-t) * vy i + t * vy (Suc i mod n)) \<in> P"
proof -
  let ?si = "Suc i mod n"
  have hsi: "?si < n" using assms(1) by (by100 simp)
  have hne: "i \<noteq> ?si"
  proof (cases "Suc i < n")
    case True thus ?thesis by (by100 simp)
  next
    case False hence "Suc i = n" using assms(2) by (by100 simp)
    hence "?si = 0" by (by100 simp)
    moreover have "i > 0" using \<open>Suc i = n\<close> assms(1) by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  define coeffs :: "nat \<Rightarrow> real" where
    "coeffs = (\<lambda>k. if k = i then 1 - t else if k = ?si then t else 0)"
  have hnn: "\<forall>j<n. coeffs j \<ge> 0"
  proof (intro allI impI)
    fix j assume "j < n"
    show "coeffs j \<ge> 0" unfolding coeffs_def
      using assms(3) unfolding top1_unit_interval_def by (by100 auto)
  qed
  have hsum: "(\<Sum>j<n. coeffs j) = 1"
  proof -
    have "(\<Sum>j<n. coeffs j) = coeffs i + coeffs ?si + (\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j)"
      by (rule sum_split_two[OF assms(2) hsi hne])
    also have "coeffs i = 1 - t" unfolding coeffs_def by (by100 simp)
    also have "coeffs ?si = t" unfolding coeffs_def using hne by (by100 simp)
    also have "(\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j) = 0"
      unfolding coeffs_def using hne by (by100 auto)
    finally show ?thesis by (by100 simp)
  qed
  have hx: "(1-t) * vx i + t * vx ?si = (\<Sum>j<n. coeffs j * vx j)"
  proof -
    have "(\<Sum>j<n. coeffs j * vx j) = coeffs i * vx i + coeffs ?si * vx ?si
        + (\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j * vx j)"
      by (rule sum_split_two[OF assms(2) hsi hne])
    also have "coeffs i * vx i = (1-t) * vx i" unfolding coeffs_def by (by100 simp)
    also have "coeffs ?si * vx ?si = t * vx ?si" unfolding coeffs_def using hne by (by100 simp)
    also have "(\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j * vx j) = 0"
      unfolding coeffs_def using hne by (by100 auto)
    finally show ?thesis by (by100 simp)
  qed
  have hy: "(1-t) * vy i + t * vy ?si = (\<Sum>j<n. coeffs j * vy j)"
  proof -
    have "(\<Sum>j<n. coeffs j * vy j) = coeffs i * vy i + coeffs ?si * vy ?si
        + (\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j * vy j)"
      by (rule sum_split_two[OF assms(2) hsi hne])
    also have "coeffs i * vy i = (1-t) * vy i" unfolding coeffs_def by (by100 simp)
    also have "coeffs ?si * vy ?si = t * vy ?si" unfolding coeffs_def using hne by (by100 simp)
    also have "(\<Sum>j\<in>{..<n}-{i}-{?si}. coeffs j * vy j) = 0"
      unfolding coeffs_def using hne by (by100 auto)
    finally show ?thesis by (by100 simp)
  qed
  show ?thesis unfolding hP using hnn hsum hx hy by (by100 blast)
qed

\<comment> \<open>NOTE: transfer\\_bij approach FAILS for cut\\_paste\\_opp because the permutation \\<sigma>
   does NOT preserve edge adjacency (Suc(\\<sigma>(i)) mod n \\<noteq> \\<sigma>(Suc(i) mod n) at region
   boundaries, e.g. i=a0-1 gives Suc(a0-1)=a0 but \\<sigma>(a0)=a0+b \\<noteq> a0=Suc(\\<sigma>(a0-1))).
   Correct approach requires constructing new polygon witnesses with rearranged boundary,
   or following the expert audit's recommendation to use homeomorphism instead of same-space.\<close>

\<comment> \<open>Rotate transfer: quotient\_of\_scheme\_on is preserved by rotation (cyclic shift).
   Same polygon P. Shifted vertices: vx'(i) = vx((i+k) mod n).
   The convex hull is invariant. Edge identification shifts consistently.\<close>
lemma quotient_of_scheme_rotate:
  assumes "top1_quotient_of_scheme_on Y TY (u @ v)"
  shows "top1_quotient_of_scheme_on Y TY (v @ u)"
proof -
  let ?n = "length u + length v"
  let ?k = "length u"
  have hlen: "length (v @ u) = length (u @ v)" by (by100 simp)
  \<comment> \<open>Key shift property.\<close>
  have hshift: "\<And>i. i < ?n \<Longrightarrow> (v @ u) ! i = (u @ v) ! ((i + ?k) mod ?n)"
  proof -
    fix i assume hi: "i < ?n"
    show "(v @ u) ! i = (u @ v) ! ((i + ?k) mod ?n)"
    proof (cases "i < length v")
      case True
      hence "(v @ u) ! i = v ! i" using nth_append[of v u i] by (by100 simp)
      moreover have "(i + ?k) mod ?n = i + ?k"
        using True by (by100 simp)
      moreover have "(u @ v) ! (i + ?k) = v ! i"
        using True nth_append[of u v "i + ?k"] by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    next
      case False
      hence hge: "i \<ge> length v" by (by100 linarith)
      hence "(v @ u) ! i = u ! (i - length v)" using nth_append[of v u i] by (by100 simp)
      moreover have "(i + ?k) mod ?n = i - length v"
      proof -
        have "i + ?k = ?n + (i - length v)" using hge by (by100 linarith)
        hence "(i + ?k) mod ?n = (?n + (i - length v)) mod ?n" by (by100 metis)
        also have "\<dots> = (i - length v) mod ?n" by (by100 simp)
        also have "\<dots> = i - length v" using hi hge by (by100 simp)
        finally show ?thesis .
      qed
      moreover have "(u @ v) ! (i - length v) = u ! (i - length v)"
      proof -
        have "i - length v < length u" using hi hge by (by100 linarith)
        thus ?thesis using nth_append[of u v "i - length v"] by (by100 simp)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>Apply the generalized bij transfer with sigma(i) = (i + length u) mod n.\<close>
  have hn_pos: "(0::nat) < ?n"
  proof -
    from assms obtain P0 q0 where "top1_is_polygonal_region_on P0 (length (u @ v))"
      by (rule quotient_of_scheme_extract)
    hence h3: "length (u @ v) \<ge> 3" unfolding top1_is_polygonal_region_on_def by (by100 blast)
    have "length (u @ v) = length u + length v" by (by100 simp)
    with h3 show ?thesis by (by100 linarith)
  qed
  define \<sigma> where "\<sigma> = (\<lambda>i. (i + ?k) mod ?n)"
  have hbij: "bij_betw \<sigma> {..<?n} {..<?n}"
  proof -
    have hinj: "inj_on \<sigma> {..<?n}"
    proof (rule inj_onI)
      fix x y assume "x \<in> {..<?n}" "y \<in> {..<?n}" "\<sigma> x = \<sigma> y"
      from this have "x < ?n" "y < ?n" "(x + ?k) mod ?n = (y + ?k) mod ?n" unfolding \<sigma>_def by (by100 simp)+
      thus "x = y" using shift_mod_inj[OF hn_pos] by (by100 metis)
    qed
    have himg: "\<sigma> ` {..<?n} \<subseteq> {..<?n}"
    proof
      fix y assume "y \<in> \<sigma> ` {..<?n}"
      then obtain x where "x < ?n" "y = \<sigma> x" by (by100 blast)
      hence "y = (x + ?k) mod ?n" unfolding \<sigma>_def by (by100 simp)
      moreover have "(x + ?k) mod ?n < ?n" by (rule mod_less_n[OF hn_pos])
      ultimately have "y < ?n" by (by100 simp)
      thus "y \<in> {..<?n}" by (by100 simp)
    qed
    have hcard: "card (\<sigma> ` {..<?n}) = card {..<?n}"
      using card_image[OF hinj] by (by100 simp)
    have "\<sigma> ` {..<?n} = {..<?n}"
      using card_subset_eq[OF finite_lessThan himg hcard] by (by100 blast)
    thus ?thesis unfolding bij_betw_def using hinj by (by100 blast)
  qed
  have hfst_bij: "\<And>i. i < ?n \<Longrightarrow> fst ((v @ u)!i) = fst ((u @ v)!(\<sigma> i))"
  proof -
    fix i assume "i < ?n"
    from hshift[OF this] have "(v @ u) ! i = (u @ v) ! ((i + ?k) mod ?n)" .
    thus "fst ((v @ u)!i) = fst ((u @ v)!(\<sigma> i))" unfolding \<sigma>_def by (by100 simp)
  qed
  have hsnd_bij: "\<And>i. i < ?n \<Longrightarrow> snd ((v @ u)!i) = snd ((u @ v)!(\<sigma> i))"
  proof -
    fix i assume "i < ?n"
    from hshift[OF this] have "(v @ u) ! i = (u @ v) ! ((i + ?k) mod ?n)" .
    thus "snd ((v @ u)!i) = snd ((u @ v)!(\<sigma> i))" unfolding \<sigma>_def by (by100 simp)
  qed
  have hsuc_bij: "\<And>i. i < ?n \<Longrightarrow> Suc (\<sigma> i) mod ?n = \<sigma> (Suc i mod ?n)"
  proof -
    fix i assume "i < ?n"
    have "Suc (\<sigma> i) mod ?n = Suc ((i + ?k) mod ?n) mod ?n" unfolding \<sigma>_def by (by100 simp)
    also have "\<dots> = (Suc i + ?k) mod ?n" using suc_mod_shift[OF hn_pos] .
    also have "\<dots> = (Suc i mod ?n + ?k) mod ?n" by (rule mod_add_left)
    also have "\<dots> = \<sigma> (Suc i mod ?n)" unfolding \<sigma>_def by (by100 simp)
    finally show "Suc (\<sigma> i) mod ?n = \<sigma> (Suc i mod ?n)" .
  qed
  \<comment> \<open>Need length (u@v) = length u + length v for unification.\<close>
  have hlen_uv: "length (u @ v) = ?n" by (by100 simp)
  have hbij': "bij_betw \<sigma> {..<length (u @ v)} {..<length (u @ v)}"
    using hbij hlen_uv by (by100 simp)
  have hfst_bij': "\<And>i. i < length (u @ v) \<Longrightarrow> fst ((v @ u) ! i) = fst ((u @ v) ! (\<sigma> i))"
    using hfst_bij hlen_uv by (by100 simp)
  have hsnd_bij': "\<And>i. i < length (u @ v) \<Longrightarrow> snd ((v @ u) ! i) = snd ((u @ v) ! (\<sigma> i))"
    using hsnd_bij hlen_uv by (by100 simp)
  have hsuc_bij': "\<And>i. i < length (u @ v) \<Longrightarrow> Suc (\<sigma> i) mod length (u @ v) = \<sigma> (Suc i mod length (u @ v))"
    using hsuc_bij hlen_uv by (by100 simp)
  have h_inst: "top1_quotient_of_scheme_on Y TY (u @ v) \<Longrightarrow>
      length (v @ u) = length (u @ v) \<Longrightarrow>
      bij_betw \<sigma> {..<length (u @ v)} {..<length (u @ v)} \<Longrightarrow>
      (\<And>i. i < length (u @ v) \<Longrightarrow> fst ((v @ u) ! i) = fst ((u @ v) ! (\<sigma> i))) \<Longrightarrow>
      (\<And>i. i < length (u @ v) \<Longrightarrow> snd ((v @ u) ! i) = snd ((u @ v) ! (\<sigma> i))) \<Longrightarrow>
      (\<And>i. i < length (u @ v) \<Longrightarrow> Suc (\<sigma> i) mod length (u @ v) = \<sigma> (Suc i mod length (u @ v))) \<Longrightarrow>
      top1_quotient_of_scheme_on Y TY (v @ u)"
    by (rule quotient_of_scheme_transfer_bij)
  show ?thesis using h_inst[OF assms hlen hbij' hfst_bij' hsnd_bij' hsuc_bij'] .
qed


end
