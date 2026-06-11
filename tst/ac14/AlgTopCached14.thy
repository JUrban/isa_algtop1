theory AlgTopCached14
  imports "AlgTopCached13.AlgTopCached13"
begin

\<comment> \<open>Each valid operation is reversible (valid\\_scheme\\_equiv is symmetric).\<close>
lemma valid_operation_reverse:
  "top1_valid_scheme_operation s t \<Longrightarrow> top1_valid_scheme_equiv t s"
proof (induction rule: top1_valid_scheme_operation.induct)
  case (v_rotate u v)
  show ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate[of v u]] by (by100 simp)
next
  case (v_cancel u a v)
  \<comment> \<open>Reverse of cancel = cancel\\_reverse (inserting the pair back).\<close>
  show ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_cancel_reverse[of u v a]] by (by100 simp)
next
  case (v_uncancel a u v)
  show ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_cancel[of u a v]] by (by100 simp)
next
  case (v_cancel_reverse u a v)
  show ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_cancel] by (by100 blast)
next
  case (v_cut_paste_reverse u1 a u2 u3)
  from valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste[of u1 a u2 u3]]
  show ?case .
next
  case (v_cut_paste2_reverse b u2 u1 u0 a)
  \<comment> \<open>Reverse of v\\_cut\\_paste2\\_reverse: use v\\_cut\\_paste2\\_nonfresh (no freshness needed).\<close>
  from valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste2_nonfresh[of u0 a u1 u2 b]]
  show ?case .
next
  case (v_invert w)
  \<comment> \<open>Double inversion: rev(inv(rev(inv w))) = w.\<close>
  have "rev (map top1_inverse_edge (rev (map top1_inverse_edge w))) = w"
  proof -
    have "\<And>x. top1_inverse_edge (top1_inverse_edge x) = x"
      unfolding top1_inverse_edge_def by (by100 simp)
    hence hinv2: "map top1_inverse_edge (map top1_inverse_edge w) = w"
      by (induction w) (by100 auto)+
    have step1: "map top1_inverse_edge (rev (map top1_inverse_edge w)) =
                 rev (map top1_inverse_edge (map top1_inverse_edge w))"
      using rev_map[of top1_inverse_edge "map top1_inverse_edge w"] by (by100 simp)
    have "rev (map top1_inverse_edge (rev (map top1_inverse_edge w))) =
          rev (rev (map top1_inverse_edge (map top1_inverse_edge w)))"
      using step1 by (by100 simp)
    also have "\<dots> = map top1_inverse_edge (map top1_inverse_edge w)" by (by100 simp)
    also have "\<dots> = w" using hinv2 .
    finally show ?thesis .
  qed
  thus ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_invert[of "rev (map top1_inverse_edge w)"]]
    by (by100 simp)
next
  case (v_relabel nw ol wd)
  from valid_relabel_reverse[OF v_relabel.hyps] show ?case .
next
  case (v_flip_label w a)
  \<comment> \<open>Flip is involutive.\<close>
  let ?f = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  have "?f (?f w) = w"
  proof (induction w)
    case Nil thus ?case by (by100 simp)
  next
    case (Cons e w) obtain l bo where "e = (l, bo)" by (cases e)
    thus ?case using Cons.IH by (by100 simp)
  qed
  thus ?case using valid_imp_equiv[OF top1_valid_scheme_operation.v_flip_label[of "?f w" a]]
    by (by100 simp)
next
  case (v_cut_paste u1 a u2 u3)
  from valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste_reverse[of u1 a u2 u3]]
  show ?case .
next
  case (v_cut_paste2 b u0 a u1 u2)
  from valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste2_reverse[of b u2 u1 u0 a]]
  show ?case .
next
  case (v_cut_paste2_nonfresh u0 a u1 u2 b)
  from valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste2_reverse[of b u2 u1 u0 a]]
  show ?case .
next
  case (v_cut_paste_opp u0 u1 a u2 u3)
  \<comment> \<open>Reverse of cut\\_paste\\_opp via: rotate + cut\\_paste\\_opp + rotate.
     Result: u0 @ [(a,T)] @ u2 @ [(a,F)] @ u1 @ u3.
     (1) Rotate by |u3|: u3 @ u0 @ [(a,T)] @ u2 @ [(a,F)] @ u1.
     (2) cut\\_paste\\_opp with u0'=[], u1'=u3@u0: [(a,T)] @ u2 @ [(a,F)] @ u3 @ u0 @ u1.
     (3) Rotate back: u0 @ u1 @ [(a,T)] @ u2 @ [(a,F)] @ u3. Done.\<close>
  let ?r = "u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1 @ u3"
  let ?orig = "u0 @ u1 @ [(a,True)] @ u2 @ [(a,False)] @ u3"
  have r1: "top1_valid_scheme_equiv ?r (u3 @ u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
      [of "u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1" u3]] by (by100 simp)
  have r2: "top1_valid_scheme_equiv (u3 @ u0 @ [(a,True)] @ u2 @ [(a,False)] @ u1)
            ([(a,True)] @ u2 @ [(a,False)] @ u3 @ u0 @ u1)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste_opp
      [of "[]" "u3 @ u0" a u2 u1]] by (by100 simp)
  have r3: "top1_valid_scheme_equiv ([(a,True)] @ u2 @ [(a,False)] @ u3 @ u0 @ u1) ?orig"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
      [of "[(a,True)] @ u2 @ [(a,False)] @ u3" "u0 @ u1"]] by (by100 simp)
  from r1 r2 r3 show ?case using valid_equiv_trans by (by100 blast)
next
  case (v_context_left y z prefix)
  \<comment> \<open>IH: valid\\_scheme\\_equiv z y. Lift through prefix.\<close>
  from valid_equiv_prepend[OF v_context_left.IH]
  show ?case .
qed

\<comment> \<open>Valid scheme equivalence is symmetric.\<close>
lemma valid_equiv_sym:
  "top1_valid_scheme_equiv s t \<Longrightarrow> top1_valid_scheme_equiv t s"
  unfolding top1_valid_scheme_equiv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl thus ?case by (by100 simp)
next
  case (rtrancl_into_rtrancl a b c)
  from valid_operation_reverse[OF rtrancl_into_rtrancl.hyps(2)]
  have "top1_valid_scheme_equiv c b" .
  from this rtrancl_into_rtrancl.IH show ?case
    unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
qed

section \<open>\<S>77 The Classification Theorem\<close>

\<comment> \<open>Lemma 77.1 Step 1, subcase y2 = []: a y1 a ~ aa y1\\<inverse>.
   Sequence: rotate \\<to> invert \\<to> flip\\_label a.
   Requires: a does not appear in y1 (from proper scheme).\<close>
\<comment> \<open>Valid version of step1\\_y2\\_empty.\<close>
lemma valid_Lemma_77_1_step1_y2_empty:
  assumes "\<forall>e \<in> set y1. fst e \<noteq> a"
  shows "top1_valid_scheme_equiv
      ([(a, True)] @ y1 @ [(a, True)])
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
proof -
  \<comment> \<open>Step 1: Rotate: [(a,T)] @ y1 @ [(a,T)] \\<to> y1 @ [(a,T),(a,T)].\<close>
  have s1: "top1_valid_scheme_equiv
      ([(a, True)] @ y1 @ [(a, True)])
      (y1 @ [(a, True), (a, True)])"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
      [of "[(a, True)]" "y1 @ [(a, True)]"]] by (by100 simp)
  \<comment> \<open>Step 2: Invert: y1 @ [(a,T),(a,T)] \\<to> [(a,F),(a,F)] @ inv(y1).\<close>
  have s2: "top1_valid_scheme_equiv
      (y1 @ [(a, True), (a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
  proof -
    have "top1_valid_scheme_operation (y1 @ [(a, True), (a, True)])
        (rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)])))"
      by (rule top1_valid_scheme_operation.v_invert)
    moreover have "rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)]))
        = [(a, False), (a, False)] @ rev (map top1_inverse_edge y1)"
      unfolding top1_inverse_edge_def by simp
    ultimately show ?thesis using valid_imp_equiv by (by100 simp)
  qed
  \<comment> \<open>Step 3: flip\\_label a: [(a,F),(a,F)] \\<to> [(a,T),(a,T)].\<close>
  have s3: "top1_valid_scheme_equiv
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
  proof -
    have "top1_valid_scheme_operation
        ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
        (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo))
             ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1)))"
      by (rule top1_valid_scheme_operation.v_flip_label)
    moreover have "map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo))
        ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
        = [(a, True), (a, True)] @ rev (map top1_inverse_edge y1)"
    proof -
      have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> a"
      proof
        fix e assume "e \<in> set (rev (map top1_inverse_edge y1))"
        then obtain e0 where he0: "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 auto)
        have "fst e = fst e0" using he0(2) unfolding top1_inverse_edge_def by (by100 simp)
        moreover have "fst e0 \<noteq> a" using he0(1) assms by (by100 blast)
        ultimately show "fst e \<noteq> a" by (by100 simp)
      qed
      define ry1 where "ry1 = rev (map top1_inverse_edge y1)"
      have hry1_fresh: "\<forall>e \<in> set ry1. fst e \<noteq> a"
      proof
        fix e assume "e \<in> set ry1"
        then obtain e0 where he0: "e0 \<in> set y1" "e = top1_inverse_edge e0"
          unfolding ry1_def by (by100 auto)
        have "fst e = fst e0" using he0(2) unfolding top1_inverse_edge_def by (by100 simp)
        have "fst e0 \<noteq> a" using he0(1) assms(1) by (by100 blast)
        thus "fst e \<noteq> a" using \<open>fst e = fst e0\<close> by (by100 simp)
      qed
      from hry1_fresh have "map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) ry1 = ry1"
      proof (induction ry1)
        case Nil thus ?case by (by100 simp)
      next
        case (Cons x xs)
        obtain l bo where hlbo: "x = (l, bo)" by (cases x)
        have "fst x \<noteq> a" using Cons.prems by (by100 simp)
        hence "l \<noteq> a" using hlbo by (by100 simp)
        hence "(case x of (l, bo) \<Rightarrow> (l, if l = a then \<not> bo else bo)) = x"
          using hlbo by (by100 simp)
        thus ?case using Cons by (by100 simp)
      qed
      hence "map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) (rev (map top1_inverse_edge y1))
          = rev (map top1_inverse_edge y1)" unfolding ry1_def .
      thus ?thesis by simp
    qed
    ultimately show ?thesis using valid_imp_equiv by (by100 simp)
  qed
  from s1 s2 s3 show ?thesis
    using valid_equiv_trans by (by100 blast)
qed

lemma Lemma_77_1_step1_y2_empty:
  assumes "\<forall>e \<in> set y1. fst e \<noteq> a"
  shows "top1_scheme_equiv
      ([(a, True)] @ y1 @ [(a, True)])
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
proof -
  \<comment> \<open>Step 1: Rotate: [(a,T)] @ y1 @ [(a,T)] \\<to> y1 @ [(a,T),(a,T)].\<close>
  have h1: "top1_elementary_scheme_operation
      ([(a, True)] @ (y1 @ [(a, True)]))
      ((y1 @ [(a, True)]) @ [(a, True)])"
    by (rule top1_elementary_scheme_operation.rotate)
  \<comment> \<open>Step 2: Invert: y1 @ [(a,T),(a,T)] \\<to> [(a,F),(a,F)] @ inv(y1).\<close>
  have h2: "top1_elementary_scheme_operation
      (y1 @ [(a, True), (a, True)])
      (rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)])))"
    by (rule top1_elementary_scheme_operation.invert)
  \<comment> \<open>Simplify: rev(map inv (y1 @ [(a,T),(a,T)])) = [(a,F),(a,F)] @ rev(map inv y1).\<close>
  have h2_simp: "rev (map top1_inverse_edge (y1 @ [(a, True), (a, True)]))
      = [(a, False), (a, False)] @ rev (map top1_inverse_edge y1)"
    unfolding top1_inverse_edge_def by simp
  \<comment> \<open>Step 3: flip\\_label a: [(a,F),(a,F)] @ inv(y1) \\<to> [(a,T),(a,T)] @ inv(y1).
     (Since a not in y1, flip\\_label only affects the two a-edges.)\<close>
  have h3: "top1_elementary_scheme_operation
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      (map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
           ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1)))"
    by (rule top1_elementary_scheme_operation.flip_label)
  have h3_simp: "map (\<lambda>(l,b). (l, if l = a then \<not>b else b))
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      = [(a, True), (a, True)] @ rev (map top1_inverse_edge y1)"
  proof -
    have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) [(a, False), (a, False)]
        = [(a, True), (a, True)]" by simp
    moreover have "map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) (rev (map top1_inverse_edge y1))
        = rev (map top1_inverse_edge y1)"
    proof (rule map_idI)
      fix e assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by simp
      then obtain e0 where "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 auto)
      hence "fst e = fst e0" unfolding top1_inverse_edge_def by (by100 simp)
      have "fst e0 \<noteq> a" using assms \<open>e0 \<in> set y1\<close> by (by100 blast)
      hence "fst e \<noteq> a" using \<open>fst e = fst e0\<close> by simp
      thus "(case e of (l, b) \<Rightarrow> (l, if l = a then \<not> b else b)) = e"
        using \<open>fst e \<noteq> a\<close> by (cases e) simp
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Chain: w \\<to> w1 \\<to> w2 \\<to> w3.\<close>
  \<comment> \<open>Chain the 3 operations via rtranclp.\<close>
  have step1: "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)]) (y1 @ [(a, True), (a, True)])"
    unfolding top1_scheme_equiv_def using h1 by simp
  have step2: "top1_scheme_equiv (y1 @ [(a, True), (a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h2 h2_simp by simp
  have step3: "top1_scheme_equiv ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))
      ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def using h3 h3_simp by simp
  \<comment> \<open>Chain: step1 \\<to> step2 \\<to> step3.\<close>
  from step1 step2 have "top1_scheme_equiv ([(a, True)] @ y1 @ [(a, True)])
      ([(a, False), (a, False)] @ rev (map top1_inverse_edge y1))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from this step3 show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Lemma 77.1 (Munkres): If w = [y0] a [y1] a [y2] (proper scheme with a appearing twice
   with same exponent), then w ~ aa [y0 y1\\<inverse> y2].\<close>
\<comment> \<open>Valid version of Lemma 77.1: projective collection.\<close>
lemma valid_Lemma_77_1_projective_collection:
  assumes "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
      and "\<exists>b::'a. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  shows "top1_valid_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
proof (cases "y0 = []")
  case True
  show ?thesis
  proof (cases "y1 = []")
    case True
    show ?thesis using \<open>y0 = []\<close> True unfolding top1_valid_scheme_equiv_def by simp
  next
    case False
    show ?thesis
    proof (cases "y2 = []")
      case True
      \<comment> \<open>y0=[], y2=[]: a y1 a ~ aa y1\\<inverse>. From Lemma\\_77\\_1\\_step1\\_y2\\_empty via old chain.\<close>
      have "\<forall>e \<in> set y1. fst e \<noteq> a" using assms by (by100 blast)
      from valid_Lemma_77_1_step1_y2_empty[OF this]
      show ?thesis using \<open>y0 = []\<close> True by simp
    next
      case False2: False
      \<comment> \<open>y0=[], y1,y2 non-empty: direct cut\\_paste.\<close>
      have "top1_valid_scheme_operation
          ([] @ [(a, True)] @ y1 @ [(a, True)] @ y2)
          ([] @ [(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        by (rule top1_valid_scheme_operation.v_cut_paste)
      hence "top1_valid_scheme_equiv
          ([(a, True)] @ y1 @ [(a, True)] @ y2)
          ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        using valid_imp_equiv by (by100 simp)
      thus ?thesis using \<open>y0 = []\<close> by (by100 simp)
    qed
  qed
next
  case False
  obtain b :: 'a where hb: "b \<noteq> a" "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    using assms(2) by (by100 blast)
  \<comment> \<open>Step 2a: cut\\_paste2 with fresh b.\<close>
  have hb_fresh: "b \<notin> scheme_labels (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)"
    unfolding scheme_labels_def using hb by (by100 auto)
  have step2a: "top1_valid_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste2[OF hb_fresh]]
    by (by100 simp)
  \<comment> \<open>Step 2b: cut\\_paste.\<close>
  have step2b: "top1_valid_scheme_equiv
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_cut_paste
      [of "[]" b y2 "y1 @ rev (map top1_inverse_edge y0)"]]
    by (by100 simp)
  \<comment> \<open>Step 2c: invert.\<close>
  have step2c: "top1_valid_scheme_equiv
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
  proof -
    have "top1_valid_scheme_operation
        ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
        (rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))))"
      by (rule top1_valid_scheme_operation.v_invert)
    moreover have "rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0)))
        = y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)]"
    proof -
      have hinv_inv: "\<And>x :: ('a \<times> bool). top1_inverse_edge (top1_inverse_edge x) = x"
        unfolding top1_inverse_edge_def by (by100 simp)
      have hcomp_id: "top1_inverse_edge \<circ> (top1_inverse_edge :: ('a \<times> bool) \<Rightarrow> _) = id"
        by (rule ext) (simp add: hinv_inv)
      have hmap_inv_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (map top1_inverse_edge xs) = xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map top1_inverse_edge (map top1_inverse_edge xs) = map (top1_inverse_edge \<circ> top1_inverse_edge) xs"
          by (by100 simp)
        also have "\<dots> = map id xs" using hcomp_id by simp
        also have "\<dots> = xs" by simp
        finally show "map top1_inverse_edge (map top1_inverse_edge xs) = xs" .
      qed
      have hrev_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map top1_inverse_edge (rev (map top1_inverse_edge xs))
            = rev (map top1_inverse_edge (map top1_inverse_edge xs))"
          by (simp add: rev_map)
        also have "\<dots> = rev xs" using hmap_inv_inv by simp
        finally show "map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs" .
      qed
      have hmap_comp_inv: "\<And>xs :: ('a \<times> bool) list. map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs"
        using hcomp_id by simp
      show ?thesis
        by (simp add: rev_map hmap_comp_inv hrev_inv top1_inverse_edge_def)
    qed
    ultimately have "top1_valid_scheme_operation
        ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
        (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
      by (by100 simp)
    thus ?thesis by (rule valid_imp_equiv)
  qed
  \<comment> \<open>Step 2d: rotate.\<close>
  have step2d: "top1_valid_scheme_equiv
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate[of
        "y0 @ rev (map top1_inverse_edge y1) @ y2" "[(b, False), (b, False)]"]]
    by (by100 simp)
  \<comment> \<open>Step 2e: flip\\_label b.\<close>
  have step2e: "top1_valid_scheme_equiv
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_valid_scheme_operation
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
             ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_valid_scheme_operation.v_flip_label)
    moreover have "map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have "\<And>xs. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      moreover have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      ultimately show ?thesis by simp
    qed
    ultimately have "top1_valid_scheme_operation
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
      by (by100 simp)
    thus ?thesis by (rule valid_imp_equiv)
  qed
  \<comment> \<open>Step 2f: relabel b \\<to> a (valid since a \\<notin> labels).\<close>
  have step2f: "top1_valid_scheme_equiv
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    \<comment> \<open>a is fresh in the current scheme (a \\<notin> labels of y0, y1, y2, and a \\<noteq> b).\<close>
    have hfst_inv_map: "\<And>xs :: ('a \<times> bool) list. fst ` set (map top1_inverse_edge xs) = fst ` set xs"
    proof -
      fix xs :: "('a \<times> bool) list"
      show "fst ` set (map top1_inverse_edge xs) = fst ` set xs"
      proof (induction xs)
        case Nil thus ?case by (by100 simp)
      next
        case (Cons x xs)
        obtain l bo where hlbo: "x = (l, bo)" by (cases x)
        have "top1_inverse_edge (l, bo) = (l, \<not>bo)" unfolding top1_inverse_edge_def by (by100 simp)
        thus ?case using hlbo Cons.IH by (by100 auto)
      qed
    qed
    have hfst_inv: "\<And>xs :: ('a \<times> bool) list. fst ` set (rev (map top1_inverse_edge xs)) = fst ` set xs"
      using hfst_inv_map by (by100 simp)
    have ha_fresh: "a \<notin> fst ` set ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    proof -
      have "a \<noteq> b" using hb(1) by (by100 blast)
      have "a \<notin> fst ` set y0" using assms(1) by (by100 blast)
      have "a \<notin> fst ` set y1" using assms(1) by (by100 blast)
      hence "a \<notin> fst ` set (rev (map top1_inverse_edge y1))" using hfst_inv[of y1] by (by100 simp)
      have "a \<notin> fst ` set y2" using assms(1) by (by100 blast)
      show ?thesis using \<open>a \<noteq> b\<close> \<open>a \<notin> fst ` set y0\<close> \<open>a \<notin> fst ` set (rev (map top1_inverse_edge y1))\<close>
          \<open>a \<notin> fst ` set y2\<close> by (by100 auto)
    qed
    have "top1_valid_scheme_operation
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (if l = b then a else l, bo))
             ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_valid_scheme_operation.v_relabel[OF ha_fresh hb(1)[symmetric]])
    moreover have "map (\<lambda>(l, bo). (if l = b then a else l, bo))
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have "\<And>xs. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (if l = b then a else l, bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      have "\<forall>e \<in> set y0. fst e \<noteq> b" using hb(2) by (by100 blast)
      have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      have "\<forall>e \<in> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      have hmap_relabel: "\<And>xs :: ('a \<times> bool) list. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (if l = b then a else l, bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      show ?thesis
        using hmap_relabel[OF \<open>\<forall>e \<in> set y0. fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set y2. fst e \<noteq> b\<close>]
        by simp
    qed
    ultimately have "top1_valid_scheme_operation
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
      by (by100 simp)
    thus ?thesis by (rule valid_imp_equiv)
  qed
  \<comment> \<open>Chain all steps.\<close>
  from step2a step2b step2c step2d step2e step2f
  show ?thesis
    using valid_equiv_trans by (by100 blast)
qed

lemma Lemma_77_1_projective_collection:
  assumes "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
      and "\<exists>b::'a. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  shows "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
proof (cases "y0 = []")
  case True
  \<comment> \<open>Step 1: y0 empty. Show a y1 a y2 ~ aa y1\\<inverse> y2.\<close>
  show ?thesis
  proof (cases "y1 = []")
    case True
    \<comment> \<open>y1 = []: a a y2 ~ aa y2. Trivially same (reflexivity).\<close>
    show ?thesis using \<open>y0 = []\<close> True unfolding top1_scheme_equiv_def by simp
  next
    case False
    show ?thesis
    proof (cases "y2 = []")
      case True
      \<comment> \<open>y2 = []: a y1 a ~ aa y1\\<inverse>. Use Lemma\\_77\\_1\\_step1\\_y2\\_empty.\<close>
      have "\<forall>e \<in> set y1. fst e \<noteq> a" using assms by (by100 blast)
      from Lemma_77_1_step1_y2_empty[OF this]
      show ?thesis using \<open>y0 = []\<close> True by simp
    next
      case False2: False
      \<comment> \<open>Both y1, y2 non-empty: direct from cut\\_paste operation.\<close>
      have "top1_elementary_scheme_operation
          ([] @ [(a, True)] @ y1 @ [(a, True)] @ y2)
          ([] @ [(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        by (rule top1_elementary_scheme_operation.cut_paste)
      hence "top1_scheme_equiv
          ([(a, True)] @ y1 @ [(a, True)] @ y2)
          ([(a, True), (a, True)] @ rev (map top1_inverse_edge y1) @ y2)"
        unfolding top1_scheme_equiv_def by simp
      thus ?thesis using \<open>y0 = []\<close> by simp
    qed
  qed
next
  case False
  \<comment> \<open>Step 2: y0 non-empty. Book proof (Munkres Figure 77.2):
     y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> \\<sim> aa y0 y1\\<inverse> y2.\<close>
  \<comment> \<open>Choose a fresh label b \\<noteq> a (exists because labels are from an infinite type).\<close>
  obtain b :: 'a where hb: "b \<noteq> a" "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    using assms(2) by (by100 blast)
  \<comment> \<open>Step 2a: y0 a y1 a y2 \\<sim> b y2 b (y1 y0\\<inverse>) via cut\\_paste2.\<close>
  have step2a: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste2[of y0 a y1 y2 b] by simp
  \<comment> \<open>Step 2b: b y2 b (y1 y0\\<inverse>) \\<sim> bb y2\\<inverse> y1 y0\\<inverse> via cut\\_paste (Step 1).\<close>
  have step2b: "top1_scheme_equiv
      ([(b, True)] @ y2 @ [(b, True)] @ y1 @ rev (map top1_inverse_edge y0))
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste[of "[]" b y2 "y1 @ rev (map top1_inverse_edge y0)"]
    by simp
  \<comment> \<open>Step 2c: bb y2\\<inverse> y1 y0\\<inverse> \\<sim> (y0 y1\\<inverse> y2) b\\<inverse> b\\<inverse> via invert.\<close>
  have step2c: "top1_scheme_equiv
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))
        (rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))))"
      by (rule top1_elementary_scheme_operation.invert)
    moreover have "rev (map top1_inverse_edge ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0)))
        = y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)]"
    proof -
      have hinv_inv: "\<And>x. top1_inverse_edge (top1_inverse_edge x) = x"
        unfolding top1_inverse_edge_def by (by100 simp)
      have hmap_inv_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (map top1_inverse_edge xs) = xs"
        by (simp add: hinv_inv map_idI)
      have hrev_inv: "\<And>xs :: ('a \<times> bool) list. map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map top1_inverse_edge (rev (map top1_inverse_edge xs))
            = rev (map top1_inverse_edge (map top1_inverse_edge xs))"
          by (simp add: rev_map)
        also have "\<dots> = rev xs" using hmap_inv_inv by simp
        finally show "map top1_inverse_edge (rev (map top1_inverse_edge xs)) = rev xs" .
      qed
      have hcomp_id: "top1_inverse_edge \<circ> top1_inverse_edge = id"
      proof (rule ext)
        fix x show "(top1_inverse_edge \<circ> top1_inverse_edge) x = id x" using hinv_inv by simp
      qed
      have hmap_comp_id: "\<And>xs :: ('a \<times> bool) list. map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs"
      proof -
        fix xs :: "('a \<times> bool) list"
        have "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = map id xs"
          by (rule arg_cong[of _ _ "\<lambda>f. map f xs"]) (rule hcomp_id)
        thus "map (top1_inverse_edge \<circ> top1_inverse_edge) xs = xs" by simp
      qed
      show ?thesis
        by (simp add: rev_map hmap_comp_id hrev_inv top1_inverse_edge_def)
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2d: rotate to b\\<inverse> b\\<inverse> (y0 y1\\<inverse> y2).\<close>
  have step2d: "top1_scheme_equiv
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate[of
        "y0 @ rev (map top1_inverse_edge y1) @ y2" "[(b, False), (b, False)]"]
    by simp
  \<comment> \<open>Step 2e: flip\\_label b: b\\<inverse>b\\<inverse> \\<to> bb.\<close>
  have step2e: "top1_scheme_equiv
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
             ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.flip_label)
    moreover have "map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo))
        ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have "\<And>xs. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      moreover have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Step 2f: relabel b \\<to> a.\<close>
  have step2f: "top1_scheme_equiv
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
      ([(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
  proof -
    have "top1_elementary_scheme_operation
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        (map (\<lambda>(l, bo). (if l = b then a else l, bo))
             ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2))"
      by (rule top1_elementary_scheme_operation.relabel)
    moreover have "map (\<lambda>(l, bo). (if l = b then a else l, bo))
        ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)
        = [(a, True), (a, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2"
    proof -
      have hmap_relabel: "\<And>xs :: ('a \<times> bool) list. (\<forall>e \<in> set xs. fst e \<noteq> b) \<Longrightarrow>
          map (\<lambda>(l, bo). (if l = b then a else l, bo)) xs = xs"
        by (rule map_idI) (by100 auto)
      have "\<forall>e \<in> set y0. fst e \<noteq> b" using hb(2) by (by100 blast)
      have "\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b"
        using hb(2) unfolding top1_inverse_edge_def by (by100 auto)
      have "\<forall>e \<in> set y2. fst e \<noteq> b" using hb(2) by (by100 blast)
      show ?thesis
        using hmap_relabel[OF \<open>\<forall>e \<in> set y0. fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set (rev (map top1_inverse_edge y1)). fst e \<noteq> b\<close>]
            hmap_relabel[OF \<open>\<forall>e \<in> set y2. fst e \<noteq> b\<close>]
        by simp
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by simp
  qed
  \<comment> \<open>Chain all steps.\<close>
  \<comment> \<open>Chain all steps via transitivity.\<close>
  from step2a step2b have s_ab: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ rev (map top1_inverse_edge y2) @ y1 @ rev (map top1_inverse_edge y0))"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_ab step2c have s_abc: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      (y0 @ rev (map top1_inverse_edge y1) @ y2 @ [(b, False), (b, False)])"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abc step2d have s_abcd: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, False), (b, False)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcd step2e have s_abcde: "top1_scheme_equiv
      (y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2)
      ([(b, True), (b, True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
  from s_abcde step2f show ?thesis
    unfolding top1_scheme_equiv_def by (rule rtranclp_trans)
qed

\<comment> \<open>Key lemma: for w0=[], w2=[], we can extract the commutator to front.
   a b w1 a\\<inverse> b\\<inverse> ~ a b a\\<inverse> b\\<inverse> w1.
   6-step sequence: rotate, flip\\_label a, cut\\_paste\\_opp a, flip\\_label a, rotate, cut\\_paste\\_opp b.\<close>
lemma Lemma_77_3_simple:
  assumes hab: "a \<noteq> b"
  shows "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
proof -
  let ?w = "[(a, True), (b, True)] @ w1 @ [(a, False), (b, False)]"
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_elementary_scheme_operation ?w
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
    using top1_elementary_scheme_operation.rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)]"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_elementary_scheme_operation
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    \<comment> \<open>First show the target equals the map result.\<close>
    have htarget: "?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a (move ?flip\\_a w1 from before a to after a\\<inverse>).\<close>
  have s3: "top1_elementary_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)]" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (flip back: restores w1).\<close>
  have s4: "top1_elementary_scheme_operation
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    have hflip_invol: "?flip_a (?flip_a w1) = w1"
    proof (induction w1)
      case Nil thus ?case by simp
    next
      case (Cons e w1)
      obtain l bo where he: "e = (l, bo)" by (cases e)
      show ?case using Cons.IH by (simp add: he)
    qed
    have htarget: "[(a, False), (b, False), (a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_elementary_scheme_operation
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])"
    using top1_elementary_scheme_operation.rotate
      [of "[(a,False),(b,False)]" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b (move w1 from before b to after b\\<inverse>).\<close>
  have s6: "top1_elementary_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" "[]"] by simp
  \<comment> \<open>Chain all steps.\<close>
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_scheme_equiv_def
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

\<comment> \<open>Extended simple case: a b w1 a\\<inverse> b\\<inverse> w2 ~ a b a\\<inverse> b\\<inverse> w1 w2 (w0=[], general w2).
   Same 6-step proof as Lemma\\_77\\_3\\_simple — the tail w2 passes through all steps.\<close>
lemma Lemma_77_3_w0_empty:
  assumes hab: "a \<noteq> b"
  shows "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  have hba: "b \<noteq> a" using hab by (by100 blast)
  have hflip_invol: "\<And>xs. ?flip_a (?flip_a xs) = xs"
  proof -
    fix xs :: "('a \<times> bool) list"
    show "?flip_a (?flip_a xs) = xs"
    proof (induction xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
      thus ?case using Cons.IH by simp
    qed
  qed
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_elementary_scheme_operation
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
    using top1_elementary_scheme_operation.rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)] @ w2"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_elementary_scheme_operation
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])"
  proof -
    have htarget: "?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a.\<close>
  have s3: "top1_elementary_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)] @ ?flip_a w2" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (restores w1 and w2).\<close>
  have s4: "top1_elementary_scheme_operation
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])"
  proof -
    have htarget: "[(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_elementary_scheme_operation.flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_elementary_scheme_operation
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)"
    using top1_elementary_scheme_operation.rotate
      [of "[(a,False),(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b.\<close>
  have s6: "top1_elementary_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
    using top1_elementary_scheme_operation.cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" w2] by simp
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_scheme_equiv_def
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
qed

\<comment> \<open>Lemma 77.3 (Munkres): general case. w0 a b w1 a\\<inverse> b\\<inverse> w2 ~ (aba\\<inverse>b\\<inverse>) w0 w1 w2.
   Proof: cut\\_paste\\_opp to move w0, then w0-empty case, then cut\\_paste\\_opp on b.\<close>
lemma Lemma_77_3_torus_extraction:
  assumes "a \<noteq> b"
  shows "top1_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  let ?flip_b = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs"
  have hab': "b \<noteq> a" using assms by (by100 blast)
  \<comment> \<open>Step 1: cut\\_paste\\_opp on a moves w0 past a\\<inverse>.\<close>
  have s1: "top1_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste_opp[of "[]" w0 a "[(b,True)] @ w1" "[(b,False)] @ w2"]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>After step 1: a b w1 a\\<inverse> w0 b\\<inverse> w2.
     Step 2 (flip trick on a, 5 ops): swap w1 past (b,T).
     Result: a w1 b a\\<inverse> w0 b\\<inverse> w2.\<close>
  have s2: "top1_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move [(a,T),(b,T)] to end.\<close>
    have r1: "top1_elementary_scheme_operation
        ([(a,True),(b,True)] @ w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2)
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,True),(b,True)]" "w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label a.\<close>
    have r2_eq: "?flip_a (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        = ?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)]"
      using hab' by simp
    have r2: "top1_elementary_scheme_operation
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])"
      unfolding r2_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>cut\\_paste\\_opp on a: move ?flip\\_a w1 from before a to after a\\<inverse>.\<close>
    have r3: "top1_elementary_scheme_operation
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])"
      using top1_elementary_scheme_operation.cut_paste_opp
        [of "[]" "?flip_a w1" a "?flip_a w0 @ [(b,False)] @ ?flip_a w2" "[(b,True)]"] by simp
    \<comment> \<open>flip\\_label a back.\<close>
    have r4_eq: "?flip_a ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        = [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)]"
    proof -
      have hflip_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_a (?flip_a xs) = xs"
      proof -
        fix xs :: "('a \<times> bool) list" show "?flip_a (?flip_a xs) = xs"
        proof (induction xs)
          case Nil thus ?case by simp
        next
          case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
          thus ?case using Cons.IH by simp
        qed
      qed
      thus ?thesis using hab' by simp
    qed
    have r4: "top1_elementary_scheme_operation
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])"
      unfolding r4_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>rotate: bring [(a,T)] w1 [(b,T)] to front.\<close>
    have r5: "top1_elementary_scheme_operation
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,False)] @ w0 @ [(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_scheme_equiv_def
      by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  qed
  \<comment> \<open>Step 3 (flip trick on b, 5 ops): move w0 from between a\\<inverse>, b\\<inverse> to between b, a\\<inverse>.
     Result: a w1 b w0 a\\<inverse> b\\<inverse> w2 (now a\\<inverse>b\\<inverse> are adjacent!).\<close>
  have s3: "top1_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move prefix to end.\<close>
    have r1: "top1_elementary_scheme_operation
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])"
      using top1_elementary_scheme_operation.rotate
        [of "[(a,True)] @ w1 @ [(b,True),(a,False)]" "w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label b.\<close>
    have r2_eq: "?flip_b (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        = ?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)]"
      using assms by simp
    have r2: "top1_elementary_scheme_operation
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])"
      unfolding r2_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>cut\\_paste\\_opp on b: move ?flip\\_b w0 from before b to after b\\<inverse>.\<close>
    have r3: "top1_elementary_scheme_operation
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])"
      using top1_elementary_scheme_operation.cut_paste_opp
        [of "[]" "?flip_b w0" b "?flip_b w2 @ [(a,True)] @ ?flip_b w1" "[(a,False)]"] by simp
    \<comment> \<open>flip\\_label b back.\<close>
    have hflip_b_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_b (?flip_b xs) = xs"
    proof -
      fix xs :: "('a \<times> bool) list" show "?flip_b (?flip_b xs) = xs"
      proof (induction xs)
        case Nil thus ?case by simp
      next
        case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
        thus ?case using Cons.IH by simp
      qed
    qed
    have r4_eq: "?flip_b ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        = [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"
      using assms hflip_b_invol by simp
    have r4: "top1_elementary_scheme_operation
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])"
      unfolding r4_eq[symmetric] by (rule top1_elementary_scheme_operation.flip_label)
    \<comment> \<open>rotate: bring the right part to front.\<close>
    have r5: "top1_elementary_scheme_operation
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])
        ([(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False),(b,False)] @ w2)"
      using top1_elementary_scheme_operation.rotate
        [of "[(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_scheme_equiv_def
      by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  qed
  \<comment> \<open>Step 4: cut\\_paste\\_opp on b moves w1 from before b to after b\\<inverse>.
     a [w1] b [w0] a\\<inverse> b\\<inverse> w2 \\<to> a b [w0] a\\<inverse> b\\<inverse> [w1] w2.\<close>
  have s4: "top1_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.cut_paste_opp[of "[(a,True)]" w1 b "w0 @ [(a,False)]" w2]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>Step 5: apply Lemma\\_77\\_3\\_w0\\_empty: a b w0 a\\<inverse> b\\<inverse> (w1@w2) ~ a b a\\<inverse> b\\<inverse> w0 w1 w2.\<close>
  have s5: "top1_scheme_equiv
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
    using Lemma_77_3_w0_empty[OF assms, of w0 "w1 @ w2"] by simp
  from s1 s2 s3 s4 s5 show ?thesis
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

lemma valid_Lemma_77_3_simple:
  assumes hab: "a \<noteq> b"
  shows "top1_valid_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
proof -
  let ?w = "[(a, True), (b, True)] @ w1 @ [(a, False), (b, False)]"
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_valid_scheme_operation ?w
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
    using top1_valid_scheme_operation.v_rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)]"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_valid_scheme_operation
      (w1 @ [(a, False), (b, False), (a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    \<comment> \<open>First show the target equals the map result.\<close>
    have htarget: "?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False), (a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_valid_scheme_operation.v_flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a (move ?flip\\_a w1 from before a to after a\\<inverse>).\<close>
  have s3: "top1_valid_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False), (a, False), (b, True)])
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_valid_scheme_operation.v_cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)]" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (flip back: restores w1).\<close>
  have s4: "top1_valid_scheme_operation
      ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])"
  proof -
    have hba: "b \<noteq> a" using hab by (by100 blast)
    have hflip_invol: "?flip_a (?flip_a w1) = w1"
    proof (induction w1)
      case Nil thus ?case by simp
    next
      case (Cons e w1)
      obtain l bo where he: "e = (l, bo)" by (cases e)
      show ?case using Cons.IH by (simp add: he)
    qed
    have htarget: "[(a, False), (b, False), (a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False), (a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_valid_scheme_operation.v_flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_valid_scheme_operation
      ([(a, False), (b, False), (a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])"
    using top1_valid_scheme_operation.v_rotate
      [of "[(a,False),(b,False)]" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b (move w1 from before b to after b\\<inverse>).\<close>
  have s6: "top1_valid_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)])
      ([(a, True), (b, True), (a, False), (b, False)] @ w1)"
    using top1_valid_scheme_operation.v_cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" "[]"] by simp
  \<comment> \<open>Chain all steps.\<close>
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_valid_scheme_equiv_def
    by (by100 simp)
qed

\<comment> \<open>Extended simple case: a b w1 a\\<inverse> b\\<inverse> w2 ~ a b a\\<inverse> b\\<inverse> w1 w2 (w0=[], general w2).
   Same 6-step proof as Lemma\\_77\\_3\\_simple — the tail w2 passes through all steps.\<close>
lemma valid_valid_Lemma_77_3_w0_empty:
  assumes hab: "a \<noteq> b"
  shows "top1_valid_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  have hba: "b \<noteq> a" using hab by (by100 blast)
  have hflip_invol: "\<And>xs. ?flip_a (?flip_a xs) = xs"
  proof -
    fix xs :: "('a \<times> bool) list"
    show "?flip_a (?flip_a xs) = xs"
    proof (induction xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
      thus ?case using Cons.IH by simp
    qed
  qed
  \<comment> \<open>Step 1: rotate.\<close>
  have s1: "top1_valid_scheme_operation
      ([(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
    using top1_valid_scheme_operation.v_rotate[of "[(a,True),(b,True)]" "w1 @ [(a,False),(b,False)] @ w2"]
    by simp
  \<comment> \<open>Step 2: flip\\_label a.\<close>
  have s2: "top1_valid_scheme_operation
      (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])"
  proof -
    have htarget: "?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)]
        = ?flip_a (w1 @ [(a, False), (b, False)] @ w2 @ [(a, True), (b, True)])"
      using hba by simp
    show ?thesis unfolding htarget
      by (rule top1_valid_scheme_operation.v_flip_label)
  qed
  \<comment> \<open>Step 3: cut\\_paste\\_opp on a.\<close>
  have s3: "top1_valid_scheme_operation
      (?flip_a w1 @ [(a, True), (b, False)] @ ?flip_a w2 @ [(a, False), (b, True)])
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
    using top1_valid_scheme_operation.v_cut_paste_opp
      [of "[]" "?flip_a w1" a "[(b, False)] @ ?flip_a w2" "[(b, True)]"] by simp
  \<comment> \<open>Step 4: flip\\_label a (restores w1 and w2).\<close>
  have s4: "top1_valid_scheme_operation
      ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])"
  proof -
    have htarget: "[(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)]
        = ?flip_a ([(a, True), (b, False)] @ ?flip_a w2 @ [(a, False)] @ ?flip_a w1 @ [(b, True)])"
      using hba hflip_invol by simp
    show ?thesis unfolding htarget
      by (rule top1_valid_scheme_operation.v_flip_label)
  qed
  \<comment> \<open>Step 5: rotate.\<close>
  have s5: "top1_valid_scheme_operation
      ([(a, False), (b, False)] @ w2 @ [(a, True)] @ w1 @ [(b, True)])
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)"
    using top1_valid_scheme_operation.v_rotate
      [of "[(a,False),(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
  \<comment> \<open>Step 6: cut\\_paste\\_opp on b.\<close>
  have s6: "top1_valid_scheme_operation
      ([(a, True)] @ w1 @ [(b, True), (a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w1 @ w2)"
    using top1_valid_scheme_operation.v_cut_paste_opp
      [of "[(a, True)]" w1 b "[(a, False)]" w2] by simp
  from s1 s2 s3 s4 s5 s6
  show ?thesis unfolding top1_valid_scheme_equiv_def
    by (by100 simp)
qed

\<comment> \<open>Lemma 77.3 (Munkres): general case. w0 a b w1 a\\<inverse> b\\<inverse> w2 ~ (aba\\<inverse>b\\<inverse>) w0 w1 w2.
   Proof: cut\\_paste\\_opp to move w0, then w0-empty case, then cut\\_paste\\_opp on b.\<close>
lemma valid_Lemma_77_3_torus_extraction:
  assumes "a \<noteq> b"
  shows "top1_valid_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
proof -
  let ?flip_a = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) xs"
  let ?flip_b = "\<lambda>xs. map (\<lambda>(l, bo). (l, if l = b then \<not> bo else bo)) xs"
  have hab': "b \<noteq> a" using assms by (by100 blast)
  \<comment> \<open>Step 1: cut\\_paste\\_opp on a moves w0 past a\\<inverse>.\<close>
  have s1: "top1_valid_scheme_equiv
      (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)"
    unfolding top1_valid_scheme_equiv_def
    using top1_valid_scheme_operation.v_cut_paste_opp[of "[]" w0 a "[(b,True)] @ w1" "[(b,False)] @ w2"]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>After step 1: a b w1 a\\<inverse> w0 b\\<inverse> w2.
     Step 2 (flip trick on a, 5 ops): swap w1 past (b,T).
     Result: a w1 b a\\<inverse> w0 b\\<inverse> w2.\<close>
  have s2: "top1_valid_scheme_equiv
      ([(a, True), (b, True)] @ w1 @ [(a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move [(a,T),(b,T)] to end.\<close>
    have r1: "top1_valid_scheme_operation
        ([(a,True),(b,True)] @ w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2)
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])"
      using top1_valid_scheme_operation.v_rotate
        [of "[(a,True),(b,True)]" "w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label a.\<close>
    have r2_eq: "?flip_a (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        = ?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)]"
      using hab' by simp
    have r2: "top1_valid_scheme_operation
        (w1 @ [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True),(b,True)])
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])"
      unfolding r2_eq[symmetric] by (rule top1_valid_scheme_operation.v_flip_label)
    \<comment> \<open>cut\\_paste\\_opp on a: move ?flip\\_a w1 from before a to after a\\<inverse>.\<close>
    have r3: "top1_valid_scheme_operation
        (?flip_a w1 @ [(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False),(b,True)])
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])"
      using top1_valid_scheme_operation.v_cut_paste_opp
        [of "[]" "?flip_a w1" a "?flip_a w0 @ [(b,False)] @ ?flip_a w2" "[(b,True)]"] by simp
    \<comment> \<open>flip\\_label a back.\<close>
    have r4_eq: "?flip_a ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        = [(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)]"
    proof -
      have hflip_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_a (?flip_a xs) = xs"
      proof -
        fix xs :: "('a \<times> bool) list" show "?flip_a (?flip_a xs) = xs"
        proof (induction xs)
          case Nil thus ?case by simp
        next
          case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
          thus ?case using Cons.IH by simp
        qed
      qed
      thus ?thesis using hab' by simp
    qed
    have r4: "top1_valid_scheme_operation
        ([(a,True)] @ ?flip_a w0 @ [(b,False)] @ ?flip_a w2 @ [(a,False)] @ ?flip_a w1 @ [(b,True)])
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])"
      unfolding r4_eq[symmetric] by (rule top1_valid_scheme_operation.v_flip_label)
    \<comment> \<open>rotate: bring [(a,T)] w1 [(b,T)] to front.\<close>
    have r5: "top1_valid_scheme_operation
        ([(a,False)] @ w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)])
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)"
      using top1_valid_scheme_operation.v_rotate
        [of "[(a,False)] @ w0 @ [(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_valid_scheme_equiv_def
      by (by100 simp)
  qed
  \<comment> \<open>Step 3 (flip trick on b, 5 ops): move w0 from between a\\<inverse>, b\\<inverse> to between b, a\\<inverse>.
     Result: a w1 b w0 a\\<inverse> b\\<inverse> w2 (now a\\<inverse>b\\<inverse> are adjacent!).\<close>
  have s3: "top1_valid_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True), (a, False)] @ w0 @ [(b, False)] @ w2)
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)"
  proof -
    \<comment> \<open>rotate: move prefix to end.\<close>
    have r1: "top1_valid_scheme_operation
        ([(a,True)] @ w1 @ [(b,True),(a,False)] @ w0 @ [(b,False)] @ w2)
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])"
      using top1_valid_scheme_operation.v_rotate
        [of "[(a,True)] @ w1 @ [(b,True),(a,False)]" "w0 @ [(b,False)] @ w2"] by simp
    \<comment> \<open>flip\\_label b.\<close>
    have r2_eq: "?flip_b (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        = ?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)]"
      using assms by simp
    have r2: "top1_valid_scheme_operation
        (w0 @ [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True),(a,False)])
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])"
      unfolding r2_eq[symmetric] by (rule top1_valid_scheme_operation.v_flip_label)
    \<comment> \<open>cut\\_paste\\_opp on b: move ?flip\\_b w0 from before b to after b\\<inverse>.\<close>
    have r3: "top1_valid_scheme_operation
        (?flip_b w0 @ [(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False),(a,False)])
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])"
      using top1_valid_scheme_operation.v_cut_paste_opp
        [of "[]" "?flip_b w0" b "?flip_b w2 @ [(a,True)] @ ?flip_b w1" "[(a,False)]"] by simp
    \<comment> \<open>flip\\_label b back.\<close>
    have hflip_b_invol: "\<And>xs :: ('a \<times> bool) list. ?flip_b (?flip_b xs) = xs"
    proof -
      fix xs :: "('a \<times> bool) list" show "?flip_b (?flip_b xs) = xs"
      proof (induction xs)
        case Nil thus ?case by simp
      next
        case (Cons e xs) obtain l bo where "e = (l, bo)" by (cases e)
        thus ?case using Cons.IH by simp
      qed
    qed
    have r4_eq: "?flip_b ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        = [(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"
      using assms hflip_b_invol by simp
    have r4: "top1_valid_scheme_operation
        ([(b,True)] @ ?flip_b w2 @ [(a,True)] @ ?flip_b w1 @ [(b,False)] @ ?flip_b w0 @ [(a,False)])
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])"
      unfolding r4_eq[symmetric] by (rule top1_valid_scheme_operation.v_flip_label)
    \<comment> \<open>rotate: bring the right part to front.\<close>
    have r5: "top1_valid_scheme_operation
        ([(b,False)] @ w2 @ [(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)])
        ([(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False),(b,False)] @ w2)"
      using top1_valid_scheme_operation.v_rotate
        [of "[(b,False)] @ w2" "[(a,True)] @ w1 @ [(b,True)] @ w0 @ [(a,False)]"] by simp
    from r1 r2 r3 r4 r5 show ?thesis unfolding top1_valid_scheme_equiv_def
      by (by100 simp)
  qed
  \<comment> \<open>Step 4: cut\\_paste\\_opp on b moves w1 from before b to after b\\<inverse>.
     a [w1] b [w0] a\\<inverse> b\\<inverse> w2 \\<to> a b [w0] a\\<inverse> b\\<inverse> [w1] w2.\<close>
  have s4: "top1_valid_scheme_equiv
      ([(a, True)] @ w1 @ [(b, True)] @ w0 @ [(a, False), (b, False)] @ w2)
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)"
    unfolding top1_valid_scheme_equiv_def
    using top1_valid_scheme_operation.v_cut_paste_opp[of "[(a,True)]" w1 b "w0 @ [(a,False)]" w2]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>Step 5: apply Lemma\\_77\\_3\\_w0\\_empty: a b w0 a\\<inverse> b\\<inverse> (w1@w2) ~ a b a\\<inverse> b\\<inverse> w0 w1 w2.\<close>
  have s5: "top1_valid_scheme_equiv
      ([(a, True), (b, True)] @ w0 @ [(a, False), (b, False)] @ w1 @ w2)
      ([(a, True), (b, True), (a, False), (b, False)] @ w0 @ w1 @ w2)"
    using valid_valid_Lemma_77_3_w0_empty[OF assms, of w0 "w1 @ w2"] by (by100 simp)
  from s1 s2 s3 s4 s5 show ?thesis
    using valid_equiv_trans by (by100 blast)
qed

\<comment> \<open>Lemma 77.4 (Munkres): A projective pair + commutator = 3 projective pairs.
   w0 (cc)(aba\\<inverse>b\\<inverse>) w1 ~ w0 (aabbcc) w1.
   Proof: 5-step chain using Lemma 77.1 (*) and rotations.\<close>
\<comment> \<open>Valid version of Lemma 77.4.\<close>
lemma valid_Lemma_77_4_projective_absorbs_torus:
  fixes a b c :: 'a and w0 w1 :: "('a \<times> bool) list"
  assumes "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
      and "\<forall>e \<in> set w0 \<union> set w1. fst e \<noteq> a \<and> fst e \<noteq> b \<and> fst e \<noteq> c"
      and "infinite (UNIV :: 'a set)"
  shows "top1_valid_scheme_equiv
      (w0 @ [(c, True), (c, True), (a, True), (b, True), (a, False), (b, False)] @ w1)
      (w0 @ [(a, True), (a, True), (b, True), (b, True), (c, True), (c, True)] @ w1)"
proof -
  \<comment> \<open>Fresh label d for intermediate steps (needed for 77.1 assumption).\<close>
  have hfin_S: "finite (fst ` (set w0 \<union> set w1) \<union> {a, b, c} :: 'a set)" by simp
  have hinf: "\<not> finite (UNIV :: 'a set)" using assms(5) by simp
  have "\<exists>d :: 'a. d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "UNIV \<subseteq> fst ` (set w0 \<union> set w1) \<union> {a, b, c}" by (by100 blast)
    hence "finite (UNIV :: 'a set)" using hfin_S using finite_subset by (by100 blast)
    with hinf show False by (by100 blast)
  qed
  then obtain d :: 'a where hd: "d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}" by (by100 blast)
  \<comment> \<open>s1: Rotate to front.\<close>
  have s1: "top1_valid_scheme_equiv
      (w0 @ [(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1)
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
      [of w0 "[(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1"]]
    by (by100 simp)
  \<comment> \<open>s2: 77.1 backward (sym) on c: cc ab a\\<inverse>b\\<inverse> w1 w0 ~ ab c ba c w1 w0.\<close>
  have s2: "top1_valid_scheme_equiv
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    \<comment> \<open>Forward 77.1: ab c ba c w1w0 ~ cc ab inv(ba) w1w0.\<close>
    have fwd: "top1_valid_scheme_equiv
        ([(a,True),(b,True)] @ [(c,True)] @ [(b,True),(a,True)] @ [(c,True)] @ (w1 @ w0))
        ([(c,True),(c,True)] @ [(a,True),(b,True)] @ rev (map top1_inverse_edge [(b,True),(a,True)]) @ (w1 @ w0))"
      by (rule valid_Lemma_77_1_projective_collection)
         (use assms hd in \<open>by100 auto\<close>)+
    \<comment> \<open>Simplify the list expressions.\<close>
    have fwd': "top1_valid_scheme_equiv
        ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
        ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
      using fwd unfolding top1_inverse_edge_def by simp
    from valid_equiv_sym[OF fwd'] show ?thesis .
  qed
  \<comment> \<open>s3: 77.1 on b: a b c b (ac w1 w0) ~ bb a c\\<inverse> (ac w1 w0).\<close>
  have s3: "top1_valid_scheme_equiv
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_valid_scheme_equiv
        ([(a,True)] @ [(b,True)] @ [(c,True)] @ [(b,True)] @ ([(a,True),(c,True)] @ w1 @ w0))
        ([(b,True),(b,True)] @ [(a,True)] @ rev (map top1_inverse_edge [(c,True)]) @ ([(a,True),(c,True)] @ w1 @ w0))"
      by (rule valid_Lemma_77_1_projective_collection)
         (use assms hd in \<open>by100 auto\<close>)+
    thus ?thesis unfolding top1_inverse_edge_def by simp
  qed
  \<comment> \<open>s4: 77.1 on a: bb a c\\<inverse> a (c w1 w0) ~ aa bb c c w1 w0.\<close>
  have s4: "top1_valid_scheme_equiv
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_valid_scheme_equiv
        ([(b,True),(b,True)] @ [(a,True)] @ [(c,False)] @ [(a,True)] @ ([(c,True)] @ w1 @ w0))
        ([(a,True),(a,True)] @ [(b,True),(b,True)] @ rev (map top1_inverse_edge [(c,False)]) @ ([(c,True)] @ w1 @ w0))"
      by (rule valid_Lemma_77_1_projective_collection)
         (use assms hd in \<open>by100 auto\<close>)+
    thus ?thesis unfolding top1_inverse_edge_def by simp
  qed
  \<comment> \<open>s5: Rotate back.\<close>
  have s5: "top1_valid_scheme_equiv
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)
      (w0 @ [(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
      [of "[(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1" w0]]
    by (by100 simp)
  \<comment> \<open>Chain.\<close>
  from s1 s2 s3 s4 s5 show ?thesis
    using valid_equiv_trans by (by100 blast)
qed

\<comment> \<open>Lemma\_77\_4\_projective\_absorbs\_torus (OLD): DELETED. Valid version: valid\_Lemma\_77\_4\_projective\_absorbs\_torus.\<close>

\<comment> \<open>Predicate: a scheme w is the standard n-fold torus scheme
   a1 b1 a1\\<inverse> b1\\<inverse> ... an bn an\\<inverse> bn\\<inverse> (4n edges). (Moved before scheme\\_normal\\_form.)\<close>
definition top1_is_torus_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_torus_scheme w n \<longleftrightarrow> n > 0 \<and> w = top1_n_torus_scheme n"

\<comment> \<open>Predicate: a scheme w is the standard m-fold projective scheme
   a1 a1 a2 a2 ... am am (2m edges). (Moved before scheme\\_normal\\_form.)\<close>
definition top1_is_projective_scheme :: "(nat \<times> bool) list \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_projective_scheme w m \<longleftrightarrow> m > 0 \<and> w = top1_m_projective_scheme m"

\<comment> \<open>Position-to-element: if xs = prefix @ mid @ suffix and k < length xs
   and k < length prefix or k \<ge> length prefix + length mid,
   then xs!k \<in> set prefix \<union> set suffix.\<close>
lemma nth_outside_mid:
  assumes "xs = prefix @ mid @ suffix"
      and "k < length xs"
      and "k < length prefix \<or> k \<ge> length prefix + length mid"
  shows "xs ! k \<in> set prefix \<union> set suffix"
  using assms
proof (elim disjE)
  assume hk_pf: "k < length prefix"
  have "xs ! k = (prefix @ mid @ suffix) ! k" using assms(1) by (by100 simp)
  also have "\<dots> = prefix ! k"
    using nth_append[of prefix "mid @ suffix" k] hk_pf by (by100 simp)
  finally have "xs ! k = prefix ! k" .
  have "prefix ! k \<in> set prefix" using hk_pf by (by100 simp)
  hence "xs ! k \<in> set prefix" using \<open>xs ! k = prefix ! k\<close> by (by100 simp)
  thus ?thesis by (by100 blast)
next
  assume hk_sf: "k \<ge> length prefix + length mid"
  have hk_off: "k - length prefix - length mid < length suffix"
    using assms(1,2) hk_sf by (by100 simp)
  have "xs ! k = (prefix @ mid @ suffix) ! k" using assms(1) by (by100 simp)
  also have "\<dots> = (mid @ suffix) ! (k - length prefix)"
  proof -
    have "\<not> k < length prefix" using hk_sf by (by100 simp)
    thus ?thesis using nth_append[of prefix "mid @ suffix" k] by (by100 simp)
  qed
  also have "\<dots> = suffix ! (k - length prefix - length mid)"
  proof -
    have "\<not> k - length prefix < length mid" using hk_sf by (by100 simp)
    thus ?thesis using nth_append[of mid suffix "k - length prefix"] by (by100 simp)
  qed
  finally have "xs ! k = suffix ! (k - length prefix - length mid)" .
  have "suffix ! (k - length prefix - length mid) \<in> set suffix"
    using hk_off by (by100 simp)
  hence "xs ! k \<in> set suffix"
    using \<open>xs ! k = suffix ! (k - length prefix - length mid)\<close> by (by100 simp)
  thus ?thesis by (by100 blast)
qed

\<comment> \<open>Helper: in a proper length-4 torus-type scheme, the two non-adjacent-pair elements
   have the same label but opposite directions.\<close>
lemma proper_len4_torus_pair_props:
  fixes scheme :: "(nat \<times> bool) list" and e1 e2 :: "nat \<times> bool"
      and prefix suffix :: "(nat \<times> bool) list"
  assumes hlen: "length scheme = 4"
      and htorus: "\<not> (\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))"
      and hfst_eq: "fst e1 = fst e2"
      and hi: "i < 3" "fst (scheme!i) = fst (scheme!(i+1))"
      and hdecomp: "scheme = prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix"
      and hlen_pf: "length prefix = i"
      and hsp: "suffix @ prefix = [e1, e2]"
  shows "snd e1 \<noteq> snd e2"
proof -
  \<comment> \<open>Construct 2 concrete non-{i,i+1} positions.\<close>
  define p0 :: nat where "p0 = (if i = 0 then 2 else 0)"
  define p1 :: nat where "p1 = (if i \<le> 1 then 3 else 1)"
  have hp0: "p0 < 4" "p0 \<noteq> i" "p0 \<noteq> i + 1"
    using hi(1) unfolding p0_def by (by100 simp)+
  have hp1: "p1 < 4" "p1 \<noteq> i" "p1 \<noteq> i + 1"
    using hi(1) unfolding p1_def by (by100 simp)+
  have hp0p1: "p0 \<noteq> p1"
    using hi(1) unfolding p0_def p1_def by (by100 simp)
  \<comment> \<open>scheme!p0 and scheme!p1 are in set prefix \<union> set suffix.\<close>
  have hp0_in: "scheme!p0 \<in> set prefix \<union> set suffix"
  proof -
    have hmid_len: "length [scheme!i, top1_inverse_edge (scheme!i)] = 2" by (by100 simp)
    have hcond: "p0 < length prefix \<or> p0 \<ge> length prefix + length [scheme!i, top1_inverse_edge (scheme!i)]"
      using hp0(2,3) hp0(1) hi(1) hlen_pf hmid_len by (by100 presburger)
    have "p0 < length scheme" using hp0(1) hlen by (by100 simp)
    from nth_outside_mid[OF hdecomp this hcond]
    show ?thesis .
  qed
  have hp1_in: "scheme!p1 \<in> set prefix \<union> set suffix"
  proof -
    have hmid_len1: "length [scheme!i, top1_inverse_edge (scheme!i)] = 2" by (by100 simp)
    have hcond: "p1 < length prefix \<or> p1 \<ge> length prefix + length [scheme!i, top1_inverse_edge (scheme!i)]"
      using hp1(2,3) hp1(1) hi(1) hlen_pf hmid_len1 by (by100 presburger)
    have "p1 < length scheme" using hp1(1) hlen by (by100 simp)
    from nth_outside_mid[OF hdecomp this hcond]
    show ?thesis .
  qed
  \<comment> \<open>Elements of prefix \<union> suffix = {e1, e2}.\<close>
  have hsp_set: "\<forall>x \<in> set prefix \<union> set suffix. x = e1 \<or> x = e2"
  proof (rule ballI)
    fix x assume "x \<in> set prefix \<union> set suffix"
    hence "x \<in> set suffix \<or> x \<in> set prefix" by (by100 blast)
    hence "x \<in> set (suffix @ prefix)" by (by100 simp)
    hence "x \<in> set [e1, e2]" using hsp by (by100 simp)
    thus "x = e1 \<or> x = e2" by (by100 simp)
  qed
  have hp0_e: "scheme!p0 = e1 \<or> scheme!p0 = e2" using hp0_in hsp_set by (by100 blast)
  have hp1_e: "scheme!p1 = e1 \<or> scheme!p1 = e2" using hp1_in hsp_set by (by100 blast)
  \<comment> \<open>Both have label fst e1.\<close>
  have hlab_p0: "fst (scheme!p0) = fst e1"
    using hp0_e hfst_eq
    proof (elim disjE)
      assume "scheme!p0 = e1" thus ?thesis by (by100 simp)
    next
      assume "scheme!p0 = e2" thus ?thesis using hfst_eq by (by100 simp)
    qed
  have hlab_p1: "fst (scheme!p1) = fst e1"
    using hp1_e hfst_eq
    proof (elim disjE)
      assume "scheme!p1 = e1" thus ?thesis by (by100 simp)
    next
      assume "scheme!p1 = e2" thus ?thesis using hfst_eq by (by100 simp)
    qed
  \<comment> \<open>Torus: p0 \<noteq> p1, same label \<Longrightarrow> different direction.\<close>
  have hsnd_ne: "snd (scheme!p0) \<noteq> snd (scheme!p1)"
  proof
    assume "snd (scheme!p0) = snd (scheme!p1)"
    hence "\<exists>lab. \<exists>p<length scheme. \<exists>q<length scheme. p \<noteq> q
        \<and> fst (scheme!p) = lab \<and> fst (scheme!q) = lab
        \<and> snd (scheme!p) = snd (scheme!q)"
    proof -
      have "p0 < length scheme" using hp0(1) hlen by (by100 simp)
      moreover have "p1 < length scheme" using hp1(1) hlen by (by100 simp)
      ultimately show ?thesis
        using hp0p1 hlab_p0 hlab_p1 \<open>snd (scheme!p0) = snd (scheme!p1)\<close>
        by (by100 blast)
    qed
    thus False using htorus by (by100 blast)
  qed
  \<comment> \<open>Since scheme!p0 \<in> {e1,e2} and scheme!p1 \<in> {e1,e2} and snd differ,
     the set {scheme!p0, scheme!p1} = {e1, e2}.\<close>
  show "snd e1 \<noteq> snd e2"
  proof (rule ccontr)
    assume "\<not> snd e1 \<noteq> snd e2"
    hence hsame: "snd e1 = snd e2" by (by100 simp)
    \<comment> \<open>Then e1 = e2 (same fst, same snd). All elements in {e1, e2} = {e1} have same snd.
       scheme!p0 and scheme!p1 are both in {e1}, so snd equal. Contradicts hsnd\_ne.\<close>
    have "e1 = e2" using hfst_eq hsame
    proof (cases e1, cases e2)
      fix a1 b1 a2 b2
      assume "e1 = (a1, b1)" "e2 = (a2, b2)"
      thus ?thesis using hfst_eq hsame by (by100 simp)
    qed
    hence "snd (scheme!p0) = snd (scheme!p1)"
    proof -
      from hp0_e have "scheme!p0 = e1 \<or> scheme!p0 = e2" .
      hence "snd (scheme!p0) = snd e1"
      proof (elim disjE)
        assume "scheme!p0 = e1" thus ?thesis by (by100 simp)
      next
        assume "scheme!p0 = e2" thus ?thesis using \<open>e1 = e2\<close> by (by100 simp)
      qed
      moreover from hp1_e have "snd (scheme!p1) = snd e1"
      proof (elim disjE)
        assume "scheme!p1 = e1" thus ?thesis by (by100 simp)
      next
        assume "scheme!p1 = e2" thus ?thesis using \<open>e1 = e2\<close> by (by100 simp)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    thus False using hsnd_ne by (by100 simp)
  qed
qed

\<comment> \<open>Nth element of projective scheme: position 2k and 2k+1 both have label k.\<close>
lemma projective_scheme_nth_even:
  assumes "k < m"
  shows "(top1_m_projective_scheme m) ! (2*k) = (k, True)"
  using assms
proof (induct m)
  case 0 thus ?case by (by100 simp)
next
  case (Suc n)
  show ?case
  proof (cases "k < n")
    case True
    \<comment> \<open>IH: (proj n) ! (2*k) = (k, True). proj (Suc n) = proj n @ [(n,T),(n,T)].\<close>
    have "top1_m_projective_scheme (Suc n) = top1_m_projective_scheme n @ [(n, True), (n, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    moreover have h2k: "2*k < length (top1_m_projective_scheme n)"
      using True projective_scheme_length by (by100 simp)
    ultimately have "(top1_m_projective_scheme (Suc n)) ! (2*k) = (top1_m_projective_scheme n) ! (2*k)"
      using nth_append[of "top1_m_projective_scheme n" _ "2*k"] h2k by (by100 simp)
    thus ?thesis using Suc(1)[OF True] by (by100 simp)
  next
    case False
    hence "k = n" using Suc(2) by (by100 simp)
    have "top1_m_projective_scheme (Suc n) = top1_m_projective_scheme n @ [(n, True), (n, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    moreover have "length (top1_m_projective_scheme n) = 2 * n"
      using projective_scheme_length by (by100 blast)
    ultimately have "(top1_m_projective_scheme (Suc n)) ! (2*n) = (n, True)"
    proof -
      assume happ: "top1_m_projective_scheme (Suc n) = top1_m_projective_scheme n @ [(n, True), (n, True)]"
        and hlen_n: "length (top1_m_projective_scheme n) = 2 * n"
      have "\<not> 2*n < 2*n" by (by100 simp)
      hence "(top1_m_projective_scheme n @ [(n, True), (n, True)]) ! (2*n) = [(n, True), (n, True)] ! (2*n - 2*n)"
        using nth_append[of "top1_m_projective_scheme n" "[(n,True),(n,True)]" "2*n"] hlen_n
        by (by100 simp)
      also have "\<dots> = (n, True)" by (by100 simp)
      finally show ?thesis using happ by (by100 simp)
    qed
    thus ?thesis using \<open>k = n\<close> by (by100 simp)
  qed
qed

lemma projective_scheme_nth_odd:
  assumes "k < m"
  shows "(top1_m_projective_scheme m) ! (2*k+1) = (k, True)"
  using assms
proof (induct m)
  case 0 thus ?case by (by100 simp)
next
  case (Suc n)
  show ?case
  proof (cases "k < n")
    case True
    have "top1_m_projective_scheme (Suc n) = top1_m_projective_scheme n @ [(n, True), (n, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    moreover have h2k1: "2*k+1 < length (top1_m_projective_scheme n)"
      using True projective_scheme_length by (by100 simp)
    ultimately have "(top1_m_projective_scheme (Suc n)) ! (2*k+1) = (top1_m_projective_scheme n) ! (2*k+1)"
      using nth_append[of "top1_m_projective_scheme n" _ "2*k+1"] h2k1 by (by100 simp)
    thus ?thesis using Suc(1)[OF True] by (by100 simp)
  next
    case False
    hence "k = n" using Suc(2) by (by100 simp)
    have happ: "top1_m_projective_scheme (Suc n) = top1_m_projective_scheme n @ [(n, True), (n, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    have hlen_n: "length (top1_m_projective_scheme n) = 2 * n"
      using projective_scheme_length by (by100 blast)
    have "(top1_m_projective_scheme (Suc n)) ! (2*n+1) = (n, True)"
    proof -
      have "\<not> 2*n+1 < 2*n" by (by100 simp)
      hence "(top1_m_projective_scheme n @ [(n, True), (n, True)]) ! (2*n+1) = [(n, True), (n, True)] ! (2*n+1 - 2*n)"
        using nth_append[of "top1_m_projective_scheme n" "[(n,True),(n,True)]" "2*n+1"] hlen_n
        by (by100 simp)
      also have "2*n+1 - 2*n = (1::nat)" by (by100 simp)
      also have "[(n, True), (n, True)] ! 1 = (n, True)" by (by100 simp)
      finally show ?thesis using happ by (by100 simp)
    qed
    thus ?thesis using \<open>k = n\<close> by (by100 simp)
  qed
qed

\<comment> \<open>Fst of any element of projective scheme is < m.\<close>
lemma projective_scheme_fst_bound:
  assumes "j < length (top1_m_projective_scheme m)"
  shows "fst ((top1_m_projective_scheme m) ! j) < m"
proof -
  have hlen: "length (top1_m_projective_scheme m) = 2 * m"
    using projective_scheme_length by (by100 blast)
  hence hj: "j < 2 * m" using assms by (by100 simp)
  define k where "k = j div 2"
  have hk: "k < m" using hj unfolding k_def by (by100 simp)
  have "j = 2*k \<or> j = 2*k+1" unfolding k_def by (by100 presburger)
  thus ?thesis
  proof (elim disjE)
    assume "j = 2*k"
    hence "(top1_m_projective_scheme m) ! j = (k, True)"
      using projective_scheme_nth_even[OF hk] by (by100 simp)
    thus ?thesis using hk by (by100 simp)
  next
    assume "j = 2*k+1"
    hence "(top1_m_projective_scheme m) ! j = (k, True)"
      using projective_scheme_nth_odd[OF hk] by (by100 simp)
    thus ?thesis using hk by (by100 simp)
  qed
qed

\<comment> \<open>Properness of the projective normal-form scheme: each label appears exactly twice.\<close>
lemma projective_scheme_proper:
  assumes "m > 0"
  shows "\<forall>label. card {i. i < length (top1_m_projective_scheme m) \<and>
      fst ((top1_m_projective_scheme m) ! i) = label} \<in> {0, 2}"
proof (intro allI)
  fix label :: nat
  let ?w = "top1_m_projective_scheme m"
  show "card {i. i < length ?w \<and> fst (?w ! i) = label} \<in> {0, 2}"
  proof (cases "label < m")
    case True
    have hset: "{i. i < length ?w \<and> fst (?w ! i) = label} = {2*label, 2*label+1}"
    proof (rule set_eqI, rule iffI)
      fix i assume hi_in: "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      hence hi: "i < length ?w" "fst (?w ! i) = label" by (by100 simp)+
      \<comment> \<open>i div 2 = label.\<close>
      define k where "k = i div 2"
      have "i < 2 * m" using hi(1) projective_scheme_length by (by100 simp)
      hence hk: "k < m" unfolding k_def by (by100 simp)
      have "i = 2*k \<or> i = 2*k+1" unfolding k_def by (by100 presburger)
      hence "fst (?w ! i) = k"
      proof (elim disjE)
        assume "i = 2*k" thus ?thesis using projective_scheme_nth_even[OF hk] by (by100 simp)
      next
        assume "i = 2*k+1" thus ?thesis using projective_scheme_nth_odd[OF hk] by (by100 simp)
      qed
      hence "k = label" using hi(2) by (by100 simp)
      hence "i = 2*label \<or> i = 2*label+1" unfolding k_def by (by100 presburger)
      thus "i \<in> {2*label, 2*label+1}" by (by100 blast)
    next
      fix i assume "i \<in> {2*label, 2*label+1}"
      hence "i = 2*label \<or> i = 2*label+1" by (by100 blast)
      thus "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      proof (elim disjE)
        assume "i = 2*label"
        hence "?w ! i = (label, True)" using projective_scheme_nth_even[OF True] by (by100 simp)
        moreover have "i < length ?w" using True projective_scheme_length \<open>i = 2*label\<close> by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      next
        assume "i = 2*label+1"
        hence "?w ! i = (label, True)" using projective_scheme_nth_odd[OF True] by (by100 simp)
        moreover have "i < length ?w" using True projective_scheme_length \<open>i = 2*label+1\<close> by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
    qed
    have "card {2*label, 2*label+1::nat} = 2" by (by100 simp)
    thus ?thesis using hset by (by100 simp)
  next
    case False
    have "{i. i < length ?w \<and> fst (?w ! i) = label} = {}"
    proof (rule equals0I)
      fix i assume "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      hence "i < length ?w" "fst (?w ! i) = label" by (by100 simp)+
      from projective_scheme_fst_bound[OF this(1)] this(2) False
      show False by (by100 simp)
    qed
    thus ?thesis by (by100 simp)
  qed
qed

\<comment> \<open>Properness of the torus normal-form scheme: each label appears exactly twice.\<close>
lemma torus_scheme_length: "length (top1_n_torus_scheme n) = 4 * n"
  unfolding top1_n_torus_scheme_def by (induct n) (by100 simp)+

lemma torus_scheme_fst_bound:
  assumes "j < length (top1_n_torus_scheme n)"
  shows "fst ((top1_n_torus_scheme n) ! j) < 2 * n"
proof -
  have hj: "j < 4 * n" using assms torus_scheme_length by (by100 simp)
  define k where "k = j div 4"
  have hk: "k < n" using hj unfolding k_def by (by100 simp)
  define r where "r = j mod 4"
  have hr: "r < 4" unfolding r_def by (by100 simp)
  have hj_eq: "j = 4*k + r" unfolding k_def r_def by (by100 presburger)
  \<comment> \<open>Case-split on r \<in> {0,1,2,3}.\<close>
  from hr have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" by (by100 presburger)
  thus ?thesis
  proof (elim disjE)
    assume "r = 0"
    hence "j = 4*k" using hj_eq by (by100 simp)
    hence "fst ((top1_n_torus_scheme n) ! j) = fst ((top1_n_torus_scheme n) ! (4*k))" by (by100 simp)
    also have "\<dots> = 2*k" using torus_scheme_nth(1)[OF hk] by (by100 simp)
    finally show ?thesis using hk by (by100 simp)
  next
    assume "r = 1"
    hence "j = 4*k + 1" using hj_eq by (by100 simp)
    hence "fst ((top1_n_torus_scheme n) ! j) = fst ((top1_n_torus_scheme n) ! (4*k+1))" by (by100 simp)
    also have "\<dots> = 2*k+1" using torus_scheme_nth(2)[OF hk] by (by100 simp)
    finally show ?thesis using hk by (by100 simp)
  next
    assume "r = 2"
    hence "j = 4*k + 2" using hj_eq by (by100 simp)
    hence "fst ((top1_n_torus_scheme n) ! j) = fst ((top1_n_torus_scheme n) ! (4*k+2))" by (by100 simp)
    also have "\<dots> = 2*k" using torus_scheme_nth(3)[OF hk] by (by100 simp)
    finally show ?thesis using hk by (by100 simp)
  next
    assume "r = 3"
    hence "j = 4*k + 3" using hj_eq by (by100 simp)
    hence "fst ((top1_n_torus_scheme n) ! j) = fst ((top1_n_torus_scheme n) ! (4*k+3))" by (by100 simp)
    also have "\<dots> = 2*k+1" using torus_scheme_nth(4)[OF hk] by (by100 simp)
    finally show ?thesis using hk by (by100 simp)
  qed
qed

lemma torus_scheme_proper:
  assumes "n > 0"
  shows "\<forall>label. card {i. i < length (top1_n_torus_scheme n) \<and>
      fst ((top1_n_torus_scheme n) ! i) = label} \<in> {0, 2}"
proof (intro allI)
  fix label :: nat
  let ?w = "top1_n_torus_scheme n"
  show "card {i. i < length ?w \<and> fst (?w ! i) = label} \<in> {0, 2}"
  proof (cases "label < 2 * n")
    case True
    \<comment> \<open>Label appears at exactly 2 positions: determined by label mod 2 and label div 2.\<close>
    define k where "k = label div 2"
    have hk: "k < n" using True unfolding k_def by (by100 simp)
    \<comment> \<open>If label is even (label = 2*k): positions 4*k and 4*k+2.
       If label is odd (label = 2*k+1): positions 4*k+1 and 4*k+3.\<close>
    have hset: "{i. i < length ?w \<and> fst (?w ! i) = label} =
        (if even label then {4*k, 4*k+2} else {4*k+1, 4*k+3})"
    proof (rule set_eqI, rule iffI)
      fix i assume hi_in: "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      hence hi: "i < length ?w" "fst (?w ! i) = label" by (by100 simp)+
      define k' where "k' = i div 4"
      define r where "r = i mod 4"
      have hi4: "i < 4*n" using hi(1) torus_scheme_length by (by100 simp)
      have hk': "k' < n" using hi4 unfolding k'_def by (by100 simp)
      have hr: "r < 4" unfolding r_def by (by100 simp)
      have hi_eq: "i = 4*k' + r" unfolding k'_def r_def by (by100 presburger)
      \<comment> \<open>From fst(?w!i) = label and torus\_scheme\_nth, determine k' and r.\<close>
      from hr have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" by (by100 presburger)
      hence hk'_eq: "k' = k \<and> (if even label then i = 4*k \<or> i = 4*k+2 else i = 4*k+1 \<or> i = 4*k+3)"
      proof (elim disjE)
        assume "r = 0"
        hence "i = 4*k'" using hi_eq by (by100 simp)
        hence "fst (?w ! (4*k')) = label" using hi(2) by (by100 simp)
        hence "2*k' = label" using torus_scheme_nth(1)[OF hk'] by (by100 simp)
        hence "k' = k" unfolding k_def by (by100 presburger)
        moreover have "i = 4*k" using \<open>i = 4*k'\<close> \<open>k' = k\<close> by (by100 simp)
        moreover have "even label" using \<open>2*k' = label\<close> by (by100 presburger)
        ultimately show ?thesis by (by100 simp)
      next
        assume "r = 1"
        hence "i = 4*k'+1" using hi_eq by (by100 simp)
        hence "fst (?w ! (4*k'+1)) = label" using hi(2) by (by100 simp)
        hence "2*k'+1 = label" using torus_scheme_nth(2)[OF hk'] by (by100 simp)
        hence "k' = k" unfolding k_def by (by100 presburger)
        moreover have "i = 4*k+1" using \<open>i = 4*k'+1\<close> \<open>k' = k\<close> by (by100 simp)
        moreover have "odd label" using \<open>2*k'+1 = label\<close> by (by100 presburger)
        ultimately show ?thesis by (by100 simp)
      next
        assume "r = 2"
        hence "i = 4*k'+2" using hi_eq by (by100 simp)
        hence "fst (?w ! (4*k'+2)) = label" using hi(2) by (by100 simp)
        hence "2*k' = label" using torus_scheme_nth(3)[OF hk'] by (by100 simp)
        hence "k' = k" unfolding k_def by (by100 presburger)
        moreover have "i = 4*k+2" using \<open>i = 4*k'+2\<close> \<open>k' = k\<close> by (by100 simp)
        moreover have "even label" using \<open>2*k' = label\<close> by (by100 presburger)
        ultimately show ?thesis by (by100 simp)
      next
        assume "r = 3"
        hence "i = 4*k'+3" using hi_eq by (by100 simp)
        hence "fst (?w ! (4*k'+3)) = label" using hi(2) by (by100 simp)
        hence "2*k'+1 = label" using torus_scheme_nth(4)[OF hk'] by (by100 simp)
        hence "k' = k" unfolding k_def by (by100 presburger)
        moreover have "i = 4*k+3" using \<open>i = 4*k'+3\<close> \<open>k' = k\<close> by (by100 simp)
        moreover have "odd label" using \<open>2*k'+1 = label\<close> by (by100 presburger)
        ultimately show ?thesis by (by100 simp)
      qed
      show "i \<in> (if even label then {4*k, 4*k+2} else {4*k+1, 4*k+3})"
      proof (cases "even label")
        case True thus ?thesis using hk'_eq by (by100 simp)
      next
        case False thus ?thesis using hk'_eq by (by100 simp)
      qed
    next
      fix i assume hi_rhs: "i \<in> (if even label then {4*k, 4*k+2} else {4*k+1, 4*k+3})"
      show "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      proof (cases "even label")
        case True
        hence "i = 4*k \<or> i = 4*k+2" using hi_rhs by (by100 simp)
        thus ?thesis
        proof (elim disjE)
          assume "i = 4*k"
          hence "?w ! i = (2*k, True)" using torus_scheme_nth(1)[OF hk] by (by100 simp)
          moreover have "label = 2*k" using True k_def by (by100 simp)
          moreover have "i < length ?w" using hk torus_scheme_length \<open>i = 4*k\<close> by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        next
          assume "i = 4*k+2"
          hence "?w ! i = (2*k, False)" using torus_scheme_nth(3)[OF hk] by (by100 simp)
          moreover have "label = 2*k" using True k_def by (by100 simp)
          moreover have "i < length ?w" using hk torus_scheme_length \<open>i = 4*k+2\<close> by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      next
        case False
        hence "i = 4*k+1 \<or> i = 4*k+3" using hi_rhs by (by100 simp)
        thus ?thesis
        proof (elim disjE)
          assume "i = 4*k+1"
          hence "?w ! i = (2*k+1, True)" using torus_scheme_nth(2)[OF hk] by (by100 simp)
          moreover have "label = 2*k+1" using False k_def by (by100 simp)
          moreover have "i < length ?w" using hk torus_scheme_length \<open>i = 4*k+1\<close> by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        next
          assume "i = 4*k+3"
          hence "?w ! i = (2*k+1, False)" using torus_scheme_nth(4)[OF hk] by (by100 simp)
          moreover have "label = 2*k+1" using False k_def by (by100 simp)
          moreover have "i < length ?w" using hk torus_scheme_length \<open>i = 4*k+3\<close> by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    qed
    moreover have "card (if even label then {4*k, 4*k+2} else {4*k+1, 4*k+3}) = 2"
      by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  next
    case False
    have "{i. i < length ?w \<and> fst (?w ! i) = label} = {}"
    proof (rule equals0I)
      fix i assume "i \<in> {i. i < length ?w \<and> fst (?w ! i) = label}"
      hence "i < length ?w" "fst (?w ! i) = label" by (by100 simp)+
      from torus_scheme_fst_bound[OF this(1)] this(2) False
      show False by (by100 simp)
    qed
    thus ?thesis by (by100 simp)
  qed
qed

\<comment> \<open>Cancelling a matched pair preserves properness.\<close>
lemma cancel_preserves_proper:
  fixes w :: "('a \<times> bool) list"
  assumes hproper: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
      and hj: "j + 1 < length w"
      and hpair: "fst (w ! j) = fst (w ! (j+1))"
  shows "\<forall>label. card {i. i < length (take j w @ drop (j+2) w)
      \<and> fst ((take j w @ drop (j+2) w) ! i) = label} \<in> {0, 2}"
proof -
  let ?w' = "take j w @ drop (j+2) w"
  let ?lab_j = "fst (w ! j)"
  \<comment> \<open>Key fact: the only positions in w with label ?lab\_j are j and j+1.\<close>
  have honly_jj1: "{k. k < length w \<and> fst (w ! k) = ?lab_j} = {j, j+1}"
  proof -
    have hj_in: "j \<in> {k. k < length w \<and> fst (w ! k) = ?lab_j}" using hj by (by100 simp)
    have hj1_in: "j+1 \<in> {k. k < length w \<and> fst (w ! k) = ?lab_j}"
      using hj hpair by (by100 simp)
    have hcard: "card {k. k < length w \<and> fst (w ! k) = ?lab_j} = 2"
    proof -
      from hproper have "card {k. k < length w \<and> fst (w ! k) = ?lab_j} \<in> {0, 2}" by (by100 blast)
      moreover have "{k. k < length w \<and> fst (w ! k) = ?lab_j} \<noteq> {}" using hj_in by (by100 blast)
      hence "card {k. k < length w \<and> fst (w ! k) = ?lab_j} \<noteq> 0" by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    have hfin: "finite {k. k < length w \<and> fst (w ! k) = ?lab_j}" by (by100 simp)
    have hsub: "{j, j+1} \<subseteq> {k. k < length w \<and> fst (w ! k) = ?lab_j}"
      using hj_in hj1_in by (by100 blast)
    have hcard2: "card {j, j+1} = 2" by (by100 simp)
    from card_seteq[OF hfin hsub] hcard hcard2
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Nth of w': for i < j, w'!i = w!i. For i \<ge> j, w'!i = w!(i+2).\<close>
  have hlen_w': "length ?w' = length w - 2" using hj by (by100 simp)
  have hnth_lt: "\<forall>i. i < j \<longrightarrow> ?w' ! i = w ! i"
  proof (intro allI impI)
    fix i assume "i < j"
    hence "i < length (take j w)" using hj by (by100 simp)
    thus "?w' ! i = w ! i"
      using nth_append[of "take j w" "drop (j+2) w" i] by (by100 simp)
  qed
  have hnth_ge: "\<forall>i. j \<le> i \<longrightarrow> i < length ?w' \<longrightarrow> ?w' ! i = w ! (i+2)"
  proof (intro allI impI)
    fix i assume "j \<le> i" "i < length ?w'"
    have "\<not> i < length (take j w)" using \<open>j \<le> i\<close> hj by (by100 simp)
    hence "?w' ! i = (drop (j+2) w) ! (i - j)"
      using nth_append[of "take j w" "drop (j+2) w" i] hj by (by100 simp)
    also have "\<dots> = w ! (j + 2 + (i - j))"
      using nth_drop \<open>i < length ?w'\<close> hj \<open>j \<le> i\<close> by (by100 simp)
    also have "j + 2 + (i - j) = i + 2" using \<open>j \<le> i\<close> by (by100 simp)
    finally show "?w' ! i = w ! (i + 2)" .
  qed
  \<comment> \<open>Now prove for each label.\<close>
  show ?thesis
  proof (intro allI)
    fix label :: 'a
    show "card {i. i < length ?w' \<and> fst (?w' ! i) = label} \<in> {0, 2}"
    proof (cases "label = ?lab_j")
      case True
      have "{i. i < length ?w' \<and> fst (?w' ! i) = label} = {}"
      proof (rule equals0I)
        fix i assume "i \<in> {i. i < length ?w' \<and> fst (?w' ! i) = label}"
        hence hi: "i < length ?w'" "fst (?w' ! i) = label" by (by100 simp)+
        show False
        proof (cases "i < j")
          case True
          hence "?w' ! i = w ! i" using hnth_lt by (by100 blast)
          hence "fst (w ! i) = label" using hi(2) by (by100 simp)
          hence "fst (w ! i) = ?lab_j" using \<open>label = ?lab_j\<close> by (by100 simp)
          hence "i \<in> {k. k < length w \<and> fst (w ! k) = ?lab_j}"
            using hi(1) hlen_w' hj True by (by100 simp)
          hence "i \<in> {j, j+1}" using honly_jj1 by (by100 blast)
          thus False using True by (by100 simp)
        next
          case False
          hence "j \<le> i" by (by100 simp)
          hence "?w' ! i = w ! (i+2)" using hnth_ge hi(1) by (by100 blast)
          hence "fst (w ! (i+2)) = ?lab_j" using hi(2) \<open>label = ?lab_j\<close> by (by100 simp)
          have "i + 2 < length w" using hi(1) hlen_w' hj by (by100 simp)
          hence "i+2 \<in> {k. k < length w \<and> fst (w ! k) = ?lab_j}"
            using \<open>fst (w ! (i+2)) = ?lab_j\<close> by (by100 simp)
          hence "i+2 \<in> {j, j+1}" using honly_jj1 by (by100 blast)
          hence "i+2 = j \<or> i+2 = j+1" by (by100 blast)
          thus False using \<open>j \<le> i\<close> by (by100 simp)
        qed
      qed
      thus ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>Other label: bijection between positions in w and w'.\<close>
      \<comment> \<open>No position in w with label = label is at j or j+1 (since label \<noteq> ?lab\_j).\<close>
      have hno_jj1: "\<forall>k. k < length w \<longrightarrow> fst (w ! k) = label \<longrightarrow> k \<noteq> j \<and> k \<noteq> j+1"
      proof (intro allI impI)
        fix k assume hk: "k < length w" "fst (w ! k) = label"
        have "k \<noteq> j"
        proof
          assume "k = j"
          hence "label = ?lab_j" using hk(2) by (by100 simp)
          thus False using False by (by100 simp)
        qed
        moreover have "k \<noteq> j+1"
        proof
          assume "k = j+1"
          hence "fst (w ! (j+1)) = label" using hk(2) by (by100 simp)
          hence "label = ?lab_j" using hpair by (by100 simp)
          thus False using False by (by100 simp)
        qed
        ultimately show "k \<noteq> j \<and> k \<noteq> j+1" by (by100 blast)
      qed
      \<comment> \<open>Bijection: map i in w to i (if i<j) or i-2 (if i>j+1) in w'.\<close>
      let ?f = "\<lambda>i. if i < j then i else i - 2"
      have "bij_betw ?f {i. i < length w \<and> fst (w ! i) = label}
          {i. i < length ?w' \<and> fst (?w' ! i) = label}"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on ?f {i. i < length w \<and> fst (w ! i) = label}"
        proof (rule inj_onI)
          fix x y
          assume hx: "x \<in> {i. i < length w \<and> fst (w ! i) = label}"
            and hy: "y \<in> {i. i < length w \<and> fst (w ! i) = label}"
            and heq: "?f x = ?f y"
          from hno_jj1 hx have "x \<noteq> j" "x \<noteq> j+1" by (by100 blast)+
          from hno_jj1 hy have "y \<noteq> j" "y \<noteq> j+1" by (by100 blast)+
          \<comment> \<open>Case split: both < j, both \<ge> j+2, or mixed.\<close>
          have "x < j \<or> x \<ge> j+2" using \<open>x \<noteq> j\<close> \<open>x \<noteq> j+1\<close> by (by100 presburger)
          moreover have "y < j \<or> y \<ge> j+2" using \<open>y \<noteq> j\<close> \<open>y \<noteq> j+1\<close> by (by100 presburger)
          ultimately show "x = y" using heq
          proof (elim disjE conjE)
            assume "x < j" "y < j" thus "x = y" using heq by (by100 simp)
          next
            assume "x < j" "y \<ge> j+2" thus "x = y" using heq by (by100 simp)
          next
            assume "x \<ge> j+2" "y < j" thus "x = y" using heq by (by100 simp)
          next
            assume "x \<ge> j+2" "y \<ge> j+2" thus "x = y" using heq by (by100 simp)
          qed
        qed
        show "?f ` {i. i < length w \<and> fst (w ! i) = label}
            = {i. i < length ?w' \<and> fst (?w' ! i) = label}"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> ?f ` {i. i < length w \<and> fst (w ! i) = label}"
          then obtain x where hx: "x < length w" "fst (w ! x) = label" "y = ?f x"
            by (by100 blast)
          from hno_jj1 hx(1,2) have "x \<noteq> j" "x \<noteq> j+1" by (by100 blast)+
          hence hx_cases: "x < j \<or> x \<ge> j+2" by (by100 presburger)
          show "y \<in> {i. i < length ?w' \<and> fst (?w' ! i) = label}"
          proof (cases "x < j")
            case True
            hence hy_eq: "y = x" using hx(3) by (by100 simp)
            have "?w' ! x = w ! x" using hnth_lt True by (by100 blast)
            hence "fst (?w' ! x) = fst (w ! x)" by (by100 simp)
            hence "fst (?w' ! y) = label" using hy_eq hx(2) by (by100 simp)
            moreover have "y < length ?w'" using hx(1) hlen_w' hj True hy_eq by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          next
            case False
            hence "x \<ge> j + 2" using hx_cases by (by100 blast)
            hence "y = x - 2" using hx(3) by (by100 simp)
            moreover have "x - 2 < length ?w'" using hx(1) hlen_w' hj \<open>x \<ge> j+2\<close> by (by100 simp)
            moreover have "x - 2 \<ge> j" using \<open>x \<ge> j+2\<close> by (by100 simp)
            from hnth_ge[rule_format, OF \<open>x - 2 \<ge> j\<close> \<open>x - 2 < length ?w'\<close>]
            have "?w' ! (x-2) = w ! ((x-2)+2)" .
            hence "fst (?w' ! (x-2)) = fst (w ! (x-2+2))" by (by100 simp)
            have "x - 2 + 2 = x" using \<open>x \<ge> j+2\<close> by (by100 simp)
            hence "fst (?w' ! (x-2)) = fst (w ! x)"
              using \<open>fst (?w' ! (x-2)) = fst (w ! (x-2+2))\<close> by (by100 simp)
            ultimately show ?thesis using hx(2) by (by100 simp)
          qed
        next
          fix y assume hy: "y \<in> {i. i < length ?w' \<and> fst (?w' ! i) = label}"
          hence hy_props: "y < length ?w'" "fst (?w' ! y) = label" by (by100 simp)+
          \<comment> \<open>Find x such that ?f x = y.\<close>
          show "y \<in> ?f ` {i. i < length w \<and> fst (w ! i) = label}"
          proof (cases "y < j")
            case True
            hence "?w' ! y = w ! y" using hnth_lt by (by100 blast)
            hence "fst (w ! y) = label" using hy_props(2) by (by100 simp)
            moreover have "y < length w" using hy_props(1) hlen_w' hj by (by100 simp)
            ultimately have "y \<in> {i. i < length w \<and> fst (w ! i) = label}" by (by100 simp)
            moreover have "?f y = y" using True by (by100 simp)
            ultimately show ?thesis by (by100 force)
          next
            case False
            hence "y \<ge> j" by (by100 simp)
            let ?x = "y + 2"
            have "?w' ! y = w ! (y+2)" using hnth_ge \<open>y \<ge> j\<close> hy_props(1) by (by100 blast)
            hence "fst (w ! (y+2)) = label" using hy_props(2) by (by100 simp)
            moreover have "y+2 < length w" using hy_props(1) hlen_w' hj by (by100 simp)
            moreover have "y + 2 \<ge> j + 2" using \<open>y \<ge> j\<close> by (by100 simp)
            hence "?f (y+2) = y" by (by100 simp)
            moreover have "y+2 \<in> {i. i < length w \<and> fst (w ! i) = label}"
              using \<open>fst (w ! (y+2)) = label\<close> \<open>y+2 < length w\<close> by (by100 simp)
            ultimately show ?thesis by (by100 force)
          qed
        qed
      qed
      hence "card {i. i < length w \<and> fst (w ! i) = label}
          = card {i. i < length ?w' \<and> fst (?w' ! i) = label}"
        using bij_betw_same_card by (by100 blast)
      have "card {i. i < length ?w' \<and> fst (?w' ! i) = label}
          = card {i. i < length w \<and> fst (w ! i) = label}"
        using \<open>card {i. i < length w \<and> fst (w ! i) = label}
            = card {i. i < length ?w' \<and> fst (?w' ! i) = label}\<close>
        by (by100 simp)
      moreover from hproper have "card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
        by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
  qed
qed

\<comment> \<open>A proper scheme has even length (each label contributes 0 or 2 to the count).\<close>
lemma proper_scheme_even_length:
  assumes "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
  shows "even (length w)"
proof -
  \<comment> \<open>Total length = sum over distinct labels of their counts.
     Each count \<in> {0, 2}. So total = 2 * (number of labels with count 2) = even.\<close>
  \<comment> \<open>Formalize: the set of labels appearing in w is finite.\<close>
  let ?labels = "fst ` set w"
  have hfin_lab: "finite ?labels" by (by100 simp)
  \<comment> \<open>For labels NOT in ?labels: count = 0.\<close>
  \<comment> \<open>Total length = sum over ?labels of count.\<close>
  \<comment> \<open>Each count is 2 (since label \<in> ?labels means it appears, so count \<noteq> 0, hence = 2).\<close>
  \<comment> \<open>Total = 2 * card(?labels) = even.\<close>
  have "length w = card {0..<length w}" by (by100 simp)
  \<comment> \<open>{0..<length w} partitions by label. Sum of partition sizes = total.\<close>
  \<comment> \<open>This is a partition-of-unity argument on finite sets.\<close>
  also have "\<dots> = (\<Sum>l \<in> ?labels. card {i. i < length w \<and> fst (w ! i) = l})"
  proof -
    \<comment> \<open>{0..<length w} = \<Union>l\<in>?labels. {i. i < length w \<and> fst(w!i) = l}.\<close>
    have hpart: "{0..<length w} = (\<Union>l \<in> ?labels. {i. i < length w \<and> fst (w ! i) = l})"
    proof (rule set_eqI, rule iffI)
      fix i assume "i \<in> {0..<length w}"
      hence hi: "i < length w" by (by100 simp)
      have "w ! i \<in> set w" using hi by (by100 simp)
      hence "fst (w ! i) \<in> ?labels" by (by100 blast)
      thus "i \<in> (\<Union>l \<in> ?labels. {i. i < length w \<and> fst (w ! i) = l})" using hi by (by100 blast)
    next
      fix i assume "i \<in> (\<Union>l \<in> ?labels. {i. i < length w \<and> fst (w ! i) = l})"
      thus "i \<in> {0..<length w}" by (by100 simp)
    qed
    have hdisj: "\<forall>l1 \<in> ?labels. \<forall>l2 \<in> ?labels. l1 \<noteq> l2
        \<longrightarrow> {i. i < length w \<and> fst (w ! i) = l1} \<inter> {i. i < length w \<and> fst (w ! i) = l2} = {}"
      by (by100 blast)
    have hfin_parts: "\<forall>l \<in> ?labels. finite {i. i < length w \<and> fst (w ! i) = l}"
      by (by100 simp)
    have "card (\<Union>l \<in> ?labels. {i. i < length w \<and> fst (w ! i) = l})
        = (\<Sum>l \<in> ?labels. card {i. i < length w \<and> fst (w ! i) = l})"
    proof (rule card_UN_disjoint)
      show "finite ?labels" using hfin_lab .
      show "\<forall>l\<in>?labels. finite {i. i < length w \<and> fst (w ! i) = l}" using hfin_parts .
      show "\<forall>i\<in>?labels. \<forall>j\<in>?labels. i \<noteq> j
          \<longrightarrow> {ia. ia < length w \<and> fst (w ! ia) = i} \<inter> {ia. ia < length w \<and> fst (w ! ia) = j} = {}"
        by (by100 blast)
    qed
    thus ?thesis using hpart by (by100 simp)
  qed
  also have "\<dots> = (\<Sum>l \<in> ?labels. 2)"
  proof (rule sum.cong)
    show "?labels = ?labels" by (by100 simp)
    fix l assume "l \<in> ?labels"
    then obtain x where "x \<in> set w" "fst x = l" by (by100 blast)
    hence "\<exists>j. j < length w \<and> w ! j = x" by (simp add: in_set_conv_nth)
    then obtain j where "j < length w" "w ! j = x" by (by100 blast)
    hence "j < length w" "fst (w ! j) = l" using \<open>fst x = l\<close> by (by100 simp)+
    hence "{i. i < length w \<and> fst (w ! i) = l} \<noteq> {}" by (by100 blast)
    hence "card {i. i < length w \<and> fst (w ! i) = l} \<noteq> 0" by (by100 simp)
    moreover from assms have "card {i. i < length w \<and> fst (w ! i) = l} \<in> {0, 2}" by (by100 blast)
    ultimately show "card {i. i < length w \<and> fst (w ! i) = l} = 2" by (by100 blast)
  qed
  also have "\<dots> = 2 * card ?labels" by (by100 simp)
  finally show "even (length w)" by (by100 presburger)
qed

\<comment> \<open>A proper 2-element scheme has both elements with the same label.\<close>
lemma proper_len2_same_label:
  fixes w :: "('a \<times> bool) list"
  assumes "length w = 2"
      and "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
  shows "fst (w ! 0) = fst (w ! 1)"
proof (rule ccontr)
  assume hne: "fst (w ! 0) \<noteq> fst (w ! 1)"
  from assms(2)[rule_format, of "fst (w ! 0)"]
  have "card {i. i < 2 \<and> fst (w ! i) = fst (w ! 0)} \<in> {0, 2}" using assms(1) by simp
  moreover have "{i. i < 2 \<and> fst (w ! i) = fst (w ! 0)} = {0}"
  proof
    show "{i. i < 2 \<and> fst (w ! i) = fst (w ! 0)} \<subseteq> {0}"
      using hne by (by100 auto) (metis One_nat_def Suc_1 less_2_cases_iff)
    show "{0} \<subseteq> {i. i < 2 \<and> fst (w ! i) = fst (w ! 0)}" by (by100 simp)
  qed
  ultimately show False by simp
qed

\<comment> \<open>Decompose a list at two known positions p1 < p2.\<close>
lemma list_decomp_at_two_positions:
  assumes hp1: "p1 < p2" and hp2: "p2 < length xs"
  shows "xs = take p1 xs @ [xs ! p1] @ take (p2 - p1 - 1) (drop (p1 + 1) xs)
      @ [xs ! p2] @ drop (p2 + 1) xs"
proof -
  have hp1_len: "p1 < length xs" using hp1 hp2 by (by100 simp)
  \<comment> \<open>Step 1: split at p1.\<close>
  have s1: "xs = take p1 xs @ xs ! p1 # drop (Suc p1) xs"
    using id_take_nth_drop[OF hp1_len] .
  \<comment> \<open>Step 2: split drop (Suc p1) xs at position p2 - p1 - 1.\<close>
  let ?tail = "drop (Suc p1) xs"
  have htail_len: "length ?tail = length xs - Suc p1" by (by100 simp)
  have hp2_idx: "p2 - p1 - 1 < length ?tail" using hp1 hp2 by (by100 simp)
  have htail_nth: "?tail ! (p2 - p1 - 1) = xs ! p2"
    using hp1 hp2 by (by100 simp)
  have s2: "?tail = take (p2 - p1 - 1) ?tail @ ?tail ! (p2 - p1 - 1) # drop (Suc (p2 - p1 - 1)) ?tail"
    using id_take_nth_drop[OF hp2_idx] .
  \<comment> \<open>Suc (p2 - p1 - 1) = p2 - p1 when p1 < p2.\<close>
  have "Suc (p2 - p1 - 1) = p2 - p1" using hp1 by (by100 simp)
  hence "drop (Suc (p2 - p1 - 1)) ?tail = drop (p2 - p1) (drop (Suc p1) xs)"
    by (by100 simp)
  also have "\<dots> = drop (p2 + 1) xs"
  proof -
    have "p2 - p1 + Suc p1 = Suc p2" using hp1 by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  finally have hdrop_eq: "drop (Suc (p2 - p1 - 1)) ?tail = drop (p2 + 1) xs" .
  \<comment> \<open>Combine.\<close>
  from s1 s2 htail_nth hdrop_eq
  show ?thesis by (by100 simp)
qed

\<comment> \<open>In any scheme where label a appears exactly at 2 positions with True direction
   and a does not appear elsewhere: Lemma 77.1 brings the pair to front.\<close>
lemma bring_projective_pair_to_front:
  fixes w :: "(nat \<times> bool) list" and a :: nat
  assumes hain: "(a, True) \<in> set w"
      and hcard: "card {i. i < length w \<and> fst (w ! i) = a} = 2"
      and hdir: "\<forall>i < length w. fst (w ! i) = a \<longrightarrow> snd (w ! i) = True"
      and hne: "w \<noteq> []"
      and hproper_w: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
  shows "\<exists>rest. top1_scheme_equiv w ([(a, True), (a, True)] @ rest)
      \<and> length rest = length w - 2
      \<and> (\<forall>e \<in> set rest. fst e \<noteq> a)
      \<and> fst ` set rest \<subseteq> fst ` set w
      \<and> (\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2})"
proof -
  \<comment> \<open>Find first position of (a,True).\<close>
  from hain obtain p' where hp': "p' < length w" "w ! p' = (a, True)"
    by (simp add: in_set_conv_nth) (by100 blast)
  \<comment> \<open>Rotate to position 0.\<close>
  let ?w' = "drop p' w @ take p' w"
  have hrot: "top1_scheme_equiv w ?w'"
    using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of "take p' w" "drop p' w"]]
    by (by100 simp)
  have hlen': "length ?w' = length w" by (by100 simp)
  have hw'_0: "?w' ! 0 = (a, True)"
  proof -
    have "drop p' w \<noteq> []" using hp'(1) by (by100 simp)
    hence "?w' ! 0 = (drop p' w) ! 0"
      using nth_append[of "drop p' w" "take p' w" 0] by (by100 simp)
    also have "\<dots> = w ! p'" using hp' by (by100 simp)
    finally show ?thesis using hp'(2) by (by100 simp)
  qed
  \<comment> \<open>Actually, we don't need to rotate. Apply Lemma 77.1 directly to w.\<close>
  \<comment> \<open>Find second a-position q'.\<close>
  have "card ({i. i < length w \<and> fst (w ! i) = a} - {p'}) = 1"
  proof -
    have "finite {i. i < length w \<and> fst (w ! i) = a}" by (by100 simp)
    moreover have "p' \<in> {i. i < length w \<and> fst (w ! i) = a}" using hp' by (by100 simp)
    ultimately have "card ({i. i < length w \<and> fst (w ! i) = a} - {p'})
        = card {i. i < length w \<and> fst (w ! i) = a} - 1" by (by100 simp)
    thus ?thesis using hcard by (by100 simp)
  qed
  hence "card ({i. i < length w \<and> fst (w ! i) = a} - {p'}) \<noteq> 0" by (by100 simp)
  moreover have "finite ({i. i < length w \<and> fst (w ! i) = a} - {p'})" by (by100 simp)
  ultimately have "{i. i < length w \<and> fst (w ! i) = a} - {p'} \<noteq> {}" by (by100 force)
  then obtain q' where "q' \<in> {i. i < length w \<and> fst (w ! i) = a} - {p'}" by (by100 blast)
  hence hq': "q' < length w" "fst (w ! q') = a" "q' \<noteq> p'" by (by100 simp)+
  have hq'_dir: "snd (w ! q') = True" using hdir hq'(1,2) by (by100 blast)
  hence hq'_val: "w ! q' = (a, True)" using hq'(2) by (cases "w ! q'") (by100 simp)
  \<comment> \<open>WLOG p' < q' (by symmetry, swap if needed). Actually just decompose.\<close>
  \<comment> \<open>If p' < q': y0 = take p' w, y1 = take(q'-p'-1)(drop(p'+1) w), y2 = drop(q'+1) w.
     If p' > q': swap and use q' as first position.\<close>
  \<comment> \<open>For simplicity, take the SMALLER index as the first a-position.\<close>
  define p1 where "p1 = min p' q'"
  define p2 where "p2 = max p' q'"
  have hp1_lt_p2: "p1 < p2" using hq'(3) unfolding p1_def p2_def by (by100 simp)
  have hp1_val: "w ! p1 = (a, True)"
  proof -
    have "p1 = p' \<or> p1 = q'" unfolding p1_def min_def by (by100 simp)
    thus ?thesis using hp'(2) hq'_val by (by100 blast)
  qed
  have hp2_val: "w ! p2 = (a, True)"
  proof -
    have "p2 = p' \<or> p2 = q'" unfolding p2_def max_def by (by100 simp)
    thus ?thesis using hp'(2) hq'_val by (by100 blast)
  qed
  have hp1_len: "p1 < length w" unfolding p1_def using hp'(1) hq'(1) by (by100 simp)
  have hp2_len: "p2 < length w" unfolding p2_def using hp'(1) hq'(1) by (by100 simp)
  \<comment> \<open>Decompose: w = (take p1 w) @ [(a,T)] @ (take(p2-p1-1)(drop(p1+1) w)) @ [(a,T)] @ (drop(p2+1) w).\<close>
  define y0 where "y0 = take p1 w"
  define y1 where "y1 = take (p2 - p1 - 1) (drop (p1 + 1) w)"
  define y2 where "y2 = drop (p2 + 1) w"
  have hdecomp: "w = y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2"
  proof -
    from list_decomp_at_two_positions[OF hp1_lt_p2 hp2_len]
    have "w = take p1 w @ [w ! p1] @ take (p2 - p1 - 1) (drop (p1 + 1) w) @ [w ! p2] @ drop (p2 + 1) w" .
    thus ?thesis unfolding y0_def y1_def y2_def using hp1_val hp2_val by (by100 simp)
  qed
  \<comment> \<open>All elements in y0, y1, y2 have fst \<noteq> a.\<close>
  \<comment> \<open>Positions with label a = {p1, p2} (from card=2 + card\_seteq).\<close>
  have honly_p12: "{i. i < length w \<and> fst (w ! i) = a} = {p1, p2}"
  proof -
    have "card {p1, p2} = 2" using hp1_lt_p2 by (by100 simp)
    have "p1 \<in> {i. i < length w \<and> fst (w ! i) = a}"
      using hp1_len hp1_val by (by100 simp)
    moreover have "p2 \<in> {i. i < length w \<and> fst (w ! i) = a}"
      using hp2_len hp2_val by (by100 simp)
    ultimately have "{p1, p2} \<subseteq> {i. i < length w \<and> fst (w ! i) = a}" by (by100 blast)
    have "finite {i. i < length w \<and> fst (w ! i) = a}" by (by100 simp)
    from card_seteq[OF this \<open>{p1, p2} \<subseteq> _\<close>] hcard \<open>card {p1, p2} = 2\<close>
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Elements at positions \<noteq> p1, \<noteq> p2 have fst \<noteq> a.\<close>
  have hother_ne_a: "\<forall>k < length w. k \<noteq> p1 \<longrightarrow> k \<noteq> p2 \<longrightarrow> fst (w ! k) \<noteq> a"
  proof (intro allI impI)
    fix k assume "k < length w" "k \<noteq> p1" "k \<noteq> p2"
    hence "k \<notin> {p1, p2}" by (by100 blast)
    hence "k \<notin> {i. i < length w \<and> fst (w ! i) = a}" using honly_p12 by (by100 blast)
    thus "fst (w ! k) \<noteq> a" using \<open>k < length w\<close> by (by100 blast)
  qed
  have hcond1: "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
  proof (intro ballI)
    fix e assume "e \<in> set y0 \<union> set y1 \<union> set y2"
    thus "fst e \<noteq> a"
    proof (elim UnE)
      assume "e \<in> set y0"
      then obtain i where "i < length y0" "y0 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      hence "i < p1" unfolding y0_def by (by100 simp)
      have "w ! i = e" using \<open>i < p1\<close> \<open>y0 ! i = e\<close> unfolding y0_def using hp1_len by (by100 simp)
      moreover have "i \<noteq> p1" "i \<noteq> p2" using \<open>i < p1\<close> hp1_lt_p2 by (by100 simp)+
      moreover have "i < length w" using \<open>i < p1\<close> hp1_len by (by100 simp)
      ultimately show "fst e \<noteq> a" using hother_ne_a by (by100 blast)
    next
      assume "e \<in> set y1"
      then obtain i where "i < length y1" "y1 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      hence "i < p2 - p1 - 1" unfolding y1_def by (by100 simp)
      define k where "k = p1 + 1 + i"
      have "w ! k = e" unfolding k_def y1_def
        using \<open>i < length y1\<close> \<open>y1 ! i = e\<close> y1_def hp1_len by (by100 simp)
      moreover have "k \<noteq> p1" unfolding k_def by (by100 simp)
      moreover have "k \<noteq> p2" unfolding k_def using \<open>i < p2 - p1 - 1\<close> by (by100 simp)
      moreover have "k < length w" unfolding k_def using \<open>i < p2 - p1 - 1\<close> hp2_len by (by100 simp)
      ultimately show "fst e \<noteq> a" using hother_ne_a by (by100 blast)
    next
      assume "e \<in> set y2"
      then obtain i where "i < length y2" "y2 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      define k where "k = p2 + 1 + i"
      have "w ! k = e" unfolding k_def y2_def
        using \<open>i < length y2\<close> \<open>y2 ! i = e\<close> y2_def hp2_len by (by100 simp)
      moreover have "k \<noteq> p1" unfolding k_def using hp1_lt_p2 by (by100 simp)
      moreover have "k \<noteq> p2" unfolding k_def by (by100 simp)
      have "length y2 = length w - (p2 + 1)" unfolding y2_def by (by100 simp)
      have "k < length w" unfolding k_def using \<open>i < length y2\<close> hp2_len \<open>length y2 = length w - (p2 + 1)\<close> by (by100 simp)
      from hother_ne_a[rule_format, OF this \<open>k \<noteq> p1\<close> \<open>k \<noteq> p2\<close>]
      show "fst e \<noteq> a" using \<open>w ! k = e\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Fresh label exists.\<close>
  have hcond2: "\<exists>b::nat. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  proof -
    \<comment> \<open>The set of labels in y0\<union>y1\<union>y2 is finite (subset of scheme labels).\<close>
    let ?all_labels = "insert a (fst ` set w)"
    have "finite ?all_labels" by (by100 simp)
    then obtain b :: nat where "b \<notin> ?all_labels"
      using ex_new_if_finite[of ?all_labels] infinite_UNIV_nat by (by100 blast)
    hence "b \<noteq> a" by (by100 blast)
    moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    proof (intro ballI)
      fix e assume "e \<in> set y0 \<union> set y1 \<union> set y2"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      hence "fst e \<in> fst ` set w" by (by100 blast)
      hence "fst e \<in> ?all_labels" by (by100 blast)
      thus "fst e \<noteq> b" using \<open>b \<notin> ?all_labels\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Apply Lemma 77.1.\<close>
  from Lemma_77_1_projective_collection[OF hcond1 hcond2]
  have "top1_scheme_equiv (y0 @ [(a,True)] @ y1 @ [(a,True)] @ y2)
      ([(a,True),(a,True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)" .
  hence "top1_scheme_equiv w ([(a,True),(a,True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    using hdecomp by (by100 simp)
  moreover have "length (y0 @ rev (map top1_inverse_edge y1) @ y2) = length w - 2"
  proof -
    have "length w = length y0 + 1 + length y1 + 1 + length y2"
      using hdecomp by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  moreover have "\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<noteq> a"
  proof (intro ballI)
    fix e assume "e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2)"
    hence "e \<in> set y0 \<or> e \<in> set (rev (map top1_inverse_edge y1)) \<or> e \<in> set y2" by (by100 simp)
    thus "fst e \<noteq> a"
    proof (elim disjE)
      assume "e \<in> set y0" thus ?thesis using hcond1 by (by100 blast)
    next
      assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by (by100 simp)
      then obtain e0 where "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 force)
      hence "fst e0 \<noteq> a" using hcond1 by (by100 blast)
      thus ?thesis using \<open>e = top1_inverse_edge e0\<close> unfolding top1_inverse_edge_def by (by100 simp)
    next
      assume "e \<in> set y2" thus ?thesis using hcond1 by (by100 blast)
    qed
  qed
  moreover have "\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<in> fst ` set w"
  proof (intro ballI)
    fix e assume "e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2)"
    hence "e \<in> set y0 \<or> e \<in> set (rev (map top1_inverse_edge y1)) \<or> e \<in> set y2" by (by100 simp)
    thus "fst e \<in> fst ` set w"
    proof (elim disjE)
      assume "e \<in> set y0"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by (by100 simp)
      then obtain e' where "e' \<in> set y1" "e = top1_inverse_edge e'" by (by100 force)
      hence "e' \<in> set w" using hdecomp by (by100 simp)
      hence "fst e' \<in> fst ` set w" by (by100 blast)
      thus ?thesis using \<open>e = top1_inverse_edge e'\<close> unfolding top1_inverse_edge_def by (by100 simp)
    next
      assume "e \<in> set y2"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
  qed
  hence "fst ` set (y0 @ rev (map top1_inverse_edge y1) @ y2) \<subseteq> fst ` set w" by (by100 blast)
  moreover have "\<forall>label. card {i. i < length (y0 @ rev (map top1_inverse_edge y1) @ y2)
      \<and> fst ((y0 @ rev (map top1_inverse_edge y1) @ y2) ! i) = label} \<in> {0, 2}"
  proof (intro allI)
    fix label
    let ?rest = "y0 @ rev (map top1_inverse_edge y1) @ y2"
    show "card {i. i < length ?rest \<and> fst (?rest ! i) = label} \<in> {0, 2}"
    proof (cases "label = a")
      case True
      \<comment> \<open>Label a: count = 0 since all elements have fst \<noteq> a.\<close>
      have "{i. i < length ?rest \<and> fst (?rest ! i) = a} = {}"
      proof (rule ccontr)
        assume "{i. i < length ?rest \<and> fst (?rest ! i) = a} \<noteq> {}"
        then obtain i where "i < length ?rest" "fst (?rest ! i) = a" by (by100 blast)
        hence "?rest ! i \<in> set ?rest" using nth_mem by (by100 blast)
        hence "fst (?rest ! i) \<noteq> a"
          using \<open>\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<noteq> a\<close> by (by100 blast)
        thus False using \<open>fst (?rest ! i) = a\<close> by (by100 simp)
      qed
      thus ?thesis using True by (by100 simp)
    next
      case False
      \<comment> \<open>Label l \<noteq> a: count in rest = count in w \<in> {0,2}.
         The proof goes through the internal y0/y1/y2 decomposition.
         count(l, rest) = count(l, y0) + count(l, rev(inv(y1))) + count(l, y2)
                        = count(l, y0) + count(l, y1) + count(l, y2)   [inv preserves fst]
                        = count(l, w)   [since l \<noteq> a and a-positions don't contribute]\<close>
      \<comment> \<open>Use filter-length: count(l, rest) = count(l, w) via filter decomposition.\<close>
      let ?P = "\<lambda>e. fst e = label"
      have hfilt_rest: "length (filter ?P ?rest)
          = length (filter ?P y0) + length (filter ?P (rev (map top1_inverse_edge y1))) + length (filter ?P y2)"
        by (by100 simp)
      \<comment> \<open>filter commutes with rev, and inv preserves fst.\<close>
      have "filter ?P (rev (map top1_inverse_edge y1)) = rev (filter ?P (map top1_inverse_edge y1))"
        using rev_filter[of ?P "map top1_inverse_edge y1", symmetric] .
      hence "length (filter ?P (rev (map top1_inverse_edge y1))) = length (filter ?P (map top1_inverse_edge y1))"
        by (by100 simp)
      moreover have "length (filter ?P (map top1_inverse_edge y1)) = length (filter ?P y1)"
      proof -
        \<comment> \<open>length\_filter\_map gives: length(filter P (map f xs)) = length(filter (P\<circ>f) xs).
           Then P \<circ> inv = P (since inv preserves fst) gives the result.\<close>
        have "?P \<circ> top1_inverse_edge = ?P"
          by (rule ext) (simp add: top1_inverse_edge_def comp_def split: prod.splits)
        thus ?thesis by simp
      qed
      ultimately have "length (filter ?P (rev (map top1_inverse_edge y1))) = length (filter ?P y1)"
        by (by100 simp)
      hence hcount_rest: "length (filter ?P ?rest)
          = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)"
        using hfilt_rest by (by100 simp)
      \<comment> \<open>For w: the two a-positions don't contribute to filter (since label \<noteq> a).\<close>
      have "length (filter ?P w) = length (filter ?P (y0 @ [(a,True)] @ y1 @ [(a,True)] @ y2))"
        using hdecomp by (by100 simp)
      also have "\<dots> = length (filter ?P y0) + length (filter ?P [(a,True)]) + length (filter ?P y1)
          + length (filter ?P [(a,True)]) + length (filter ?P y2)"
        by (by100 simp)
      also have "filter ?P [(a,True)] = []" using False by (by100 simp)
      hence "length (filter ?P [(a,True)]) = 0" by (by100 simp)
      hence "length (filter ?P y0) + length (filter ?P [(a,True)]) + length (filter ?P y1)
          + length (filter ?P [(a,True)]) + length (filter ?P y2)
          = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)" by (by100 simp)
      finally have hcount_w: "length (filter ?P w) = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)" .
      \<comment> \<open>So count(label, rest) = count(label, w).\<close>
      have "length (filter ?P ?rest) = length (filter ?P w)"
        using hcount_rest hcount_w by (by100 simp)
      \<comment> \<open>Convert to card via length\_filter\_conv\_card.\<close>
      hence "card {i. i < length ?rest \<and> fst (?rest ! i) = label}
           = card {i. i < length w \<and> fst (w ! i) = label}"
        using length_filter_conv_card[of ?P ?rest] length_filter_conv_card[of ?P w] by (by100 simp)
      moreover from hproper_w have "card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
  qed
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Valid version of bring\\_projective\\_pair\\_to\\_front.
   Reuses the old proof's combinatorial facts, replays only the 2 operations validly.\<close>
lemma valid_bring_projective_pair_to_front_full:
  fixes w :: "(nat \<times> bool) list" and a :: nat
  assumes hain: "(a, True) \<in> set w"
      and hcard: "card {i. i < length w \<and> fst (w ! i) = a} = 2"
      and hdir: "\<forall>i < length w. fst (w ! i) = a \<longrightarrow> snd (w ! i) = True"
      and hne: "w \<noteq> []"
      and hproper_w: "\<forall>label. card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}"
  shows "\<exists>rest. top1_valid_scheme_equiv w ([(a, True), (a, True)] @ rest)
      \<and> length rest = length w - 2
      \<and> (\<forall>e \<in> set rest. fst e \<noteq> a)
      \<and> fst ` set rest \<subseteq> fst ` set w
      \<and> (\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2})"
proof -
  \<comment> \<open>Find first position of (a,True).\<close>
  from hain obtain p' where hp': "p' < length w" "w ! p' = (a, True)"
    by (simp add: in_set_conv_nth) (by100 blast)
  \<comment> \<open>Rotate to position 0.\<close>
  let ?w' = "drop p' w @ take p' w"
  have hrot: "top1_valid_scheme_equiv w ?w'"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate[of "take p' w" "drop p' w"]]
    by (by100 simp)
  have hlen': "length ?w' = length w" by (by100 simp)
  have hw'_0: "?w' ! 0 = (a, True)"
  proof -
    have "drop p' w \<noteq> []" using hp'(1) by (by100 simp)
    hence "?w' ! 0 = (drop p' w) ! 0"
      using nth_append[of "drop p' w" "take p' w" 0] by (by100 simp)
    also have "\<dots> = w ! p'" using hp' by (by100 simp)
    finally show ?thesis using hp'(2) by (by100 simp)
  qed
  \<comment> \<open>Actually, we don't need to rotate. Apply Lemma 77.1 directly to w.\<close>
  \<comment> \<open>Find second a-position q'.\<close>
  have "card ({i. i < length w \<and> fst (w ! i) = a} - {p'}) = 1"
  proof -
    have "finite {i. i < length w \<and> fst (w ! i) = a}" by (by100 simp)
    moreover have "p' \<in> {i. i < length w \<and> fst (w ! i) = a}" using hp' by (by100 simp)
    ultimately have "card ({i. i < length w \<and> fst (w ! i) = a} - {p'})
        = card {i. i < length w \<and> fst (w ! i) = a} - 1" by (by100 simp)
    thus ?thesis using hcard by (by100 simp)
  qed
  hence "card ({i. i < length w \<and> fst (w ! i) = a} - {p'}) \<noteq> 0" by (by100 simp)
  moreover have "finite ({i. i < length w \<and> fst (w ! i) = a} - {p'})" by (by100 simp)
  ultimately have "{i. i < length w \<and> fst (w ! i) = a} - {p'} \<noteq> {}" by (by100 force)
  then obtain q' where "q' \<in> {i. i < length w \<and> fst (w ! i) = a} - {p'}" by (by100 blast)
  hence hq': "q' < length w" "fst (w ! q') = a" "q' \<noteq> p'" by (by100 simp)+
  have hq'_dir: "snd (w ! q') = True" using hdir hq'(1,2) by (by100 blast)
  hence hq'_val: "w ! q' = (a, True)" using hq'(2) by (cases "w ! q'") (by100 simp)
  \<comment> \<open>WLOG p' < q' (by symmetry, swap if needed). Actually just decompose.\<close>
  \<comment> \<open>If p' < q': y0 = take p' w, y1 = take(q'-p'-1)(drop(p'+1) w), y2 = drop(q'+1) w.
     If p' > q': swap and use q' as first position.\<close>
  \<comment> \<open>For simplicity, take the SMALLER index as the first a-position.\<close>
  define p1 where "p1 = min p' q'"
  define p2 where "p2 = max p' q'"
  have hp1_lt_p2: "p1 < p2" using hq'(3) unfolding p1_def p2_def by (by100 simp)
  have hp1_val: "w ! p1 = (a, True)"
  proof -
    have "p1 = p' \<or> p1 = q'" unfolding p1_def min_def by (by100 simp)
    thus ?thesis using hp'(2) hq'_val by (by100 blast)
  qed
  have hp2_val: "w ! p2 = (a, True)"
  proof -
    have "p2 = p' \<or> p2 = q'" unfolding p2_def max_def by (by100 simp)
    thus ?thesis using hp'(2) hq'_val by (by100 blast)
  qed
  have hp1_len: "p1 < length w" unfolding p1_def using hp'(1) hq'(1) by (by100 simp)
  have hp2_len: "p2 < length w" unfolding p2_def using hp'(1) hq'(1) by (by100 simp)
  \<comment> \<open>Decompose: w = (take p1 w) @ [(a,T)] @ (take(p2-p1-1)(drop(p1+1) w)) @ [(a,T)] @ (drop(p2+1) w).\<close>
  define y0 where "y0 = take p1 w"
  define y1 where "y1 = take (p2 - p1 - 1) (drop (p1 + 1) w)"
  define y2 where "y2 = drop (p2 + 1) w"
  have hdecomp: "w = y0 @ [(a, True)] @ y1 @ [(a, True)] @ y2"
  proof -
    from list_decomp_at_two_positions[OF hp1_lt_p2 hp2_len]
    have "w = take p1 w @ [w ! p1] @ take (p2 - p1 - 1) (drop (p1 + 1) w) @ [w ! p2] @ drop (p2 + 1) w" .
    thus ?thesis unfolding y0_def y1_def y2_def using hp1_val hp2_val by (by100 simp)
  qed
  \<comment> \<open>All elements in y0, y1, y2 have fst \<noteq> a.\<close>
  \<comment> \<open>Positions with label a = {p1, p2} (from card=2 + card\_seteq).\<close>
  have honly_p12: "{i. i < length w \<and> fst (w ! i) = a} = {p1, p2}"
  proof -
    have "card {p1, p2} = 2" using hp1_lt_p2 by (by100 simp)
    have "p1 \<in> {i. i < length w \<and> fst (w ! i) = a}"
      using hp1_len hp1_val by (by100 simp)
    moreover have "p2 \<in> {i. i < length w \<and> fst (w ! i) = a}"
      using hp2_len hp2_val by (by100 simp)
    ultimately have "{p1, p2} \<subseteq> {i. i < length w \<and> fst (w ! i) = a}" by (by100 blast)
    have "finite {i. i < length w \<and> fst (w ! i) = a}" by (by100 simp)
    from card_seteq[OF this \<open>{p1, p2} \<subseteq> _\<close>] hcard \<open>card {p1, p2} = 2\<close>
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Elements at positions \<noteq> p1, \<noteq> p2 have fst \<noteq> a.\<close>
  have hother_ne_a: "\<forall>k < length w. k \<noteq> p1 \<longrightarrow> k \<noteq> p2 \<longrightarrow> fst (w ! k) \<noteq> a"
  proof (intro allI impI)
    fix k assume "k < length w" "k \<noteq> p1" "k \<noteq> p2"
    hence "k \<notin> {p1, p2}" by (by100 blast)
    hence "k \<notin> {i. i < length w \<and> fst (w ! i) = a}" using honly_p12 by (by100 blast)
    thus "fst (w ! k) \<noteq> a" using \<open>k < length w\<close> by (by100 blast)
  qed
  have hcond1: "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> a"
  proof (intro ballI)
    fix e assume "e \<in> set y0 \<union> set y1 \<union> set y2"
    thus "fst e \<noteq> a"
    proof (elim UnE)
      assume "e \<in> set y0"
      then obtain i where "i < length y0" "y0 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      hence "i < p1" unfolding y0_def by (by100 simp)
      have "w ! i = e" using \<open>i < p1\<close> \<open>y0 ! i = e\<close> unfolding y0_def using hp1_len by (by100 simp)
      moreover have "i \<noteq> p1" "i \<noteq> p2" using \<open>i < p1\<close> hp1_lt_p2 by (by100 simp)+
      moreover have "i < length w" using \<open>i < p1\<close> hp1_len by (by100 simp)
      ultimately show "fst e \<noteq> a" using hother_ne_a by (by100 blast)
    next
      assume "e \<in> set y1"
      then obtain i where "i < length y1" "y1 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      hence "i < p2 - p1 - 1" unfolding y1_def by (by100 simp)
      define k where "k = p1 + 1 + i"
      have "w ! k = e" unfolding k_def y1_def
        using \<open>i < length y1\<close> \<open>y1 ! i = e\<close> y1_def hp1_len by (by100 simp)
      moreover have "k \<noteq> p1" unfolding k_def by (by100 simp)
      moreover have "k \<noteq> p2" unfolding k_def using \<open>i < p2 - p1 - 1\<close> by (by100 simp)
      moreover have "k < length w" unfolding k_def using \<open>i < p2 - p1 - 1\<close> hp2_len by (by100 simp)
      ultimately show "fst e \<noteq> a" using hother_ne_a by (by100 blast)
    next
      assume "e \<in> set y2"
      then obtain i where "i < length y2" "y2 ! i = e" by (simp add: in_set_conv_nth) (by100 blast)
      define k where "k = p2 + 1 + i"
      have "w ! k = e" unfolding k_def y2_def
        using \<open>i < length y2\<close> \<open>y2 ! i = e\<close> y2_def hp2_len by (by100 simp)
      moreover have "k \<noteq> p1" unfolding k_def using hp1_lt_p2 by (by100 simp)
      moreover have "k \<noteq> p2" unfolding k_def by (by100 simp)
      have "length y2 = length w - (p2 + 1)" unfolding y2_def by (by100 simp)
      have "k < length w" unfolding k_def using \<open>i < length y2\<close> hp2_len \<open>length y2 = length w - (p2 + 1)\<close> by (by100 simp)
      from hother_ne_a[rule_format, OF this \<open>k \<noteq> p1\<close> \<open>k \<noteq> p2\<close>]
      show "fst e \<noteq> a" using \<open>w ! k = e\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Fresh label exists.\<close>
  have hcond2: "\<exists>b::nat. b \<noteq> a \<and> (\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b)"
  proof -
    \<comment> \<open>The set of labels in y0\<union>y1\<union>y2 is finite (subset of scheme labels).\<close>
    let ?all_labels = "insert a (fst ` set w)"
    have "finite ?all_labels" by (by100 simp)
    then obtain b :: nat where "b \<notin> ?all_labels"
      using ex_new_if_finite[of ?all_labels] infinite_UNIV_nat by (by100 blast)
    hence "b \<noteq> a" by (by100 blast)
    moreover have "\<forall>e \<in> set y0 \<union> set y1 \<union> set y2. fst e \<noteq> b"
    proof (intro ballI)
      fix e assume "e \<in> set y0 \<union> set y1 \<union> set y2"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      hence "fst e \<in> fst ` set w" by (by100 blast)
      hence "fst e \<in> ?all_labels" by (by100 blast)
      thus "fst e \<noteq> b" using \<open>b \<notin> ?all_labels\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Apply Lemma 77.1.\<close>
  from valid_Lemma_77_1_projective_collection[OF hcond1 hcond2]
  have "top1_valid_scheme_equiv (y0 @ [(a,True)] @ y1 @ [(a,True)] @ y2)
      ([(a,True),(a,True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)" .
  hence "top1_valid_scheme_equiv w ([(a,True),(a,True)] @ y0 @ rev (map top1_inverse_edge y1) @ y2)"
    using hdecomp by (by100 simp)
  moreover have "length (y0 @ rev (map top1_inverse_edge y1) @ y2) = length w - 2"
  proof -
    have "length w = length y0 + 1 + length y1 + 1 + length y2"
      using hdecomp by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  moreover have "\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<noteq> a"
  proof (intro ballI)
    fix e assume "e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2)"
    hence "e \<in> set y0 \<or> e \<in> set (rev (map top1_inverse_edge y1)) \<or> e \<in> set y2" by (by100 simp)
    thus "fst e \<noteq> a"
    proof (elim disjE)
      assume "e \<in> set y0" thus ?thesis using hcond1 by (by100 blast)
    next
      assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by (by100 simp)
      then obtain e0 where "e0 \<in> set y1" "e = top1_inverse_edge e0" by (by100 force)
      hence "fst e0 \<noteq> a" using hcond1 by (by100 blast)
      thus ?thesis using \<open>e = top1_inverse_edge e0\<close> unfolding top1_inverse_edge_def by (by100 simp)
    next
      assume "e \<in> set y2" thus ?thesis using hcond1 by (by100 blast)
    qed
  qed
  moreover have "\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<in> fst ` set w"
  proof (intro ballI)
    fix e assume "e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2)"
    hence "e \<in> set y0 \<or> e \<in> set (rev (map top1_inverse_edge y1)) \<or> e \<in> set y2" by (by100 simp)
    thus "fst e \<in> fst ` set w"
    proof (elim disjE)
      assume "e \<in> set y0"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      assume "e \<in> set (rev (map top1_inverse_edge y1))"
      hence "e \<in> set (map top1_inverse_edge y1)" by (by100 simp)
      then obtain e' where "e' \<in> set y1" "e = top1_inverse_edge e'" by (by100 force)
      hence "e' \<in> set w" using hdecomp by (by100 simp)
      hence "fst e' \<in> fst ` set w" by (by100 blast)
      thus ?thesis using \<open>e = top1_inverse_edge e'\<close> unfolding top1_inverse_edge_def by (by100 simp)
    next
      assume "e \<in> set y2"
      hence "e \<in> set w" using hdecomp by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
  qed
  hence "fst ` set (y0 @ rev (map top1_inverse_edge y1) @ y2) \<subseteq> fst ` set w" by (by100 blast)
  moreover have "\<forall>label. card {i. i < length (y0 @ rev (map top1_inverse_edge y1) @ y2)
      \<and> fst ((y0 @ rev (map top1_inverse_edge y1) @ y2) ! i) = label} \<in> {0, 2}"
  proof (intro allI)
    fix label
    let ?rest = "y0 @ rev (map top1_inverse_edge y1) @ y2"
    show "card {i. i < length ?rest \<and> fst (?rest ! i) = label} \<in> {0, 2}"
    proof (cases "label = a")
      case True
      \<comment> \<open>Label a: count = 0 since all elements have fst \<noteq> a.\<close>
      have "{i. i < length ?rest \<and> fst (?rest ! i) = a} = {}"
      proof (rule ccontr)
        assume "{i. i < length ?rest \<and> fst (?rest ! i) = a} \<noteq> {}"
        then obtain i where "i < length ?rest" "fst (?rest ! i) = a" by (by100 blast)
        hence "?rest ! i \<in> set ?rest" using nth_mem by (by100 blast)
        hence "fst (?rest ! i) \<noteq> a"
          using \<open>\<forall>e \<in> set (y0 @ rev (map top1_inverse_edge y1) @ y2). fst e \<noteq> a\<close> by (by100 blast)
        thus False using \<open>fst (?rest ! i) = a\<close> by (by100 simp)
      qed
      thus ?thesis using True by (by100 simp)
    next
      case False
      \<comment> \<open>Label l \<noteq> a: count in rest = count in w \<in> {0,2}.
         The proof goes through the internal y0/y1/y2 decomposition.
         count(l, rest) = count(l, y0) + count(l, rev(inv(y1))) + count(l, y2)
                        = count(l, y0) + count(l, y1) + count(l, y2)   [inv preserves fst]
                        = count(l, w)   [since l \<noteq> a and a-positions don't contribute]\<close>
      \<comment> \<open>Use filter-length: count(l, rest) = count(l, w) via filter decomposition.\<close>
      let ?P = "\<lambda>e. fst e = label"
      have hfilt_rest: "length (filter ?P ?rest)
          = length (filter ?P y0) + length (filter ?P (rev (map top1_inverse_edge y1))) + length (filter ?P y2)"
        by (by100 simp)
      \<comment> \<open>filter commutes with rev, and inv preserves fst.\<close>
      have "filter ?P (rev (map top1_inverse_edge y1)) = rev (filter ?P (map top1_inverse_edge y1))"
        using rev_filter[of ?P "map top1_inverse_edge y1", symmetric] .
      hence "length (filter ?P (rev (map top1_inverse_edge y1))) = length (filter ?P (map top1_inverse_edge y1))"
        by (by100 simp)
      moreover have "length (filter ?P (map top1_inverse_edge y1)) = length (filter ?P y1)"
      proof -
        \<comment> \<open>length\_filter\_map gives: length(filter P (map f xs)) = length(filter (P\<circ>f) xs).
           Then P \<circ> inv = P (since inv preserves fst) gives the result.\<close>
        have "?P \<circ> top1_inverse_edge = ?P"
          by (rule ext) (simp add: top1_inverse_edge_def comp_def split: prod.splits)
        thus ?thesis by simp
      qed
      ultimately have "length (filter ?P (rev (map top1_inverse_edge y1))) = length (filter ?P y1)"
        by (by100 simp)
      hence hcount_rest: "length (filter ?P ?rest)
          = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)"
        using hfilt_rest by (by100 simp)
      \<comment> \<open>For w: the two a-positions don't contribute to filter (since label \<noteq> a).\<close>
      have "length (filter ?P w) = length (filter ?P (y0 @ [(a,True)] @ y1 @ [(a,True)] @ y2))"
        using hdecomp by (by100 simp)
      also have "\<dots> = length (filter ?P y0) + length (filter ?P [(a,True)]) + length (filter ?P y1)
          + length (filter ?P [(a,True)]) + length (filter ?P y2)"
        by (by100 simp)
      also have "filter ?P [(a,True)] = []" using False by (by100 simp)
      hence "length (filter ?P [(a,True)]) = 0" by (by100 simp)
      hence "length (filter ?P y0) + length (filter ?P [(a,True)]) + length (filter ?P y1)
          + length (filter ?P [(a,True)]) + length (filter ?P y2)
          = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)" by (by100 simp)
      finally have hcount_w: "length (filter ?P w) = length (filter ?P y0) + length (filter ?P y1) + length (filter ?P y2)" .
      \<comment> \<open>So count(label, rest) = count(label, w).\<close>
      have "length (filter ?P ?rest) = length (filter ?P w)"
        using hcount_rest hcount_w by (by100 simp)
      \<comment> \<open>Convert to card via length\_filter\_conv\_card.\<close>
      hence "card {i. i < length ?rest \<and> fst (?rest ! i) = label}
           = card {i. i < length w \<and> fst (w ! i) = label}"
        using length_filter_conv_card[of ?P ?rest] length_filter_conv_card[of ?P w] by (by100 simp)
      moreover from hproper_w have "card {i. i < length w \<and> fst (w ! i) = label} \<in> {0, 2}" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
  qed
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Length-4 projective base case: scheme ~ projective m=1 or m=2.\<close>
lemma projective_len4_base:
  fixes scheme :: "(nat \<times> bool) list"
  assumes hlen: "length scheme = 4"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      and hproj: "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
  shows "(\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w)"
proof -
  \<comment> \<open>Step 1: Get the projective label and standardize its direction to True.\<close>
  from hproj obtain a p q where hp: "p < length scheme" "q < length scheme" "p \<noteq> q"
      "fst (scheme!p) = a" "fst (scheme!q) = a" "snd (scheme!p) = snd (scheme!q)"
    by (by100 blast)
  have hp4: "p < 4" "q < 4" using hp(1,2) hlen by (by100 simp)+
  \<comment> \<open>Step 2: Flip direction of a to True if needed.\<close>
  define scheme1 where "scheme1 = (if snd (scheme!p) then scheme
      else map (\<lambda>(l,b). (l, if l = a then \<not>b else b)) scheme)"
  have hequiv1: "top1_scheme_equiv scheme scheme1"
    unfolding scheme1_def top1_scheme_equiv_def
    using top1_elementary_scheme_operation.flip_label[of scheme a]
    by (cases "snd (scheme!p)") (by100 simp)+
  \<comment> \<open>scheme1 has label a appearing twice with direction True.\<close>
  \<comment> \<open>Step 3: Decompose scheme1 as y0 @ [(a,T)] @ y1 @ [(a,T)] @ y2.\<close>
  \<comment> \<open>Step 4: Apply Lemma\\_77\\_1\\_projective\\_collection.\<close>
  \<comment> \<open>Step 5: Get [(a,T),(a,T)] @ rest. Analyze rest.\<close>
  \<comment> \<open>Step 6: rest is [(b,d'),(b,d'')] for some b \<noteq> a.
     If d' = d'': scheme ~ projective m=2 (after relabel).
     If d' \<noteq> d'': cancel inverse pair \<Rightarrow> scheme ~ projective m=1 (after relabel).\<close>
  \<comment> \<open>Step 3: Rotate scheme1 to put first a at position 0, then apply Lemma 77.1.\<close>
  \<comment> \<open>scheme1 has a appearing twice with direction True. Let p1, q1 be the positions.\<close>
  \<comment> \<open>After rotation: scheme1 ~ [(a,T)] @ y1 @ [(a,T)] @ y2.\<close>
  \<comment> \<open>After Lemma 77.1: ~ [(a,T),(a,T)] @ rev(inv(y1)) @ y2.\<close>
  \<comment> \<open>The rest has length 2 with label b \<noteq> a.\<close>
  \<comment> \<open>Case split: same direction \<Rightarrow> projective m=2; opposite \<Rightarrow> cancel \<Rightarrow> projective m=1.\<close>

  \<comment> \<open>Since this is a long combinatorial proof with many scheme operations,
     we use a direct approach: scheme equiv is transitive and includes all
     elementary operations, so we can chain rotations, flips, and cancellations.\<close>
  \<comment> \<open>The existence of the equivalence follows from the book's proof of Theorem 77.5 Step 2
     for the base case. The formal proof chains:
     scheme ~ scheme1 (flip) ~ rotated (rotate) ~ [(a,T),(a,T)]@rest (Lemma 77.1)
     ~ projective m=1 or m=2 (cancel or relabel).\<close>

  \<comment> \<open>After flip: scheme1 has (a,T) at 2 positions. After rotation: (a,T) at position 0.
     Second (a,T) at position 1, 2, or 3. Each case \<Rightarrow> [(a,T),(a,T)]@rest via rotation/Lemma 77.1.
     Rest has 2 elements with label b: same-direction \<Rightarrow> projective m=2; opposite \<Rightarrow> cancel \<Rightarrow> m=1.\<close>
  \<comment> \<open>Bring both a-copies to positions 0,1.\<close>
  have "\<exists>rest. top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest) \<and> length rest = 2
      \<and> (\<forall>e \<in> set rest. fst e \<noteq> a) \<and> fst ` set rest \<subseteq> fst ` set scheme"
  proof -
    \<comment> \<open>scheme1 satisfies conditions for bring\_projective\_pair\_to\_front.\<close>
    have hlen1: "length scheme1 = 4" unfolding scheme1_def using hlen by (by100 simp)
    have hfst_preserved: "\<forall>i < length scheme1. fst (scheme1 ! i) = fst (scheme ! i)"
    proof (cases "snd (scheme ! p)")
      case True
      hence "scheme1 = scheme" unfolding scheme1_def by (by100 simp)
      thus ?thesis by (by100 simp)
    next
      case False
      hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
        unfolding scheme1_def by (by100 simp)
      show ?thesis
      proof (intro allI impI)
        fix i assume "i < length scheme1"
        hence "i < length scheme" using hsch1 by (by100 simp)
        have "scheme1 ! i = (\<lambda>(l, b). (l, if l = a then \<not> b else b)) (scheme ! i)"
          using hsch1 \<open>i < length scheme\<close> by (by100 simp)
        thus "fst (scheme1 ! i) = fst (scheme ! i)"
          by (cases "scheme ! i") (by100 simp)
      qed
    qed
    have h2: "card {i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = 2"
    proof -
      have "{i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = {i. i < length scheme \<and> fst (scheme ! i) = a}"
      proof (rule set_eqI, rule iffI)
        fix i assume "i \<in> {i. i < length scheme1 \<and> fst (scheme1 ! i) = a}"
        hence "i < length scheme1" "fst (scheme1 ! i) = a" by (by100 simp)+
        have "i < length scheme" using \<open>i < length scheme1\<close> hlen1 hlen by (by100 simp)
        have "fst (scheme1 ! i) = fst (scheme ! i)" using hfst_preserved \<open>i < length scheme1\<close> by (by100 blast)
        hence "fst (scheme ! i) = a" using \<open>fst (scheme1 ! i) = a\<close> by (by100 simp)
        thus "i \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}"
          using \<open>i < length scheme\<close> by (by100 blast)
      next
        fix i assume "i \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}"
        hence "i < length scheme" "fst (scheme ! i) = a" by (by100 simp)+
        hence "i < length scheme1" using hlen1 hlen by (by100 simp)
        hence "fst (scheme1 ! i) = fst (scheme ! i)" using hfst_preserved by (by100 blast)
        hence "fst (scheme1 ! i) = a" using \<open>fst (scheme ! i) = a\<close> by (by100 simp)
        thus "i \<in> {i. i < length scheme1 \<and> fst (scheme1 ! i) = a}" using \<open>i < length scheme1\<close> by (by100 simp)
      qed
      moreover from hproper have "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<in> {0, 2}" by (by100 blast)
      moreover have "p \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}" using hp(1,4) by (by100 blast)
      hence "{i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> {}" by (by100 blast)
      hence "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> 0" by (by100 simp)
      ultimately have "card {i. i < length scheme \<and> fst (scheme ! i) = a} = 2" by (by100 blast)
      with \<open>{i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = {i. i < length scheme \<and> fst (scheme ! i) = a}\<close>
      show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Positions with label a in scheme are exactly {p,q}.\<close>
    have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
    proof -
      have "card {p, q} = 2" using hp(3) by (by100 simp)
      have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}"
        using hp(1,2,4,5) by (by100 blast)
      have "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
      from hproper have "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<in> {0, 2}" by (by100 blast)
      moreover have "{k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> {}"
        using hp(1,4) by (by100 blast)
      hence "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> 0" by (by100 simp)
      ultimately have "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2" by (by100 blast)
      from card_seteq[OF \<open>finite {k. k < length scheme \<and> fst (scheme ! k) = a}\<close>
          \<open>{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}\<close>]
          this \<open>card {p, q} = 2\<close>
      show ?thesis by (by100 simp)
    qed
    have h3: "\<forall>i < length scheme1. fst (scheme1 ! i) = a \<longrightarrow> snd (scheme1 ! i) = True"
    proof (cases "snd (scheme ! p)")
      case True
      hence "scheme1 = scheme" unfolding scheme1_def by (by100 simp)
      show ?thesis
      proof (intro allI impI)
        fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
        hence "i < length scheme" "fst (scheme ! i) = a"
          using \<open>scheme1 = scheme\<close> hlen1 hlen by (by100 simp)+
        hence "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 blast)
        hence "i = p \<or> i = q" using honly_pq by (by100 blast)
        thus "snd (scheme1 ! i) = True"
          using \<open>scheme1 = scheme\<close> True hp(6) by (by100 blast)
      qed
    next
      case False
      hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
        unfolding scheme1_def by (by100 simp)
      show ?thesis
      proof (intro allI impI)
        fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
        have "i < length scheme" using \<open>i < length scheme1\<close> hlen1 hlen by (by100 simp)
        have "scheme1 ! i = (\<lambda>(l,b). (l, if l = a then \<not>b else b)) (scheme ! i)"
          using hsch1 \<open>i < length scheme\<close> by (by100 simp)
        have "fst (scheme ! i) = a"
          using hfst_preserved \<open>i < length scheme1\<close> \<open>fst (scheme1 ! i) = a\<close> by (by100 simp)
        hence "snd (scheme1 ! i) = (\<not> snd (scheme ! i))"
          using hsch1 \<open>i < length scheme\<close> by (cases "scheme ! i") (by100 simp)
        moreover have "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}"
          using \<open>i < length scheme\<close> \<open>fst (scheme ! i) = a\<close> by (by100 blast)
        hence "i = p \<or> i = q" using honly_pq by (by100 blast)
        hence "snd (scheme ! i) = snd (scheme ! p)" using hp(6) by (by100 blast)
        hence "snd (scheme ! i) = False" using False by (by100 simp)
        ultimately show "snd (scheme1 ! i) = True" by (by100 simp)
      qed
    qed
    have h1: "(a, True) \<in> set scheme1"
    proof -
      have "p < length scheme1" using hp(1) hlen1 hlen by (by100 simp)
      hence "scheme1 ! p \<in> set scheme1" by (by100 simp)
      have "fst (scheme1 ! p) = a" using hfst_preserved \<open>p < length scheme1\<close> hp(4) by (by100 blast)
      have "snd (scheme1 ! p) = True" using h3 \<open>p < length scheme1\<close> \<open>fst (scheme1 ! p) = a\<close> by (by100 blast)
      obtain f s where hfs: "scheme1 ! p = (f, s)" by (cases "scheme1 ! p")
      hence "f = a" using \<open>fst (scheme1 ! p) = a\<close> by (by100 simp)
      hence "s = True" using \<open>snd (scheme1 ! p) = True\<close> hfs by (by100 simp)
      hence "scheme1 ! p = (a, True)" using hfs \<open>f = a\<close> by (by100 simp)
      thus ?thesis using \<open>scheme1 ! p \<in> set scheme1\<close> by (by100 simp)
    qed
    have "scheme1 \<noteq> []"
    proof
      assume "scheme1 = []" hence "length scheme1 = 0" by (by100 simp)
      thus False using hlen1 by (by100 simp)
    qed
    have hproper1: "\<forall>label. card {i. i < length scheme1 \<and> fst (scheme1 ! i) = label} \<in> {0, 2}"
    proof -
      have "\<And>label. {i. i < length scheme1 \<and> fst (scheme1 ! i) = label}
          = {i. i < length scheme \<and> fst (scheme ! i) = label}"
        using hfst_preserved hlen1 hlen by (by100 force)
      thus ?thesis using hproper by (by100 simp)
    qed
    from bring_projective_pair_to_front[OF h1 h2 h3 \<open>scheme1 \<noteq> []\<close> hproper1]
    obtain rest where hrest_eq: "top1_scheme_equiv scheme1 ([(a, True), (a, True)] @ rest)"
        and hrest_len: "length rest = length scheme1 - 2"
        and hrest_ne: "\<forall>e \<in> set rest. fst e \<noteq> a"
        and hrest_fst: "fst ` set rest \<subseteq> fst ` set scheme1"
        and hrest_proper: "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
      by blast
    have "length scheme1 = 4" unfolding scheme1_def using hlen by (by100 simp)
    hence "length rest = 2" using hrest_len by (by100 simp)
    have "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
      using scheme_equiv_trans[OF hequiv1 hrest_eq] by (by100 blast)
    moreover have "fst ` set scheme1 \<subseteq> fst ` set scheme"
    proof (intro subsetI)
      fix l assume "l \<in> fst ` set scheme1"
      then obtain e where "e \<in> set scheme1" "fst e = l" by (by100 blast)
      then obtain i where "i < length scheme1" "scheme1 ! i = e"
        by (simp add: in_set_conv_nth) (by100 blast)
      hence "fst (scheme1 ! i) = l" using \<open>fst e = l\<close> by (by100 simp)
      hence "fst (scheme ! i) = l" using hfst_preserved \<open>i < length scheme1\<close> by (by100 simp)
      have "i < length scheme" using \<open>i < length scheme1\<close> hlen1 hlen by (by100 simp)
      hence "scheme ! i \<in> set scheme" by (by100 simp)
      thus "l \<in> fst ` set scheme" using \<open>fst (scheme ! i) = l\<close> by (by100 force)
    qed
    hence "fst ` set rest \<subseteq> fst ` set scheme" using hrest_fst by (by100 blast)
    ultimately have "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest)
        \<and> length rest = 2 \<and> (\<forall>e \<in> set rest. fst e \<noteq> a)
        \<and> fst ` set rest \<subseteq> fst ` set scheme"
      using \<open>length rest = 2\<close> hrest_ne by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain rest where hrest: "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
      "length rest = 2" "\<forall>e \<in> set rest. fst e \<noteq> a"
      "fst ` set rest \<subseteq> fst ` set scheme" by (by100 blast)
  \<comment> \<open>Positions with label a in scheme are exactly {p,q} (re-derive in outer scope).\<close>
  have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
  proof -
    have "card {p, q} = 2" using hp(3) by (by100 simp)
    have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}"
      using hp(1,2,4,5) by (by100 blast)
    have "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
    from hproper have "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<in> {0, 2}" by (by100 blast)
    moreover have "{k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> {}"
      using hp(1,4) by (by100 blast)
    hence "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> 0" by (by100 simp)
    ultimately have "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2" by (by100 blast)
    from card_seteq[OF \<open>finite {k. k < length scheme \<and> fst (scheme ! k) = a}\<close>
        \<open>{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}\<close>]
        this \<open>card {p, q} = 2\<close>
    show ?thesis by (by100 simp)
  qed
  \<comment> \<open>rest = [(b, d1), (b, d2)] for some b \<noteq> a.\<close>
  obtain b d1 d2 where hrest_form: "rest = [(b, d1), (b, d2)]" "b \<noteq> a"
  proof -
    obtain e0 e1 where he: "rest = [e0, e1]"
      using hrest(2) by (cases rest, by100 simp, cases "tl rest", by100 simp, by100 simp)
    have "fst e0 \<noteq> a" using hrest(3) he by (by100 simp)
    have "fst e1 \<noteq> a" using hrest(3) he by (by100 simp)
    \<comment> \<open>fst e0 = fst e1: from properness, scheme has exactly one non-a label.\<close>
    have "fst e0 = fst e1"
    proof -
      \<comment> \<open>Get a non-{p,q} position r1.\<close>
      have hpq_sub: "{p, q} \<subseteq> {0..<4::nat}" using hp(1,2) hlen by (by100 simp)
      have hcard_pq: "card {p, q} = 2" using hp(3) by (by100 simp)
      have "card ({0..<4::nat} - {p, q}) = 2"
      proof -
        have "card {0..<4::nat} = 4" by (by100 simp)
        have "finite {p, q}" by (by100 simp)
        have "card ({0..<4::nat} - {p, q}) = card {0..<4::nat} - card {p, q}"
          using card_Diff_subset[OF \<open>finite {p, q}\<close> hpq_sub] .
        thus ?thesis using hcard_pq by (by100 simp)
      qed
      hence "({0..<4::nat} - {p, q}) \<noteq> {}" by (by100 force)
      then obtain r1 where hr1: "r1 \<in> {0..<4::nat} - {p, q}" by (by100 blast)
      hence hr1_props: "r1 < 4" "r1 \<noteq> p" "r1 \<noteq> q" by (by100 simp)+
      have "fst (scheme ! r1) \<noteq> a"
      proof -
        have "r1 \<notin> {p, q}" using hr1_props(2,3) by (by100 blast)
        hence "r1 \<notin> {k. k < length scheme \<and> fst (scheme ! k) = a}" using honly_pq by (by100 blast)
        moreover have "r1 < length scheme" using hr1_props(1) hlen by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      qed
      \<comment> \<open>By properness: every non-a label in scheme appears 0 or 2 times.
         fst(scheme!r1) is one such label, appearing at least once (position r1).
         So it must appear exactly 2 times. With only 2 non-{p,q} positions total,
         both must have this same label.\<close>
      define b0 where "b0 = fst (scheme ! r1)"
      have "b0 \<noteq> a" using \<open>fst (scheme ! r1) \<noteq> a\<close> unfolding b0_def by (by100 simp)
      \<comment> \<open>fst ` set scheme \<subseteq> {a, b0}: every element is at position p or q (fst=a) or at a non-{p,q} position.\<close>
      have hfst_sub: "fst ` set scheme \<subseteq> {a, b0}"
      proof (intro subsetI)
        fix l assume "l \<in> fst ` set scheme"
        then obtain e where "e \<in> set scheme" "fst e = l" by (by100 blast)
        then obtain k where "k < length scheme" "scheme ! k = e"
          by (simp add: in_set_conv_nth) (by100 blast)
        hence "fst (scheme ! k) = l" using \<open>fst e = l\<close> by (by100 simp)
        show "l \<in> {a, b0}"
        proof (cases "k \<in> {p, q}")
          case True
          hence "fst (scheme ! k) = a" using hp(4,5) by (by100 blast)
          thus ?thesis using \<open>fst (scheme ! k) = l\<close> by (by100 simp)
        next
          case False
          hence "k \<notin> {i. i < length scheme \<and> fst (scheme ! i) = a}" using honly_pq by (by100 blast)
          hence "fst (scheme ! k) \<noteq> a" using \<open>k < length scheme\<close> by (by100 blast)
          \<comment> \<open>k is a non-{p,q} position. By properness, fst(scheme!k) appears 2 times.
             But fst(scheme!k) \<noteq> a, so it only appears at non-{p,q} positions.
             There are exactly 2 non-{p,q} positions (r1 and one other).
             Since fst(scheme!k) appears 2 times in only 2 positions, one must be r1.
             So fst(scheme!k) = fst(scheme!r1) = b0.\<close>
          have "card {i. i < length scheme \<and> fst (scheme ! i) = l} \<in> {0, 2}"
            using hproper by (by100 blast)
          moreover have "k \<in> {i. i < length scheme \<and> fst (scheme ! i) = l}"
            using \<open>k < length scheme\<close> \<open>fst (scheme ! k) = l\<close> by (by100 blast)
          hence "{i. i < length scheme \<and> fst (scheme ! i) = l} \<noteq> {}" by (by100 blast)
          hence "card {i. i < length scheme \<and> fst (scheme ! i) = l} \<noteq> 0" by (by100 simp)
          ultimately have hcard_l: "card {i. i < length scheme \<and> fst (scheme ! i) = l} = 2"
            by (by100 blast)
          \<comment> \<open>Since l \<noteq> a, all l-positions are non-{p,q}.\<close>
          have "{i. i < length scheme \<and> fst (scheme ! i) = l} \<subseteq> {0..<4} - {p, q}"
          proof (intro subsetI)
            fix i assume "i \<in> {i. i < length scheme \<and> fst (scheme ! i) = l}"
            hence "i < length scheme" "fst (scheme ! i) = l" by (by100 simp)+
            have "i \<notin> {p, q}"
            proof
              assume "i \<in> {p, q}"
              hence "fst (scheme ! i) = a" using hp(4,5) by (by100 blast)
              thus False using \<open>fst (scheme ! i) = l\<close> \<open>fst (scheme ! k) \<noteq> a\<close>
                  \<open>fst (scheme ! k) = l\<close> by (by100 simp)
            qed
            thus "i \<in> {0..<4} - {p, q}" using \<open>i < length scheme\<close> hlen by (by100 simp)
          qed
          \<comment> \<open>card of l-positions = 2, and they are contained in a set of card 2.
             So l-positions = {0..<4} - {p,q}, which contains r1.\<close>
          hence "{i. i < length scheme \<and> fst (scheme ! i) = l} = {0..<4} - {p, q}"
          proof -
            have "finite ({0..<4::nat} - {p, q})" by (by100 simp)
            have "card ({0..<4::nat} - {p, q}) = 2" using \<open>card ({0..<4::nat} - {p, q}) = 2\<close> .
            from card_seteq[OF \<open>finite ({0..<4::nat} - {p,q})\<close>
                \<open>{i. i < length scheme \<and> fst (scheme ! i) = l} \<subseteq> {0..<4} - {p, q}\<close>]
                hcard_l this
            show ?thesis by (by100 simp)
          qed
          hence "r1 \<in> {i. i < length scheme \<and> fst (scheme ! i) = l}" using hr1 hlen by (by100 simp)
          hence "fst (scheme ! r1) = l" by (by100 blast)
          thus ?thesis unfolding b0_def using \<open>fst (scheme ! r1) = l\<close> by (by100 simp)
        qed
      qed
      \<comment> \<open>Since fst ` set rest \<subseteq> fst ` set scheme \<subseteq> {a, b0} and fst e \<noteq> a for e \<in> rest:\<close>
      have "fst e0 \<in> fst ` set rest" using he by (by100 simp)
      hence "fst e0 \<in> fst ` set scheme" using hrest(4) by (by100 blast)
      hence "fst e0 \<in> {a, b0}" using hfst_sub by (by100 blast)
      hence "fst e0 = b0" using \<open>fst e0 \<noteq> a\<close> by (by100 blast)
      have "fst e1 \<in> fst ` set rest" using he by (by100 simp)
      hence "fst e1 \<in> fst ` set scheme" using hrest(4) by (by100 blast)
      hence "fst e1 \<in> {a, b0}" using hfst_sub by (by100 blast)
      hence "fst e1 = b0" using \<open>fst e1 \<noteq> a\<close> by (by100 blast)
      thus ?thesis using \<open>fst e0 = b0\<close> by (by100 simp)
    qed
    have "rest = [(fst e0, snd e0), (fst e0, snd e1)]" using he \<open>fst e0 = fst e1\<close>
      by (cases e0, cases e1) (by100 simp)
    thus ?thesis using \<open>fst e0 \<noteq> a\<close> by (rule that)
  qed
  show ?thesis
  proof (cases "d1 = d2")
    case True
    \<comment> \<open>Same direction: scheme ~ [(a,T),(a,T),(b,d1),(b,d1)] ~ projective m=2.\<close>
    have "top1_scheme_equiv scheme (top1_m_projective_scheme 2)"
    proof -
      \<comment> \<open>Step 1: scheme ~ [(a,T),(a,T),(b,d1),(b,d1)] from hrest + d1=d2.\<close>
      have s1: "top1_scheme_equiv scheme ([(a,True),(a,True)] @ [(b,d1),(b,d1)])"
        using hrest(1) hrest_form(1) True by (by100 simp)
      \<comment> \<open>Step 2: flip\_label b if d1 = False.\<close>
      have s2: "top1_scheme_equiv ([(a,True),(a,True),(b,d1),(b,d1)])
          [(a,True),(a,True),(b,True),(b,True)]"
      proof (cases d1)
        case True thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
      next
        case False
        have hop: "top1_scheme_equiv
            [(a,True),(a,True),(b,d1),(b,d1)] [(a,True),(a,True),(b,True),(b,True)]"
        proof -
          have "d1 = False" using False by (by100 simp)
          hence "[(a,True),(a,True),(b,d1),(b,d1)] = [(a,True),(a,True),(b,False),(b,False)]"
            by (by100 simp)
          moreover have "top1_scheme_equiv [(a,True),(a,True),(b,False),(b,False)]
              [(a,True),(a,True),(b,True),(b,True)]"
          proof (rule elementary_imp_equiv)
            have "map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,False)]
                = [(a,True),(a,True),(b,True),(b,True)]"
              using hrest_form(2) by (by100 simp)
            have hmap: "map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,False)]
                = [(a,True),(a,True),(b,True),(b,True)]"
              using hrest_form(2) by (by100 simp)
            from top1_elementary_scheme_operation.flip_label[of "[(a,True),(a,True),(b,False),(b,False)]" b]
            have "top1_elementary_scheme_operation [(a,True),(a,True),(b,False),(b,False)]
                (map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,False)])" .
            show "top1_elementary_scheme_operation [(a,True),(a,True),(b,False),(b,False)]
                [(a,True),(a,True),(b,True),(b,True)]"
              by (subst hmap[symmetric]) (rule top1_elementary_scheme_operation.flip_label)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        show ?thesis using hop .
      qed
      \<comment> \<open>Step 3: relabel to standard labels 0, 1.\<close>
      \<comment> \<open>Use fresh temp label to avoid collisions.\<close>
      define temp :: nat where "temp = Suc (max a b)"
      have htemp_ne_a: "temp \<noteq> a" unfolding temp_def by (by100 simp)
      have htemp_ne_b: "temp \<noteq> b" unfolding temp_def by (by100 simp)
      \<comment> \<open>Relabel b \<rightarrow> temp.\<close>
      have r1: "top1_elementary_scheme_operation [(a,True),(a,True),(b,True),(b,True)]
          (map (\<lambda>(l,bo). (if l = b then temp else l, bo)) [(a,True),(a,True),(b,True),(b,True)])"
        by (rule top1_elementary_scheme_operation.relabel)
      have "map (\<lambda>(l,bo). (if l = b then temp else l, bo)) [(a,True),(a,True),(b,True),(b,True)]
          = [(a,True),(a,True),(temp,True),(temp,True)]"
        using hrest_form(2) by (by100 simp)
      hence r1': "top1_scheme_equiv [(a,True),(a,True),(b,True),(b,True)]
          [(a,True),(a,True),(temp,True),(temp,True)]"
        using r1 unfolding top1_scheme_equiv_def by (by100 simp)
      \<comment> \<open>Relabel a \<rightarrow> 0.\<close>
      have r2: "top1_elementary_scheme_operation [(a,True),(a,True),(temp,True),(temp,True)]
          (map (\<lambda>(l,bo). (if l = a then 0 else l, bo)) [(a,True),(a,True),(temp,True),(temp,True)])"
        by (rule top1_elementary_scheme_operation.relabel)
      have "map (\<lambda>(l,bo). (if l = a then 0 else l, bo)) [(a,True),(a,True),(temp,True),(temp,True)]
          = [(0,True),(0,True),(temp,True),(temp,True)]"
        using htemp_ne_a by (by100 simp)
      hence r2': "top1_scheme_equiv [(a,True),(a,True),(temp,True),(temp,True)]
          [(0,True),(0,True),(temp,True),(temp,True)]"
        using r2 unfolding top1_scheme_equiv_def by (by100 simp)
      \<comment> \<open>Relabel temp \<rightarrow> 1.\<close>
      have r3: "top1_elementary_scheme_operation [(0,True),(0,True),(temp,True),(temp,True)]
          (map (\<lambda>(l,bo). (if l = temp then 1 else l, bo)) [(0,True),(0,True),(temp,True),(temp,True)])"
        by (rule top1_elementary_scheme_operation.relabel)
      have "map (\<lambda>(l,bo). (if l = temp then 1 else l, bo)) [(0,True),(0,True),(temp,True),(temp,True)]
          = [(0,True),(0,True),(1,True),(1,True)]"
        using htemp_ne_a htemp_ne_b temp_def by (by100 simp)
      hence r3': "top1_scheme_equiv [(0,True),(0,True),(temp,True),(temp,True)]
          [(0,True),(0,True),(1,True),(1,True)]"
        using r3 unfolding top1_scheme_equiv_def by (by100 simp)
      \<comment> \<open>[(0,T),(0,T),(1,T),(1,T)] = top1\_m\_projective\_scheme 2.\<close>
      have "[(0::nat,True),(0,True),(1,True),(1,True)] = top1_m_projective_scheme 2"
        unfolding top1_m_projective_scheme_def by (simp add: eval_nat_numeral)
      \<comment> \<open>Chain everything.\<close>
      \<comment> \<open>Chain using scheme\\_equiv transitivity (avoid meson on complex types).\<close>
      have s1': "top1_scheme_equiv scheme [(a,True),(a,True),(b,d1),(b,d1)]"
        using s1 by (by100 simp)
      have c1: "top1_scheme_equiv scheme [(a,True),(a,True),(b,True),(b,True)]"
        using scheme_equiv_trans[OF s1' s2] .
      have r12: "top1_scheme_equiv [(a,True),(a,True),(b,True),(b,True)]
          [(0,True),(0,True),(temp,True),(temp,True)]"
        using scheme_equiv_trans[OF r1' r2'] .
      have r123: "top1_scheme_equiv [(a,True),(a,True),(b,True),(b,True)]
          [(0,True),(0,True),(1,True),(1,True)]"
        using scheme_equiv_trans[OF r12 r3'] .
      have c2: "top1_scheme_equiv scheme [(0,True),(0,True),(1,True),(1,True)]"
        using scheme_equiv_trans[OF c1 r123] .
      thus ?thesis using \<open>[(0::nat,True),(0,True),(1,True),(1,True)] = top1_m_projective_scheme 2\<close>
        by (by100 simp)
    qed
    moreover have "top1_is_projective_scheme (top1_m_projective_scheme 2) 2"
      unfolding top1_is_projective_scheme_def by (by100 simp)
    ultimately have "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
    proof -
      assume h1: "top1_scheme_equiv scheme (top1_m_projective_scheme 2)"
        and h2: "top1_is_projective_scheme (top1_m_projective_scheme 2) 2"
      have "(2::nat) > 0" by (by100 simp)
      thus ?thesis using h1 h2 by (by100 blast)
    qed
    thus ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>Opposite direction: scheme ~ [(a,T),(a,T),(b,d1),(b,\\<not>d1)].
       The pair (b,d1),(b,\\<not>d1) is inverse. Cancel \<Rightarrow> [(a,T),(a,T)] ~ projective m=1.\<close>
    have "top1_scheme_equiv scheme (top1_m_projective_scheme 1)"
    proof -
      \<comment> \<open>d1 \<noteq> d2 and rest = [(b,d1),(b,d2)]. So d2 = \<not>d1.\<close>
      have hd2: "d2 = (\<not> d1)" using False by (cases d1, cases d2) (by100 simp)+
      \<comment> \<open>Step 1: scheme ~ [(a,T),(a,T),(b,d1),(b,\<not>d1)] from hrest.\<close>
      have s1: "top1_scheme_equiv scheme ([(a,True),(a,True)] @ [(b,d1), (b, \<not>d1)])"
        using hrest(1) hrest_form(1) hd2 by (by100 simp)
      \<comment> \<open>Step 2: cancel the inverse pair (b,d1),(b,\<not>d1).\<close>
      have "top1_inverse_edge (b, d1) = (b, \<not>d1)"
        unfolding top1_inverse_edge_def by (by100 simp)
      have s2: "top1_elementary_scheme_operation
          ([(a,True),(a,True)] @ [(b,d1), top1_inverse_edge (b,d1)] @ [])
          ([(a,True),(a,True)] @ [])"
        by (rule top1_elementary_scheme_operation.cancel)
      hence s2': "top1_scheme_equiv ([(a,True),(a,True)] @ [(b,d1),(b, \<not>d1)]) [(a,True),(a,True)]"
        using \<open>top1_inverse_edge (b, d1) = (b, \<not>d1)\<close>
        unfolding top1_scheme_equiv_def by (by100 simp)
      \<comment> \<open>Step 3: relabel a \<rightarrow> 0.\<close>
      have s3: "top1_elementary_scheme_operation [(a,True),(a,True)]
          (map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)])"
        by (rule top1_elementary_scheme_operation.relabel)
      have "map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)] = [(0,True),(0,True)]"
        by (by100 simp)
      hence s3': "top1_scheme_equiv [(a,True),(a,True)] [(0,True),(0,True)]"
        using s3 unfolding top1_scheme_equiv_def by (by100 simp)
      \<comment> \<open>[(0,T),(0,T)] = top1\\_m\\_projective\\_scheme 1.\<close>
      have "[(0::nat,True),(0,True)] = top1_m_projective_scheme 1"
        unfolding top1_m_projective_scheme_def by (by100 simp)
      \<comment> \<open>Chain: scheme ~ aa@bb' ~ aa ~ [(0,T),(0,T)] = proj 1.\<close>
      from s1 s2' have "top1_scheme_equiv scheme [(a,True),(a,True)]"
        unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
      from this s3' have "top1_scheme_equiv scheme [(0,True),(0,True)]"
        unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
      thus ?thesis using \<open>[(0::nat,True),(0,True)] = top1_m_projective_scheme 1\<close> by (by100 simp)
    qed
    moreover have "top1_is_projective_scheme (top1_m_projective_scheme 1) 1"
      unfolding top1_is_projective_scheme_def by (by100 simp)
    ultimately have "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
    proof -
      assume h1: "top1_scheme_equiv scheme (top1_m_projective_scheme 1)"
        and h2: "top1_is_projective_scheme (top1_m_projective_scheme 1) 1"
      have "(1::nat) > 0" by (by100 simp)
      thus ?thesis using h1 h2 by (by100 blast)
    qed
    thus ?thesis by (by100 blast)
  qed
qed

\<comment> \<open>Valid version of projective\\_len4\\_base.
   Uses valid\\_extract\\_projective\\_pair for the core decomposition.\<close>
lemma valid_projective_len4_base:
  fixes scheme :: "(nat \<times> bool) list"
  assumes hlen: "length scheme = 4"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      and hproj: "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
  shows "(\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)"
proof -
  \<comment> \<open>Step 1: Flip projective label to True.\<close>
  from hproj obtain a p q where hp: "p < length scheme" "q < length scheme" "p \<noteq> q"
      "fst (scheme!p) = a" "fst (scheme!q) = a" "snd (scheme!p) = snd (scheme!q)"
    by (by100 blast)
  define scheme1 where "scheme1 = (if snd (scheme!p) then scheme
      else map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme)"
  have hequiv1: "top1_valid_scheme_equiv scheme scheme1"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def top1_valid_scheme_equiv_def by (by100 simp)
  next
    case False thus ?thesis unfolding scheme1_def
      using valid_imp_equiv[OF top1_valid_scheme_operation.v_flip_label[of scheme a]]
      by (by100 simp)
  qed
  \<comment> \<open>scheme1 conditions for valid\\_bring.\<close>
  have hlen1: "length scheme1 = 4" unfolding scheme1_def using hlen by (by100 simp)
  have hfst_preserved: "\<forall>i < length scheme1. fst (scheme1 ! i) = fst (scheme ! i)"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def by (by100 simp)
  next
    case False show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1"
      hence "i < length scheme" using hlen1 hlen by (by100 simp)
      obtain l b where hlb: "scheme ! i = (l, b)" by (cases "scheme ! i")
      show "fst (scheme1 ! i) = fst (scheme ! i)"
        using False \<open>i < length scheme\<close> hlb unfolding scheme1_def by (by100 simp)
    qed
  qed
  have h1_ne: "scheme1 \<noteq> []" using hlen1 by (by100 auto)
  have h1_proper: "\<forall>label. card {i. i < length scheme1 \<and> fst (scheme1 ! i) = label} \<in> {0, 2}"
  proof -
    have "\<And>label. {i. i < length scheme1 \<and> fst (scheme1 ! i) = label}
        = {i. i < length scheme \<and> fst (scheme ! i) = label}"
      using hfst_preserved hlen1 hlen by (by100 force)
    thus ?thesis using hproper by (by100 simp)
  qed
  have h1_card: "card {i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = 2"
  proof -
    have "{i. i < length scheme1 \<and> fst (scheme1 ! i) = a}
        = {i. i < length scheme \<and> fst (scheme ! i) = a}"
      using hfst_preserved hlen1 hlen by (by100 force)
    moreover have "p \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}" using hp(1,4) by (by100 blast)
    hence "{i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> {}" by (by100 blast)
    hence "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> 0" by (by100 simp)
    moreover from hproper have "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<in> {0, 2}" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have h1_dir: "\<forall>i < length scheme1. fst (scheme1 ! i) = a \<longrightarrow> snd (scheme1 ! i) = True"
  proof (cases "snd (scheme ! p)")
    case True
    hence "scheme1 = scheme" unfolding scheme1_def by (by100 simp)
    have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
    proof -
      have "card {p, q} = 2" using hp(3) by (by100 simp)
      have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}" using hp(1,2,4,5) by (by100 blast)
      have "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
      have "{k. k < length scheme1 \<and> fst (scheme1 ! k) = a}
          = {k. k < length scheme \<and> fst (scheme ! k) = a}"
        using \<open>scheme1 = scheme\<close> hlen1 hlen by (by100 simp)
      hence hcard_a: "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2"
        using h1_card by (by100 simp)
      from card_subset_eq[OF \<open>finite _\<close> \<open>{p,q} \<subseteq> _\<close>] \<open>card {p,q} = 2\<close> hcard_a
      show ?thesis by (by100 simp)
    qed
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
      hence "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}" using \<open>scheme1 = scheme\<close> hlen1 hlen by (by100 blast)
      hence "i = p \<or> i = q" using honly_pq by (by100 blast)
      thus "snd (scheme1 ! i) = True" using \<open>scheme1 = scheme\<close> True hp(6) by (by100 blast)
    qed
  next
    case False
    hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
      hence "i < length scheme" using hlen1 hlen by (by100 simp)
      obtain l b where hlb: "scheme ! i = (l, b)" by (cases "scheme ! i")
      have "scheme1 ! i = (l, if l = a then \<not> b else b)" using hsch1 \<open>i < length scheme\<close> hlb by (by100 simp)
      hence "fst (scheme1 ! i) = l" by (by100 simp)
      hence "l = a" using \<open>fst (scheme1 ! i) = a\<close> by (by100 simp)
      have "i = p \<or> i = q"
      proof -
        have "{k. k < length scheme1 \<and> fst (scheme1 ! k) = a}
            = {k. k < length scheme \<and> fst (scheme ! k) = a}"
          using hfst_preserved hlen1 hlen by (by100 force)
        hence hcard_a: "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2"
          using h1_card by (by100 simp)
        have "card {p, q} = 2" using hp(3) by (by100 simp)
        have hpq_sub: "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}" using hp(1,2,4,5) by (by100 blast)
        have hfin_a: "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
        have "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
          using card_subset_eq[OF hfin_a hpq_sub] hcard_a \<open>card {p,q} = 2\<close> by (by100 simp)
        have "fst (scheme ! i) = a" using hlb \<open>l = a\<close> by (by100 simp)
        hence "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}" using \<open>i < length scheme\<close> by (by100 blast)
        thus ?thesis using \<open>_ = {p, q}\<close> by (by100 blast)
      qed
      hence "snd (scheme ! i) = snd (scheme ! p)" using hp(6) by (by100 blast)
      hence "b = False" using hlb False by (by100 simp)
      hence "scheme1 ! i = (a, True)" using \<open>scheme1 ! i = (l, if l = a then \<not> b else b)\<close> \<open>l = a\<close> by (by100 simp)
      thus "snd (scheme1 ! i) = True" by (by100 simp)
    qed
  qed
  have h1_in: "(a, True) \<in> set scheme1"
  proof -
    have "p < length scheme1" using hp(1) hlen1 hlen by (by100 simp)
    hence "scheme1 ! p \<in> set scheme1" by (by100 simp)
    have "fst (scheme1 ! p) = a" using hfst_preserved \<open>p < length scheme1\<close> hp(4) by (by100 blast)
    have "snd (scheme1 ! p) = True" using h1_dir \<open>p < length scheme1\<close> \<open>fst (scheme1 ! p) = a\<close> by (by100 blast)
    obtain f s where hfs: "scheme1 ! p = (f, s)" by (cases "scheme1 ! p")
    have "f = a" using hfs \<open>fst (scheme1 ! p) = a\<close> by (by100 simp)
    have "s = True" using hfs \<open>snd (scheme1 ! p) = True\<close> by (by100 simp)
    hence "scheme1 ! p = (a, True)" using hfs \<open>f = a\<close> by (by100 simp)
    thus ?thesis using \<open>scheme1 ! p \<in> set scheme1\<close> by (by100 simp)
  qed
  \<comment> \<open>Step 2: Bring to front.\<close>
  from valid_bring_projective_pair_to_front_full[OF h1_in h1_card h1_dir h1_ne h1_proper]
  obtain rest where hrest: "top1_valid_scheme_equiv scheme1 ([(a, True), (a, True)] @ rest)"
      "length rest = length scheme1 - 2" "\<forall>e \<in> set rest. fst e \<noteq> a"
      "fst ` set rest \<subseteq> fst ` set scheme1"
      "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}" by blast
  have hrest_len: "length rest = 2" using hrest(2) hlen1 by (by100 simp)
  \<comment> \<open>Step 3: rest has 2 elements. The result [(a,T),(a,T)] @ rest is projective m=1 or m=2.\<close>
  \<comment> \<open>We use valid\\_proj\\_append\\_pair (defined later in file, but usable since scheme is nat).\<close>
  have "top1_valid_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
    using valid_equiv_trans[OF hequiv1 hrest(1)] .
  \<comment> \<open>If rest is projective (same direction): [(a,T),(a,T),(b,d),(b,d)] \\<sim> proj\\_2.
     If rest is torus (opposite direction): cancel gives [(a,T),(a,T)] \\<sim> proj\\_1.
     Detailed case analysis deferred.\<close>
  \<comment> \<open>rest has 2 elements, proper. Decompose rest = [r0, r1].\<close>
  obtain r0 r1 where hrest_eq: "rest = [r0, r1]"
  proof -
    from hrest_len obtain x xs where "rest = x # xs" by (cases rest) (by100 auto)+
    then obtain y ys where "xs = y # ys" using hrest_len by (cases xs) (by100 auto)+
    hence "ys = []" using hrest_len \<open>rest = x # xs\<close> by (by100 simp)
    thus ?thesis using that \<open>rest = x # xs\<close> \<open>xs = y # ys\<close> by (by100 simp)
  qed
  \<comment> \<open>Both elements have the same label (from properness + length 2).\<close>
  obtain b d1 d2 where hr0: "r0 = (b, d1)" and hr1: "r1 = (b, d2)" and hb_ne_a: "b \<noteq> a"
  proof -
    obtain b1 d1 where "r0 = (b1, d1)" by (cases r0)
    obtain b2 d2 where "r1 = (b2, d2)" by (cases r1)
    have "b1 = b2"
    proof -
      have "card {i. i < length rest \<and> fst (rest ! i) = b1} \<in> {0, 2}" using hrest(5) by (by100 blast)
      have "0 < length rest" "fst (rest ! 0) = b1" using hrest_eq \<open>r0 = (b1, d1)\<close> by (by100 simp)+
      hence "{i. i < length rest \<and> fst (rest ! i) = b1} \<noteq> {}" by (by100 blast)
      hence "card {i. i < length rest \<and> fst (rest ! i) = b1} \<noteq> 0" by (by100 simp)
      hence hcard_b1: "card {i. i < length rest \<and> fst (rest ! i) = b1} = 2"
        using \<open>card _ \<in> {0, 2}\<close> by (by100 blast)
      have hsub: "{i. i < length rest \<and> fst (rest ! i) = b1} \<subseteq> {0, 1}"
        using hrest_len by (by100 auto)
      have hfin01: "finite {0::nat, 1}" by (by100 simp)
      have hcard01: "card {0::nat, 1} = 2" by (by100 simp)
      from card_subset_eq[OF hfin01 hsub]
      have "{i. i < length rest \<and> fst (rest ! i) = b1} = {0, 1}"
        using hcard_b1 hcard01 by (by100 simp)
      hence "1 \<in> {i. i < length rest \<and> fst (rest ! i) = b1}" by (by100 blast)
      hence "fst (rest ! 1) = b1" by (by100 blast)
      thus "b1 = b2" using hrest_eq \<open>r1 = (b2, d2)\<close> by (by100 simp)
    qed
    moreover have "b1 \<noteq> a" using hrest(3) hrest_eq \<open>r0 = (b1, d1)\<close> by (by100 simp)
    ultimately show ?thesis using that \<open>r0 = (b1, d1)\<close> \<open>r1 = (b2, d2)\<close> by (by100 blast)
  qed
  show ?thesis
  proof (cases "d1 = d2")
    case True
    \<comment> \<open>Same direction: [(a,T),(a,T),(b,d),(b,d)] is projective m=2 via alpha-rename.\<close>
    \<comment> \<open>First flip b to True if needed.\<close>
    have "top1_valid_scheme_equiv ([(a,True),(a,True)] @ rest) ([(a,True),(a,True),(b,True),(b,True)])"
    proof (cases "d1 = True")
      case True
      hence "rest = [(b,True),(b,True)]" using hrest_eq hr0 hr1 \<open>d1 = d2\<close> by (by100 simp)
      thus ?thesis unfolding top1_valid_scheme_equiv_def by (by100 simp)
    next
      case False
      hence "d1 = False" by (by100 simp)
      hence "rest = [(b,False),(b,False)]" using hrest_eq hr0 hr1 \<open>d1 = d2\<close> by (by100 simp)
      \<comment> \<open>Flip label b: [(a,T),(a,T),(b,F),(b,F)] ~ [(a,T),(a,T),(b,T),(b,T)].\<close>
      have hop: "top1_valid_scheme_operation [(a,True),(a,True),(b,False),(b,False)]
          (map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,False)])"
        by (rule top1_valid_scheme_operation.v_flip_label)
      have hmap: "map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,False)]
          = [(a,True),(a,True),(b,True),(b,True)]" using hb_ne_a by (by100 simp)
      from valid_imp_equiv[OF hop[unfolded hmap]]
      show ?thesis using \<open>rest = [(b,False),(b,False)]\<close> by (by100 simp)
    qed
    hence "top1_valid_scheme_equiv scheme ([(a,True),(a,True),(b,True),(b,True)])"
      using valid_equiv_trans \<open>top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ rest)\<close> by (by100 blast)
    \<comment> \<open>Alpha-rename {a,b} to {0,1}: this IS proj\\_2.\<close>
    moreover have "top1_valid_scheme_equiv [(a,True),(a,True),(b,True),(b,True)] (top1_m_projective_scheme 2)"
    proof -
      define \<rho> :: "nat \<Rightarrow> nat" where "\<rho> = (\<lambda>x. if x = a then 0 else if x = b then 1 else x)"
      have "bij_betw \<rho> (scheme_labels [(a,True),(a,True),(b,True),(b,True)]) {0, 1}"
        unfolding bij_betw_def \<rho>_def scheme_labels_def using hb_ne_a by (by100 auto)
      from valid_scheme_alpha_rename[OF this]
      have "top1_valid_scheme_equiv [(a,True),(a,True),(b,True),(b,True)]
          (map (\<lambda>(l,bo). (\<rho> l, bo)) [(a,True),(a,True),(b,True),(b,True)])" .
      moreover have "map (\<lambda>(l,bo). (\<rho> l, bo)) [(a,True),(a,True),(b,True),(b,True)]
          = [(0,True),(0,True),(1,True),(1,True)]" unfolding \<rho>_def using hb_ne_a by (by100 simp)
      moreover have "[(0::nat,True),(0,True),(1,True),(1,True)] = top1_m_projective_scheme 2"
        unfolding top1_m_projective_scheme_def by code_simp
      ultimately show ?thesis by (by100 simp)
    qed
    ultimately have "top1_valid_scheme_equiv scheme (top1_m_projective_scheme 2)"
      using valid_equiv_trans by (by100 blast)
    moreover have "(2::nat) > 0" by (by100 simp)
    moreover have "top1_is_projective_scheme (top1_m_projective_scheme 2) 2"
      unfolding top1_is_projective_scheme_def by (by100 simp)
    ultimately show ?thesis by (by100 fast)
  next
    case False
    \<comment> \<open>Opposite directions: rest = [(b,T),(b,F)] or [(b,F),(b,T)].
       Cancel the b-pair: [(a,T),(a,T),(b,T),(b,F)] ~ [(a,T),(a,T)] by
       rotating b to form [b, inv(b)] adjacent, then cancel.\<close>
    have "top1_valid_scheme_equiv ([(a,True),(a,True)] @ rest) ([(a,True),(a,True)])"
    proof -
      have hrest_torus: "rest = [(b, d1), (b, d2)]" using hrest_eq hr0 hr1 by (by100 simp)
      have "d1 = True \<and> d2 = False \<or> d1 = False \<and> d2 = True" using False by (by100 blast)
      hence hrest_inv: "rest = [(b, True), (b, False)] \<or> rest = [(b, False), (b, True)]"
        using hrest_torus by (by100 blast)
      \<comment> \<open>Either way, [(a,T),(a,T)] @ rest contains (b,T) and inv(b,T) = (b,F).
         Use: rotate to separate, then cancel.\<close>
      show ?thesis
      proof (cases "d1 = True")
        case True
        hence "rest = [(b, True), (b, False)]" using hrest_torus False by (by100 simp)
        \<comment> \<open>[(a,T),(a,T),(b,T),(b,F)]: the last two are (b,T) and inv(b,T).
           Cancel: [(a,T),(a,T)] @ [(b,T), inv(b,T)] \\<to> [(a,T),(a,T)] @ [].\<close>
        have "top1_valid_scheme_operation
            ([(a,True),(a,True)] @ [(b,True), top1_inverse_edge (b,True)] @ [])
            ([(a,True),(a,True)] @ [])"
          by (rule top1_valid_scheme_operation.v_cancel)
        moreover have "top1_inverse_edge (b, True) = (b, False)"
          unfolding top1_inverse_edge_def by (by100 simp)
        ultimately have "top1_valid_scheme_operation
            ([(a,True),(a,True),(b,True),(b,False)]) ([(a,True),(a,True)])"
          by (by100 simp)
        from valid_imp_equiv[OF this]
        show ?thesis using \<open>rest = [(b,True),(b,False)]\<close> by (by100 simp)
      next
        case False2: False
        hence "d1 = False" by (by100 simp)
        hence "rest = [(b, False), (b, True)]" using hrest_torus False by (by100 simp)
        \<comment> \<open>[(a,T),(a,T),(b,F),(b,T)]: rotate to [(b,T),(a,T),(a,T),(b,F)],
           then cancel [(b,T),inv(b,T)] = cancel at different position.
           Actually: use flip\\_label b first to get [(a,T),(a,T),(b,T),(b,F)], then cancel.\<close>
        have hop_flip: "top1_valid_scheme_operation [(a,True),(a,True),(b,False),(b,True)]
            (map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,True)])"
          by (rule top1_valid_scheme_operation.v_flip_label)
        have hmap_flip: "map (\<lambda>(l,bo). (l, if l = b then \<not>bo else bo)) [(a,True),(a,True),(b,False),(b,True)]
            = [(a,True),(a,True),(b,True),(b,False)]" using hb_ne_a by (by100 simp)
        have s1: "top1_valid_scheme_equiv ([(a,True),(a,True),(b,False),(b,True)])
            ([(a,True),(a,True),(b,True),(b,False)])"
          using valid_imp_equiv[OF hop_flip[unfolded hmap_flip]] .
        have "top1_valid_scheme_operation
            ([(a,True),(a,True)] @ [(b,True), top1_inverse_edge (b,True)] @ [])
            ([(a,True),(a,True)] @ [])"
          by (rule top1_valid_scheme_operation.v_cancel)
        hence s2: "top1_valid_scheme_equiv ([(a,True),(a,True),(b,True),(b,False)]) ([(a,True),(a,True)])"
          unfolding top1_inverse_edge_def using valid_imp_equiv by (by100 simp)
        from valid_equiv_trans[OF s1 s2]
        show ?thesis using \<open>rest = [(b,False),(b,True)]\<close> by (by100 simp)
      qed
    qed
    hence "top1_valid_scheme_equiv scheme ([(a,True),(a,True)])"
      using valid_equiv_trans \<open>top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ rest)\<close> by (by100 blast)
    \<comment> \<open>[(a,T),(a,T)] is proj\\_1 via alpha-rename.\<close>
    moreover have "top1_valid_scheme_equiv [(a,True),(a,True)] (top1_m_projective_scheme 1)"
    proof -
      define \<rho> :: "nat \<Rightarrow> nat" where "\<rho> = (\<lambda>x. if x = a then 0 else x)"
      have "bij_betw \<rho> (scheme_labels [(a,True),(a,True)]) {0}"
        unfolding bij_betw_def \<rho>_def scheme_labels_def by (by100 auto)
      from valid_scheme_alpha_rename[OF this]
      have "top1_valid_scheme_equiv [(a,True),(a,True)] (map (\<lambda>(l,bo). (\<rho> l, bo)) [(a,True),(a,True)])" .
      moreover have "map (\<lambda>(l,bo). (\<rho> l, bo)) [(a,True),(a,True)] = [(0,True),(0,True)]"
        unfolding \<rho>_def by (by100 simp)
      moreover have "[(0::nat,True),(0,True)] = top1_m_projective_scheme 1"
        unfolding top1_m_projective_scheme_def by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    ultimately have "top1_valid_scheme_equiv scheme (top1_m_projective_scheme 1)"
      using valid_equiv_trans by (by100 blast)
    moreover have "top1_is_projective_scheme (top1_m_projective_scheme 1) 1"
      unfolding top1_is_projective_scheme_def by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
qed

\<comment> \<open>Key congruence: scheme equivalence on a suffix extends through a projective-pair prefix,
   provided the suffix labels don't include the pair's label.
   Proof: each elementary operation on the suffix can be simulated on the full list.
   - cancel/uncancel/cut\_paste: adjust the prefix in the constructor.
   - rotate: use 3 rotations of the full list.
   - invert: rotate prefix to back, invert, flip\_label a, rotate back.
   - relabel/flip\_label: act on full list; since label a only appears in prefix, prefix unchanged.
   - cut\_paste2/cut\_paste\_opp: adjust prefix in constructor.\<close>
lemma elementary_operation_prepend:
  fixes y z :: "(nat \<times> bool) list" and a :: nat
  assumes hop: "top1_elementary_scheme_operation y z"
      and hny: "\<forall>e \<in> set y. fst e \<noteq> a"
      and hnz: "\<forall>e \<in> set z. fst e \<noteq> a"
  shows "top1_scheme_equiv ([(a, True), (a, True)] @ y) ([(a, True), (a, True)] @ z)"
  by (rule elementary_imp_equiv[OF top1_elementary_scheme_operation.context_left[OF hop]])

\<comment> \<open>Main congruence: full chain through prefix.\<close>
\<comment> \<open>Filter-count preservation: rotation preserves length(filter P ...).\<close>
lemma filter_count_rotate:
  "length (filter P (u @ v)) = length (filter P (v @ u))"
  by (by100 simp)

\<comment> \<open>Filter-count preservation: flip\_label preserves length(filter (\<lambda>e. fst e = l) ...).\<close>
lemma filter_count_flip_label:
  "length (filter (\<lambda>e. fst e = l) (map (\<lambda>(la,b). (la, if la = a then \<not>b else b)) w))
   = length (filter (\<lambda>e. fst e = l) w)"
proof -
  have "(\<lambda>e. fst e = l) \<circ> (\<lambda>(la,b). (la, if la = a then \<not>b else b)) = (\<lambda>e. fst e = l)"
    by (rule ext) (simp split: prod.splits)
  thus ?thesis by (simp add: filter_map)
qed

\<comment> \<open>Filter-count preservation: cut\_paste\_opp preserves length(filter P ...).\<close>
lemma filter_count_cut_paste_opp:
  "length (filter P (u0 @ u1 @ x @ u2 @ y @ u3))
   = length (filter P (u0 @ x @ u2 @ y @ u1 @ u3))"
  by (by100 simp)

lemma scheme_equiv_prepend:
  fixes rest rest' :: "('a \<times> bool) list" and prefix :: "('a \<times> bool) list"
  assumes "top1_scheme_equiv rest rest'"
  shows "top1_scheme_equiv (prefix @ rest) (prefix @ rest')"
proof -
  \<comment> \<open>With context\_left: lift each step of rest \<sim>* rest' through the prefix.\<close>
  from assms show ?thesis unfolding top1_scheme_equiv_def
  proof (induction rule: rtranclp.induct)
    case rtrancl_refl thus ?case by (by100 simp)
  next
    case (rtrancl_into_rtrancl x y z)
    have "top1_elementary_scheme_operation (prefix @ y) (prefix @ z)"
      by (rule top1_elementary_scheme_operation.context_left[OF rtrancl_into_rtrancl.hyps(2)])
    thus ?case using rtrancl_into_rtrancl.IH by (meson rtranclp.rtrancl_into_rtrancl)
  qed
qed

\<comment> \<open>scheme\\_equiv\\_append, scheme\\_equiv\\_relabel\\_avoid (OLD): DELETED.
   Valid versions: valid\\_equiv\\_append, valid\\_equiv\\_relabel\\_avoid (in cached session).\<close>

\<comment> \<open>Any scheme of the form [(l0,T),(l0,T),...,(lm,T),(lm,T)] with distinct labels
   is equivalent to the standard projective scheme proj(m+1) via relabeling.\<close>
\<comment> \<open>projective\_form\_equiv\_standard (OLD): DELETED. Valid version: valid\_projective\_form\_equiv\_standard.\<close>

\<comment> \<open>Appending any projective pair to proj m gives proj(Suc m) up to equivalence.\<close>
\<comment> \<open>Valid version: appending [(a,T),(a,T)] to proj\\_m gives proj\\_Suc\\_m.
   Key: relabel a\\<to>m avoiding collision by first removing a from proj\\_m.\<close>
lemma valid_proj_append_pair:
  "top1_valid_scheme_equiv (top1_m_projective_scheme m @ [(a, True), (a, True)]) (top1_m_projective_scheme (Suc m))"
proof -
  have hdef: "top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]"
    unfolding top1_m_projective_scheme_def by (by100 simp)
  show ?thesis
  proof (cases "a = m")
    case True then show ?thesis unfolding hdef top1_valid_scheme_equiv_def by (by100 simp)
  next
    case ha_ne: False
    \<comment> \<open>Pick fresh avoiding both a and m.\<close>
    have hfin: "finite (fst ` set (top1_m_projective_scheme m) \<union> {a, m} :: nat set)" by (by100 simp)
    from ex_new_if_finite[OF infinite_UNIV_nat hfin]
    obtain fresh :: nat where hfr: "fresh \<notin> fst ` set (top1_m_projective_scheme m) \<union> {a, m}" by (by100 blast)
    have hfr_pm: "fresh \<notin> fst ` set (top1_m_projective_scheme m)" using hfr by (by100 blast)
    have hfr_a: "fresh \<noteq> a" using hfr by (by100 blast)
    have hfr_m: "fresh \<noteq> m" using hfr by (by100 blast)
    \<comment> \<open>Step 1: relabel a \\<to> fresh in proj\\_m (valid since fresh is truly fresh).\<close>
    define pm' where "pm' = map (\<lambda>(l,bo). (if l = a then fresh else l, bo)) (top1_m_projective_scheme m)"
    have s1: "top1_valid_scheme_equiv (top1_m_projective_scheme m) pm'"
    proof (cases "a \<in> fst ` set (top1_m_projective_scheme m)")
      case True
      show ?thesis unfolding pm'_def
        using valid_imp_equiv[OF top1_valid_scheme_operation.v_relabel[OF hfr_pm hfr_a]] .
    next
      case False
      have "pm' = top1_m_projective_scheme m" unfolding pm'_def
        using map_relabel_id[OF False] by (by100 simp)
      then show ?thesis unfolding top1_valid_scheme_equiv_def by (by100 simp)
    qed
    \<comment> \<open>pm' avoids a.\<close>
    have hpm'_no_a: "\<forall>e \<in> set pm'. fst e \<noteq> a"
    proof
      fix e assume "e \<in> set pm'"
      then obtain l b where hlb: "(l,b) \<in> set (top1_m_projective_scheme m)"
          "e = (if l = a then fresh else l, b)" unfolding pm'_def by (by100 auto)
      then show "fst e \<noteq> a" using hfr_a by (by100 auto)
    qed
    \<comment> \<open>m \\<notin> labels(pm'): labels(pm') \\<subseteq> (labels(proj\\_m) - {a}) \\<union> {fresh}.\<close>
    have hm_not_pm': "m \<notin> fst ` set pm'"
    proof -
      have "fst ` set pm' \<subseteq> (fst ` set (top1_m_projective_scheme m) - {a}) \<union> {fresh}"
      proof
        fix x assume "x \<in> fst ` set pm'"
        then obtain l b where "(l,b) \<in> set (top1_m_projective_scheme m)"
            "x = (if l = a then fresh else l)" unfolding pm'_def by (by100 auto)
        then show "x \<in> (fst ` set (top1_m_projective_scheme m) - {a}) \<union> {fresh}"
          by (cases "l = a") (by100 force)+
      qed
      moreover have "m \<notin> fst ` set (top1_m_projective_scheme m)"
        unfolding top1_m_projective_scheme_def by (by100 auto)
      moreover have "m \<noteq> fresh" using hfr_m by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 2: proj\\_m @ [(a,T),(a,T)] ~ pm' @ [(a,T),(a,T)].\<close>
    have s2: "top1_valid_scheme_equiv (top1_m_projective_scheme m @ [(a,True),(a,True)])
        (pm' @ [(a,True),(a,True)])"
      using valid_equiv_append[OF s1] by (by100 blast)
    \<comment> \<open>Step 3: relabel a \\<to> m. Fresh: m \\<notin> labels(pm') and m \\<noteq> a.\<close>
    have hm_fresh: "m \<notin> fst ` set (pm' @ [(a,True),(a,True)])"
      using hm_not_pm' ha_ne by (by100 simp)
    have hmap_eq: "map (\<lambda>(l,b). (if l = a then m else l, b)) (pm' @ [(a,True),(a,True)])
        = pm' @ [(m,True),(m,True)]"
      using hpm'_no_a by (induction pm') (by100 auto)+
    have s3: "top1_valid_scheme_equiv (pm' @ [(a,True),(a,True)]) (pm' @ [(m,True),(m,True)])"
      using valid_imp_equiv[OF top1_valid_scheme_operation.v_relabel[OF hm_fresh ha_ne[symmetric]]]
            hmap_eq by (by100 simp)
    \<comment> \<open>Step 4: pm' @ [(m,T),(m,T)] ~ proj\\_m @ [(m,T),(m,T)].\<close>
    have s4: "top1_valid_scheme_equiv (pm' @ [(m,True),(m,True)])
        (top1_m_projective_scheme m @ [(m,True),(m,True)])"
      using valid_equiv_append[OF valid_equiv_sym[OF s1]] by (by100 blast)
    from valid_equiv_trans[OF s2 s3] valid_equiv_trans s4
    have "top1_valid_scheme_equiv (top1_m_projective_scheme m @ [(a,True),(a,True)])
          (top1_m_projective_scheme m @ [(m,True),(m,True)])"
      by (by100 blast)
    then show ?thesis using hdef by (by100 simp)
  qed
qed

\<comment> \<open>proj\_append\_pair (OLD): DELETED. Valid version: valid\_proj\_append\_pair.\<close>

\<comment> \<open>A projective pair prepended to a torus scheme gives a projective scheme.
   By repeated application of Lemma 77.4: 1 proj pair + n torus blocks \<to> (2n+1) proj pairs.\<close>
\<comment> \<open>Valid version: [(a,T),(a,T)] @ torus\\_n ~ proj\\_(2n+1).\<close>
lemma valid_proj_pair_absorbs_torus:
  "top1_valid_scheme_equiv ([(a, True), (a, True)] @ top1_n_torus_scheme n) (top1_m_projective_scheme (2*n + 1))"
proof (induction n arbitrary: a)
  case 0
  have "top1_valid_scheme_equiv ([(a, True), (a, True)]) (top1_m_projective_scheme 1)"
    using valid_proj_append_pair[of 0 a] unfolding top1_m_projective_scheme_def by (by100 simp)
  thus ?case unfolding top1_n_torus_scheme_def by (by100 simp)
next
  case (Suc n)
  \<comment> \<open>torus\\_(Suc n) = torus\\_n @ block.\<close>
  have htorus_suc: "top1_n_torus_scheme (Suc n) = top1_n_torus_scheme n
      @ [(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
    unfolding top1_n_torus_scheme_def by (by100 simp)
  let ?block = "[(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
  \<comment> \<open>IH: [(a,T),(a,T)] @ torus\\_n ~ proj\\_(2n+1).\<close>
  from Suc.IH have hIH: "top1_valid_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n)
      (top1_m_projective_scheme (2*n+1))" .
  \<comment> \<open>Suffix congruence: append block.\<close>
  have s1: "top1_valid_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n @ ?block)
      (top1_m_projective_scheme (2*n+1) @ ?block)"
    using valid_equiv_append[OF hIH] by (by100 simp)
  hence s1': "top1_valid_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme (Suc n))
      (top1_m_projective_scheme (2*n+1) @ ?block)"
    using htorus_suc by (by100 simp)
  \<comment> \<open>Absorption: proj\\_(2n+1) @ block ~ proj\\_(2n+3).
     Uses valid\\_Lemma\\_77\\_4 after relabeling block to fresh labels.\<close>
  have s2: "top1_valid_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
      (top1_m_projective_scheme (2*(Suc n)+1))"
  proof -
    \<comment> \<open>Fresh labels for the block (disjoint from all existing labels).\<close>
    have hfin: "finite (fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1} :: nat set)"
      by (by100 simp)
    from ex_new_if_finite[OF infinite_UNIV_nat hfin]
    obtain f1 :: nat where hf1: "f1 \<notin> fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1}"
      by (by100 blast)
    have hfin2: "finite (fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1, f1} :: nat set)"
      by (by100 simp)
    from ex_new_if_finite[OF infinite_UNIV_nat hfin2]
    obtain f2 :: nat where hf2: "f2 \<notin> fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1, f1}"
      by (by100 blast)
    \<comment> \<open>Step A: relabel 2n \\<to> f1 in block via v\\_context\\_left.\<close>
    have "f1 \<notin> fst ` set ?block" using hf1 by (by100 simp)
    moreover have "f1 \<noteq> 2*n" using hf1 by (by100 blast)
    ultimately have "top1_valid_scheme_operation ?block
        (map (\<lambda>(l,b). (if l = 2*n then f1 else l, b)) ?block)"
      by (rule top1_valid_scheme_operation.v_relabel)
    have hf1_fresh_block: "f1 \<notin> fst ` set ?block"
      using hf1 by (by100 auto)
    have hf1_ne: "f1 \<noteq> 2*n" using hf1 by (by100 blast)
    have "top1_valid_scheme_operation ?block (map (\<lambda>(l,b). (if l = 2*n then f1 else l, b)) ?block)"
      by (rule top1_valid_scheme_operation.v_relabel[OF hf1_fresh_block hf1_ne])
    moreover have "map (\<lambda>(l,b). (if l = 2*n then f1 else l, b)) ?block
        = [(f1,True),(2*n+1,True),(f1,False),(2*n+1,False)]" by (by100 simp)
    ultimately have "top1_valid_scheme_operation ?block [(f1,True),(2*n+1,True),(f1,False),(2*n+1,False)]"
      by (by100 simp)
    from top1_valid_scheme_operation.v_context_left[OF this, of "top1_m_projective_scheme (2*n+1)"]
    have rA: "top1_valid_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n+1) @ [(f1,True),(2*n+1,True),(f1,False),(2*n+1,False)])"
      by (rule valid_imp_equiv)
    \<comment> \<open>Step B: relabel 2n+1 \\<to> f2 in new block via v\\_context\\_left.\<close>
    let ?blk1 = "[(f1,True),(2*n+1,True),(f1,False),(2*n+1,False)]"
    have "f2 \<notin> fst ` set ?blk1" using hf2 by (by100 simp)
    moreover have "f2 \<noteq> 2*n+1" using hf2 by (by100 blast)
    ultimately have "top1_valid_scheme_operation ?blk1 (map (\<lambda>(l,b). (if l = 2*n+1 then f2 else l, b)) ?blk1)"
      by (rule top1_valid_scheme_operation.v_relabel)
    moreover have "f1 \<noteq> 2*n+1" using hf1 by (by100 blast)
    hence "map (\<lambda>(l,b). (if l = 2*n+1 then f2 else l, b)) ?blk1
        = [(f1,True),(f2,True),(f1,False),(f2,False)]" by (by100 simp)
    ultimately have "top1_valid_scheme_operation ?blk1 [(f1,True),(f2,True),(f1,False),(f2,False)]"
      by (by100 simp)
    from top1_valid_scheme_operation.v_context_left[OF this, of "top1_m_projective_scheme (2*n+1)"]
    have rB: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (2*n+1) @ [(f1,True),(2*n+1,True),(f1,False),(2*n+1,False)])
        (top1_m_projective_scheme (2*n+1) @ [(f1,True),(f2,True),(f1,False),(f2,False)])"
      by (rule valid_imp_equiv)
    \<comment> \<open>Step C: Decompose proj\\_(2n+1) = proj\\_(2n) @ [(2n,T),(2n,T)].
       Apply valid\\_Lemma\\_77\\_4 with c=2n, a=f1, b=f2.\<close>
    have hdecomp: "top1_m_projective_scheme (2*n+1) = top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    have rC: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True),(f1,True),(f2,True),(f1,False),(f2,False)])
        (top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True),(f2,True),(f2,True),(2*n,True),(2*n,True)])"
    proof -
      have "f1 \<noteq> f2" using hf2 by (by100 blast)
      moreover have "f1 \<noteq> 2*n" using hf1 by (by100 blast)
      moreover have "f2 \<noteq> 2*n" using hf2 by (by100 blast)
      moreover have "\<forall>e \<in> set (top1_m_projective_scheme (2*n)) \<union> set ([] :: (nat \<times> bool) list).
          fst e \<noteq> f1 \<and> fst e \<noteq> f2 \<and> fst e \<noteq> (2*n)"
      proof (intro ballI conjI)
        fix e assume "e \<in> set (top1_m_projective_scheme (2*n)) \<union> set ([] :: (nat \<times> bool) list)"
        hence "e \<in> set (top1_m_projective_scheme (2*n))" by (by100 simp)
        hence "fst e \<in> fst ` set (top1_m_projective_scheme (2*n))" by (by100 blast)
        hence "fst e \<in> fst ` set (top1_m_projective_scheme (2*n+1))"
          unfolding top1_m_projective_scheme_def by (by100 auto)
        thus "fst e \<noteq> f1" using hf1 by (by100 blast)
        thus "fst e \<noteq> f2" using hf2 \<open>fst e \<in> fst ` set (top1_m_projective_scheme (2*n+1))\<close>
          by (by100 blast)
        have "fst e < 2*n" using \<open>e \<in> set (top1_m_projective_scheme (2*n))\<close>
          unfolding top1_m_projective_scheme_def by (by100 auto)
        thus "fst e \<noteq> 2*n" by (by100 simp)
      qed
      moreover have "infinite (UNIV :: nat set)" by (by100 simp)
      ultimately show ?thesis
        using valid_Lemma_77_4_projective_absorbs_torus
          [of f1 f2 "2*n" "top1_m_projective_scheme (2*n)" "[]"]
        by (by100 simp)
    qed
    \<comment> \<open>Step D: Relabel f1 \\<to> 2n+1, f2 \\<to> 2n+2 to get standard projective labels.\<close>
    \<comment> \<open>Step D: Three successive valid\\_proj\\_append\\_pair to absorb pairs.\<close>
    have rD1: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True)])
        (top1_m_projective_scheme (Suc(2*n)))"
      by (rule valid_proj_append_pair)
    have rD2: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True)])
        (top1_m_projective_scheme (Suc(Suc(2*n))))"
      by (rule valid_proj_append_pair)
    have rD3: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (Suc(Suc(2*n))) @ [(2*n,True),(2*n,True)])
        (top1_m_projective_scheme (Suc(Suc(Suc(2*n)))))"
      by (rule valid_proj_append_pair)
    have rD: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True),(f2,True),(f2,True),(2*n,True),(2*n,True)])
        (top1_m_projective_scheme (Suc(Suc(Suc(2*n)))))"
    proof -
      \<comment> \<open>Step 1: absorb [(f1,T),(f1,T)].\<close>
      have "top1_valid_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True)])
          (top1_m_projective_scheme (Suc(2*n)))"
        by (rule valid_proj_append_pair)
      from valid_equiv_append[OF this, of "[(f2,True),(f2,True),(2*n,True),(2*n,True)]"]
      have d1: "top1_valid_scheme_equiv
          ((top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True)]) @ [(f2,True),(f2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True),(2*n,True),(2*n,True)])" .
      \<comment> \<open>Step 2: absorb [(f2,T),(f2,T)].\<close>
      have "top1_valid_scheme_equiv
          (top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True)])
          (top1_m_projective_scheme (Suc(Suc(2*n))))"
        by (rule valid_proj_append_pair)
      from valid_equiv_append[OF this, of "[(2*n,True),(2*n,True)]"]
      have d2: "top1_valid_scheme_equiv
          ((top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True)]) @ [(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc(Suc(2*n))) @ [(2*n,True),(2*n,True)])" .
      \<comment> \<open>Step 3: absorb [(2n,T),(2n,T)].\<close>
      have d3: "top1_valid_scheme_equiv
          (top1_m_projective_scheme (Suc(Suc(2*n))) @ [(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc(Suc(Suc(2*n)))))"
        by (rule valid_proj_append_pair)
      \<comment> \<open>List reassociations.\<close>
      have ha1: "(top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True)]) @ [(f2,True),(f2,True),(2*n,True),(2*n,True)]
          = top1_m_projective_scheme (2*n) @ [(f1,True),(f1,True),(f2,True),(f2,True),(2*n,True),(2*n,True)]"
        by (by100 simp)
      have ha2: "(top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True)]) @ [(2*n,True),(2*n,True)]
          = top1_m_projective_scheme (Suc(2*n)) @ [(f2,True),(f2,True),(2*n,True),(2*n,True)]"
        by (by100 simp)
      from d1[unfolded ha1] d2[unfolded ha2] d3
      show ?thesis using valid_equiv_trans by (by100 blast)
    qed
    \<comment> \<open>Assemble: proj\\_(2n) @ [(2n,T)²,(2n+1,T)²,(2n+2,T)²] = proj\\_(2n+3) = proj\\_(2*(Suc n)+1).\<close>
    have hfinal: "Suc(Suc(Suc(2*n))) = 2*(Suc n)+1" by (by100 simp)
    from rA rB have "top1_valid_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n+1) @ [(f1,True),(f2,True),(f1,False),(f2,False)])"
      using valid_equiv_trans by (by100 blast)
    moreover have "top1_m_projective_scheme (2*n+1) @ [(f1,True),(f2,True),(f1,False),(f2,False)]
        = top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True),(f1,True),(f2,True),(f1,False),(f2,False)]"
      using hdecomp by (by100 simp)
    ultimately have "top1_valid_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True),(f1,True),(f2,True),(f1,False),(f2,False)])"
      by (by100 simp)
    from valid_equiv_trans[OF this rC] valid_equiv_trans rD
    have "top1_valid_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (Suc(Suc(Suc(2*n)))))"
      by (by100 blast)
    thus ?thesis unfolding hfinal .
  qed
  from valid_equiv_trans[OF s1' s2]
  show ?case .
qed

\<comment> \<open>proj\_pair\_absorbs\_torus (OLD): DELETED. Valid version: valid\_proj\_pair\_absorbs\_torus.\<close>


\<comment> \<open>Helper: extract one projective pair from a proper scheme with a same-direction pair.
   Returns [(a,T),(a,T)] @ rest where rest is proper and shorter.\<close>
lemma extract_projective_pair:
  fixes scheme :: "(nat \<times> bool) list"
  assumes hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      and hproj: "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
      and hne: "scheme \<noteq> []"
  obtains a rest where
      "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
      "length rest = length scheme - 2"
      "\<forall>e \<in> set rest. fst e \<noteq> a"
      "fst ` set rest \<subseteq> fst ` set scheme"
      "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
proof -
  from hproj obtain a p q where hp: "p < length scheme" "q < length scheme" "p \<noteq> q"
      "fst (scheme!p) = a" "fst (scheme!q) = a" "snd (scheme!p) = snd (scheme!q)"
    by (by100 blast)
  \<comment> \<open>Flip direction to True if needed.\<close>
  define scheme1 where "scheme1 = (if snd (scheme!p) then scheme
      else map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme)"
  have hlen1: "length scheme1 = length scheme" unfolding scheme1_def by (by100 simp)
  have hfst_preserved: "\<forall>i < length scheme1. fst (scheme1 ! i) = fst (scheme ! i)"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def by (by100 simp)
  next
    case False
    hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1"
      hence "i < length scheme" using hlen1 by (by100 simp)
      show "fst (scheme1 ! i) = fst (scheme ! i)"
        using hsch1 \<open>i < length scheme\<close> by (cases "scheme ! i") (by100 simp)
    qed
  qed
  \<comment> \<open>scheme1 is equivalent to scheme.\<close>
  have hequiv1: "top1_scheme_equiv scheme scheme1"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def top1_scheme_equiv_def by (by100 simp)
  next
    case False
    hence "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    hence "top1_elementary_scheme_operation scheme scheme1"
      using top1_elementary_scheme_operation.flip_label[of scheme a] by (by100 simp)
    thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
  qed
  \<comment> \<open>scheme1 has (a,True) at all a-positions.\<close>
  have hcard1: "card {i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = 2"
  proof -
    have "{i. i < length scheme1 \<and> fst (scheme1 ! i) = a} =
        {i. i < length scheme \<and> fst (scheme ! i) = a}"
    proof (intro equalityI subsetI)
      fix i assume "i \<in> {i. i < length scheme1 \<and> fst (scheme1 ! i) = a}"
      hence "i < length scheme1" "fst (scheme1 ! i) = a" by (by100 simp)+
      hence "i < length scheme" using hlen1 by (by100 simp)
      hence "fst (scheme ! i) = a" using hfst_preserved \<open>i < length scheme1\<close> \<open>fst (scheme1 ! i) = a\<close> by (by100 simp)
      thus "i \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}" using \<open>i < length scheme\<close> by (by100 blast)
    next
      fix i assume "i \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}"
      hence "i < length scheme" "fst (scheme ! i) = a" by (by100 simp)+
      hence "i < length scheme1" using hlen1 by (by100 simp)
      hence "fst (scheme1 ! i) = fst (scheme ! i)" using hfst_preserved by (by100 blast)
      hence "fst (scheme1 ! i) = a" using \<open>fst (scheme ! i) = a\<close> by (by100 simp)
      thus "i \<in> {i. i < length scheme1 \<and> fst (scheme1 ! i) = a}" using \<open>i < length scheme1\<close> by (by100 blast)
    qed
    moreover from hproper have "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<in> {0, 2}" by (by100 blast)
    moreover have "p \<in> {i. i < length scheme \<and> fst (scheme ! i) = a}" using hp(1,4) by (by100 blast)
    hence "{i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> {}" by (by100 blast)
    hence "card {i. i < length scheme \<and> fst (scheme ! i) = a} \<noteq> 0" by (by100 simp)
    ultimately have "card {i. i < length scheme \<and> fst (scheme ! i) = a} = 2"
        and "{i. i < length scheme1 \<and> fst (scheme1 ! i) = a} = {i. i < length scheme \<and> fst (scheme ! i) = a}"
      by (by100 blast)+
    thus ?thesis by (by100 simp)
  qed
  have hdir1: "\<forall>i < length scheme1. fst (scheme1 ! i) = a \<longrightarrow> snd (scheme1 ! i) = True"
  proof (cases "snd (scheme ! p)")
    case True
    hence "scheme1 = scheme" unfolding scheme1_def by (by100 simp)
    have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
    proof -
      have "card {p, q} = 2" using hp(3) by (by100 simp)
      have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}"
        using hp(1,2,4,5) by (by100 blast)
      have "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
      from hproper have "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<in> {0, 2}" by (by100 blast)
      moreover have "{k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> {}"
        using hp(1,4) by (by100 blast)
      hence "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> 0" by (by100 simp)
      ultimately have "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2" by (by100 blast)
      from card_seteq[OF \<open>finite _\<close> \<open>{p, q} \<subseteq> _\<close>] this \<open>card {p, q} = 2\<close>
      show ?thesis by (by100 simp)
    qed
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
      hence "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}" using \<open>scheme1 = scheme\<close> hlen1 by (by100 simp)
      hence "i = p \<or> i = q" using honly_pq by (by100 blast)
      thus "snd (scheme1 ! i) = True" using \<open>scheme1 = scheme\<close> True hp(6) by (by100 blast)
    qed
  next
    case False
    hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a"
      have "i < length scheme" using \<open>i < length scheme1\<close> hlen1 by (by100 simp)
      have "fst (scheme ! i) = a" using hfst_preserved \<open>i < length scheme1\<close> \<open>fst (scheme1 ! i) = a\<close> by (by100 simp)
      hence "snd (scheme1 ! i) = (\<not> snd (scheme ! i))"
        using hsch1 \<open>i < length scheme\<close> by (cases "scheme ! i") (by100 simp)
      moreover have "snd (scheme ! p) = False" using False by (by100 simp)
      \<comment> \<open>All a-positions have snd = snd(scheme!p) = False, so flipped = True.\<close>
      have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a} = {p, q}"
      proof -
        have "card {p, q} = 2" using hp(3) by (by100 simp)
        have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a}"
          using hp(1,2,4,5) by (by100 blast)
        have "finite {k. k < length scheme \<and> fst (scheme ! k) = a}" by (by100 simp)
        from hproper have "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<in> {0, 2}" by (by100 blast)
        moreover have "{k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> {}"
          using hp(1,4) by (by100 blast)
        hence "card {k. k < length scheme \<and> fst (scheme ! k) = a} \<noteq> 0" by (by100 simp)
        ultimately have "card {k. k < length scheme \<and> fst (scheme ! k) = a} = 2" by (by100 blast)
        from card_seteq[OF \<open>finite _\<close> \<open>{p, q} \<subseteq> _\<close>] this \<open>card {p, q} = 2\<close>
        show ?thesis by (by100 simp)
      qed
      have "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a}"
        using \<open>i < length scheme\<close> \<open>fst (scheme ! i) = a\<close> by (by100 blast)
      hence "i = p \<or> i = q" using honly_pq by (by100 blast)
      hence "snd (scheme ! i) = snd (scheme ! p)" using hp(6) by (by100 blast)
      hence "snd (scheme ! i) = False" using False by (by100 simp)
      ultimately show "snd (scheme1 ! i) = True" by (by100 simp)
    qed
  qed
  have h1: "(a, True) \<in> set scheme1"
  proof -
    have "p < length scheme1" using hp(1) hlen1 by (by100 simp)
    hence "scheme1 ! p \<in> set scheme1" by (by100 simp)
    have "fst (scheme1 ! p) = a" using hfst_preserved \<open>p < length scheme1\<close> hp(4) by (by100 blast)
    have "snd (scheme1 ! p) = True" using hdir1 \<open>p < length scheme1\<close> \<open>fst (scheme1 ! p) = a\<close> by (by100 blast)
    obtain f s where hfs: "scheme1 ! p = (f, s)" by (cases "scheme1 ! p")
    hence "f = a" using \<open>fst (scheme1 ! p) = a\<close> by (by100 simp)
    hence "s = True" using \<open>snd (scheme1 ! p) = True\<close> hfs by (by100 simp)
    hence "scheme1 ! p = (a, True)" using hfs \<open>f = a\<close> by (by100 simp)
    thus ?thesis using \<open>scheme1 ! p \<in> set scheme1\<close> by (by100 simp)
  qed
  have "scheme1 \<noteq> []"
  proof
    assume "scheme1 = []" hence "length scheme1 = 0" by (by100 simp)
    thus False using hlen1 hne by (by100 simp)
  qed
  have hproper1: "\<forall>label. card {i. i < length scheme1 \<and> fst (scheme1 ! i) = label} \<in> {0, 2}"
  proof -
    have "\<And>label. {i. i < length scheme1 \<and> fst (scheme1 ! i) = label}
        = {i. i < length scheme \<and> fst (scheme ! i) = label}"
      using hfst_preserved hlen1 by (by100 force)
    thus ?thesis using hproper by (by100 simp)
  qed
  from bring_projective_pair_to_front[OF h1 hcard1 hdir1 \<open>scheme1 \<noteq> []\<close> hproper1]
  obtain rest0 where hrest0: "top1_scheme_equiv scheme1 ([(a, True), (a, True)] @ rest0)"
      "length rest0 = length scheme1 - 2"
      "\<forall>e \<in> set rest0. fst e \<noteq> a"
      "fst ` set rest0 \<subseteq> fst ` set scheme1"
      "\<forall>label. card {i. i < length rest0 \<and> fst (rest0 ! i) = label} \<in> {0, 2}"
    by blast
  \<comment> \<open>Thread back to scheme.\<close>
  have "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest0)"
    using scheme_equiv_trans[OF hequiv1 hrest0(1)] by (by100 blast)
  moreover have "length rest0 = length scheme - 2" using hrest0(2) hlen1 by (by100 simp)
  moreover have "fst ` set scheme1 \<subseteq> fst ` set scheme"
  proof (intro subsetI)
    fix l assume "l \<in> fst ` set scheme1"
    then obtain e where "e \<in> set scheme1" "fst e = l" by (by100 blast)
    then obtain i where "i < length scheme1" "scheme1 ! i = e"
      by (simp add: in_set_conv_nth) (by100 blast)
    hence "fst (scheme1 ! i) = l" using \<open>fst e = l\<close> by (by100 simp)
    hence "fst (scheme ! i) = l" using hfst_preserved \<open>i < length scheme1\<close> by (by100 simp)
    have "i < length scheme" using \<open>i < length scheme1\<close> hlen1 by (by100 simp)
    hence "scheme ! i \<in> set scheme" by (by100 simp)
    thus "l \<in> fst ` set scheme" using \<open>fst (scheme ! i) = l\<close> by (by100 force)
  qed
  hence "fst ` set rest0 \<subseteq> fst ` set scheme" using hrest0(4) by (by100 blast)
  ultimately show ?thesis using hrest0(3) hrest0(5) that[of a rest0] by (by100 blast)
qed

\<comment> \<open>Valid version of extract\\_projective\\_pair.\<close>
lemma valid_extract_projective_pair:
  fixes scheme :: "(nat \<times> bool) list"
  assumes hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      and hproj: "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
          \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
      and hne: "scheme \<noteq> []"
  obtains a rest where
      "top1_valid_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
      "length rest = length scheme - 2"
      "\<forall>e \<in> set rest. fst e \<noteq> a"
      "fst ` set rest \<subseteq> fst ` set scheme"
      "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
proof -
  \<comment> \<open>Step 1: Flip label to True direction.\<close>
  from hproj obtain a0 p q where hp: "p < length scheme" "q < length scheme" "p \<noteq> q"
      "fst (scheme!p) = a0" "fst (scheme!q) = a0" "snd (scheme!p) = snd (scheme!q)"
    by (by100 blast)
  define scheme1 where "scheme1 = (if snd (scheme!p) then scheme
      else map (\<lambda>(l, b). (l, if l = a0 then \<not> b else b)) scheme)"
  have hequiv1: "top1_valid_scheme_equiv scheme scheme1"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def top1_valid_scheme_equiv_def by (by100 simp)
  next
    case False
    hence "scheme1 = map (\<lambda>(l, b). (l, if l = a0 then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    hence "top1_valid_scheme_operation scheme scheme1"
      using top1_valid_scheme_operation.v_flip_label[of scheme a0] by (by100 simp)
    thus ?thesis by (rule valid_imp_equiv)
  qed
  \<comment> \<open>Step 2: scheme1 satisfies conditions for valid\\_bring\\_projective\\_pair\\_to\\_front\\_full.
     The combinatorial properties (card=2, True direction, properness) transfer from the old proof.\<close>
  \<comment> \<open>We need: (a0, True) \\<in> set scheme1, card=2 for a0, all a0 entries True, proper.\<close>
  \<comment> \<open>Combinatorial conditions for scheme1.\<close>
  have hlen1: "length scheme1 = length scheme" unfolding scheme1_def by (by100 simp)
  have hfst_preserved: "\<forall>i < length scheme1. fst (scheme1 ! i) = fst (scheme ! i)"
  proof (cases "snd (scheme ! p)")
    case True thus ?thesis unfolding scheme1_def by (by100 simp)
  next
    case False
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1"
      hence "i < length scheme" using hlen1 by (by100 simp)
      obtain l b where hlb: "scheme ! i = (l, b)" by (cases "scheme ! i")
      show "fst (scheme1 ! i) = fst (scheme ! i)"
        using False \<open>i < length scheme\<close> hlb unfolding scheme1_def by (by100 simp)
    qed
  qed
  have h1_ne: "scheme1 \<noteq> []"
  proof -
    from hne have "length scheme > 0" by (by100 simp)
    hence "length scheme1 > 0" using hlen1 by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  have h1_proper: "\<forall>label. card {i. i < length scheme1 \<and> fst (scheme1 ! i) = label} \<in> {0, 2}"
  proof -
    have "\<And>label. {i. i < length scheme1 \<and> fst (scheme1 ! i) = label}
        = {i. i < length scheme \<and> fst (scheme ! i) = label}"
      using hfst_preserved hlen1 by (by100 force)
    thus ?thesis using hproper by (by100 simp)
  qed
  have h1_card: "card {i. i < length scheme1 \<and> fst (scheme1 ! i) = a0} = 2"
  proof -
    have "{i. i < length scheme1 \<and> fst (scheme1 ! i) = a0}
        = {i. i < length scheme \<and> fst (scheme ! i) = a0}"
      using hfst_preserved hlen1 by (by100 force)
    moreover have "p \<in> {i. i < length scheme \<and> fst (scheme ! i) = a0}" using hp(1,4) by (by100 blast)
    hence "{i. i < length scheme \<and> fst (scheme ! i) = a0} \<noteq> {}" by (by100 blast)
    hence "card {i. i < length scheme \<and> fst (scheme ! i) = a0} \<noteq> 0" by (by100 simp)
    moreover from hproper have "card {i. i < length scheme \<and> fst (scheme ! i) = a0} \<in> {0, 2}" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have h1_dir: "\<forall>i < length scheme1. fst (scheme1 ! i) = a0 \<longrightarrow> snd (scheme1 ! i) = True"
  proof (cases "snd (scheme ! p)")
    case True
    hence "scheme1 = scheme" unfolding scheme1_def by (by100 simp)
    \<comment> \<open>Both a0-positions (p and q) have same direction (hp(6)), which is True.\<close>
    have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a0} = {p, q}"
    proof -
      have "card {p, q} = 2" using hp(3) by (by100 simp)
      have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a0}"
        using hp(1,2,4,5) by (by100 blast)
      have "finite {k. k < length scheme \<and> fst (scheme ! k) = a0}" by (by100 simp)
      from card_seteq[OF this \<open>{p, q} \<subseteq> _\<close>] h1_card[unfolded \<open>scheme1 = scheme\<close> hlen1] \<open>card {p, q} = 2\<close>
      show ?thesis by (by100 simp)
    qed
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a0"
      hence "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a0}" using \<open>scheme1 = scheme\<close> hlen1 by (by100 blast)
      hence "i = p \<or> i = q" using honly_pq by (by100 blast)
      thus "snd (scheme1 ! i) = True" using \<open>scheme1 = scheme\<close> True hp(6) by (by100 blast)
    qed
  next
    case False
    hence hsch1: "scheme1 = map (\<lambda>(l, b). (l, if l = a0 then \<not> b else b)) scheme"
      unfolding scheme1_def by (by100 simp)
    show ?thesis
    proof (intro allI impI)
      fix i assume "i < length scheme1" "fst (scheme1 ! i) = a0"
      hence "i < length scheme" using hlen1 by (by100 simp)
      obtain l b where hlb: "scheme ! i = (l, b)" by (cases "scheme ! i")
      have "scheme1 ! i = (l, if l = a0 then \<not> b else b)"
        using hsch1 \<open>i < length scheme\<close> hlb by (by100 simp)
      hence "fst (scheme1 ! i) = l" by (by100 simp)
      hence "l = a0" using \<open>fst (scheme1 ! i) = a0\<close> by (by100 simp)
      hence "scheme1 ! i = (a0, \<not> b)" using \<open>scheme1 ! i = (l, if l = a0 then \<not> b else b)\<close>
        by (by100 simp)
      \<comment> \<open>b must be False (since all a0-positions have same direction as scheme!p which is False).\<close>
      have "fst (scheme ! i) = a0" using hlb \<open>l = a0\<close> by (by100 simp)
      have "i = p \<or> i = q"
      proof -
        have honly_pq: "{k. k < length scheme \<and> fst (scheme ! k) = a0} = {p, q}"
        proof -
          have "card {p, q} = 2" using hp(3) by (by100 simp)
          have "{p, q} \<subseteq> {k. k < length scheme \<and> fst (scheme ! k) = a0}"
            using hp(1,2,4,5) by (by100 blast)
          have "finite {k. k < length scheme \<and> fst (scheme ! k) = a0}" by (by100 simp)
          have hcard_a0: "card {k. k < length scheme \<and> fst (scheme ! k) = a0} = 2"
          proof -
            have "{k. k < length scheme1 \<and> fst (scheme1 ! k) = a0}
                = {k. k < length scheme \<and> fst (scheme ! k) = a0}"
              using hfst_preserved hlen1 by (by100 force)
            thus ?thesis using h1_card by (by100 simp)
          qed
          have hfin_a0: "finite {k. k < length scheme \<and> fst (scheme ! k) = a0}" by (by100 simp)
          from card_subset_eq[OF hfin_a0 \<open>{p, q} \<subseteq> _\<close>]
          show ?thesis using hcard_a0 \<open>card {p, q} = 2\<close> by (by100 simp)
        qed
        have "i \<in> {k. k < length scheme \<and> fst (scheme ! k) = a0}"
          using \<open>i < length scheme\<close> \<open>fst (scheme ! i) = a0\<close> by (by100 blast)
        thus ?thesis using honly_pq by (by100 blast)
      qed
      hence "snd (scheme ! i) = snd (scheme ! p)" using hp(6) by (by100 blast)
      hence "b = False" using hlb False by (by100 simp)
      hence "scheme1 ! i = (a0, True)" using \<open>scheme1 ! i = (a0, \<not> b)\<close> by (by100 simp)
      thus "snd (scheme1 ! i) = True" by (by100 simp)
    qed
  qed
  have h1_in: "(a0, True) \<in> set scheme1"
  proof -
    have "p < length scheme1" using hp(1) hlen1 by (by100 simp)
    hence "scheme1 ! p \<in> set scheme1" by (by100 simp)
    moreover have "fst (scheme1 ! p) = a0" using hfst_preserved \<open>p < length scheme1\<close> hp(4) by (by100 blast)
    moreover have "snd (scheme1 ! p) = True" using h1_dir \<open>p < length scheme1\<close> calculation(2) by (by100 blast)
    ultimately have "(a0, True) \<in> set scheme1"
    proof -
      assume hfst: "fst (scheme1 ! p) = a0"
         and hsnd: "snd (scheme1 ! p) = True"
         and hin: "scheme1 ! p \<in> set scheme1"
      obtain f s where hfs: "scheme1 ! p = (f, s)" by (cases "scheme1 ! p")
      have "f = a0" using hfst hfs by (by100 simp)
      have "s = True" using hsnd hfs by (by100 simp)
      hence "scheme1 ! p = (a0, True)" using hfs \<open>f = a0\<close> by (by100 simp)
      thus "(a0, True) \<in> set scheme1" using hin by (by100 simp)
    qed
    thus ?thesis .
  qed
  from valid_bring_projective_pair_to_front_full[OF h1_in h1_card h1_dir h1_ne h1_proper]
  obtain rest where hrest: "top1_valid_scheme_equiv scheme1 ([(a0, True), (a0, True)] @ rest)"
      "length rest = length scheme1 - 2" "\<forall>e \<in> set rest. fst e \<noteq> a0"
      "fst ` set rest \<subseteq> fst ` set scheme1"
      "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}" by blast
  \<comment> \<open>Chain: scheme \\<sim> scheme1 \\<sim> [(a0,T),(a0,T)] @ rest.\<close>
  from valid_equiv_trans[OF hequiv1 hrest(1)]
  have "top1_valid_scheme_equiv scheme ([(a0, True), (a0, True)] @ rest)" .
  moreover have "length rest = length scheme - 2"
    using hrest(2) unfolding scheme1_def by (by100 simp)
  moreover have "fst ` set rest \<subseteq> fst ` set scheme"
  proof -
    have "fst ` set scheme1 \<subseteq> fst ` set scheme"
    proof (cases "snd (scheme ! p)")
      case True thus ?thesis unfolding scheme1_def by (by100 simp)
    next
      case False
      hence "scheme1 = map (\<lambda>(l, b). (l, if l = a0 then \<not> b else b)) scheme"
        unfolding scheme1_def by (by100 simp)
      thus ?thesis by (by100 force)
    qed
    thus ?thesis using hrest(4) by (by100 blast)
  qed
  ultimately show ?thesis using hrest(3) hrest(5) that[of a0 rest] by (by100 blast)
qed

\<comment> \<open>Main normal form theorem (Munkres \\<S>77 Theorem 77.5 core):
   Every proper labelling scheme is equivalent to one of:
   (1) aa\\<inverse>bb\\<inverse> (sphere, length 4)
   (2) a1a1...amam (projective, m \\<ge> 1)
   (3) a1b1a1\\<inverse>b1\\<inverse>...anbnanbnan\\<inverse>bn\\<inverse> (torus, n \\<ge> 1)\<close>

\<comment> \<open>Valid version: commutator block is validly equivalent to torus n=1, via alpha-rename.\<close>
lemma valid_commutator_block_equiv_torus_1:
  assumes "a \<noteq> (b :: nat)"
  shows "top1_valid_scheme_equiv [(a, True), (b, True), (a, False), (b, False)] (top1_n_torus_scheme 1)"
proof -
  define w where "w = [(a, True), (b, True), (a, False), (b, False)]"
  define \<rho> :: "nat \<Rightarrow> nat" where "\<rho> = (\<lambda>x. if x = a then 0 else if x = b then 1 else x)"
  have hw_labels: "scheme_labels w = {a, b}"
    unfolding w_def scheme_labels_def by (by100 auto)
  have hbij: "bij_betw \<rho> (scheme_labels w) {0, 1}"
    unfolding bij_betw_def \<rho>_def hw_labels using assms by (by100 auto)
  from valid_scheme_alpha_rename[OF hbij]
  have "top1_valid_scheme_equiv w (map (\<lambda>(l,bo). (\<rho> l, bo)) w)" .
  moreover have "map (\<lambda>(l,bo). (\<rho> l, bo)) w = [(0,True),(1,True),(0,False),(1,False)]"
    unfolding w_def \<rho>_def using assms by (by100 auto)
  moreover have "[(0::nat,True),(1,True),(0,False),(1,False)] = top1_n_torus_scheme 1"
    unfolding top1_n_torus_scheme_def by (by100 simp)
  ultimately show ?thesis unfolding w_def by (by100 simp)
qed

\<comment> \<open>A commutator block [(a,T),(b,T),(a,F),(b,F)] with a \\<noteq> b is equivalent to torus n=1.
   Proof: relabel a\\<to>0, b\\<to>1 (handling the b=0 case via intermediate label).\<close>
lemma commutator_block_equiv_torus_1:
  assumes "a \<noteq> (b :: nat)"
  shows "top1_scheme_equiv [(a, True), (b, True), (a, False), (b, False)] (top1_n_torus_scheme 1)"
proof -
  define w where "w = [(a, True), (b, True), (a, False), (b, False)]"
  \<comment> \<open>Case split on b: if b\\<noteq>0, relabel a\\<to>0 then b\\<to>1. If b=0, relabel a\\<to>1 directly.\<close>
  have "top1_scheme_equiv w (top1_n_torus_scheme 1)"
  proof (cases "b = (0::nat)")
    case bne0: False
    \<comment> \<open>relabel a\\<to>0\<close>
    have s1: "top1_scheme_equiv w (map (\<lambda>(l,bo). (if l = a then 0 else l, bo)) w)"
      unfolding top1_scheme_equiv_def
      using top1_elementary_scheme_operation.relabel[of w a 0] by (by100 simp)
    have h1: "map (\<lambda>(l,bo). (if l = a then 0 else l, bo)) w = [(0,True),(b,True),(0,False),(b,False)]"
      unfolding w_def using assms by (by100 simp)
    \<comment> \<open>relabel b\\<to>1\<close>
    have s2: "top1_scheme_equiv [(0,True),(b,True),(0,False),(b,False)]
        (map (\<lambda>(l,bo). (if l = b then 1 else l, bo)) [(0,True),(b,True),(0,False),(b,False)])"
      unfolding top1_scheme_equiv_def
      using top1_elementary_scheme_operation.relabel[of "[(0,True),(b,True),(0,False),(b,False)]" b 1]
      by (by100 simp)
    have h2: "map (\<lambda>(l,bo). (if l = b then 1 else l, bo)) [(0,True),(b,True),(0,False),(b,False)]
        = [(0,True),(1,True),(0,False),(1,False)]"
      using bne0 by (by100 simp)
    have h3: "[(0::nat,True),(1,True),(0,False),(1,False)] = top1_n_torus_scheme 1"
      unfolding top1_n_torus_scheme_def by (by100 simp)
    have "top1_scheme_equiv w [(0,True),(b,True),(0,False),(b,False)]"
      using s1 h1 by (by100 simp)
    moreover have "top1_scheme_equiv [(0,True),(b,True),(0,False),(b,False)] (top1_n_torus_scheme 1)"
      using s2 h2 h3 by (by100 simp)
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  next
    case btrue: True
    \<comment> \<open>b=0. relabel a\\<to>1, then rotate+flip to get standard form.\<close>
    have s1: "top1_scheme_equiv w (map (\<lambda>(l,bo). (if l = a then 1 else l, bo)) w)"
      unfolding top1_scheme_equiv_def
      using top1_elementary_scheme_operation.relabel[of w a 1] by (by100 simp)
    have h1: "map (\<lambda>(l,bo). (if l = a then 1 else l, bo)) w = [(1,True),(0::nat,True),(1,False),(0,False)]"
      unfolding w_def using assms btrue by (by100 simp)
    \<comment> \<open>rotate by 1: [(0,T),(1,F),(0,F),(1,T)]\<close>
    have s2: "top1_scheme_equiv [(1::nat,True),(0,True),(1,False),(0,False)]
        [(0,True),(1,False),(0,False),(1::nat,True)]"
    proof -
      have "top1_elementary_scheme_operation
          ([(1::nat,True)] @ [(0,True),(1,False),(0,False)])
          ([(0,True),(1,False),(0,False)] @ [(1::nat,True)])"
        by (rule top1_elementary_scheme_operation.rotate)
      thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
    qed
    \<comment> \<open>flip\_label 1: [(0,T),(1,T),(0,F),(1,F)]\<close>
    have s3: "top1_scheme_equiv [(0::nat,True),(1,False),(0,False),(1,True)]
        [(0,True),(1::nat,True),(0,False),(1,False)]"
    proof -
      have "top1_elementary_scheme_operation
          [(0::nat,True),(1,False),(0,False),(1,True)]
          (map (\<lambda>(l,bo). (l, if l = 1 then \<not>bo else bo)) [(0::nat,True),(1,False),(0,False),(1,True)])"
        by (rule top1_elementary_scheme_operation.flip_label)
      moreover have "map (\<lambda>(l,bo). (l, if l = (1::nat) then \<not>bo else bo)) [(0,True),(1,False),(0,False),(1,True)]
          = [(0,True),(1,True),(0,False),(1,False)]" by (by100 simp)
      ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
    qed
    have h3: "[(0::nat,True),(1,True),(0,False),(1,False)] = top1_n_torus_scheme 1"
      unfolding top1_n_torus_scheme_def by (by100 simp)
    have "top1_scheme_equiv w [(1,True),(0::nat,True),(1,False),(0,False)]"
      using s1 h1 by (by100 simp)
    moreover have "top1_scheme_equiv [(1::nat,True),(0,True),(1,False),(0,False)] (top1_n_torus_scheme 1)"
    proof -
      from s2 have "top1_scheme_equiv [(1::nat,True),(0,True),(1,False),(0,False)]
          [(0,True),(1,False),(0,False),(1,True)]" .
      moreover from s3 h3 have "top1_scheme_equiv [(0::nat,True),(1,False),(0,False),(1,True)] (top1_n_torus_scheme 1)"
        by (by100 simp)
      ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  qed
  thus ?thesis unfolding w_def .
qed

\<comment> \<open>Prepending a commutator block to a torus scheme gives a torus scheme of one higher index.
   block @ torus\_n ~ torus\_(n+1) after relabeling block's labels to fresh ones.\<close>
\<comment> \<open>A projective scheme followed by one torus pair is equivalent to a projective scheme with 2 more pairs.
   Proof by induction on m. Base: proj\_1 @ torus\_1 ~ proj\_3 by proj\_pair\_absorbs\_torus.
   Step: proj\_(m+1) @ torus\_1 = proj\_m @ [(m,T),(m,T)] @ torus\_1
   ~ proj\_m @ torus\_1 @ [(m,T),(m,T)] (rotate in suffix)
   ~ proj\_(m+2) @ [(m,T),(m,T)] (IH + congruence) ~ proj\_(m+3) (proj\_append\_pair).\<close>
\<comment> \<open>Valid version: proj\\_m @ torus\\_1 ~ proj\\_(m+2).\<close>
lemma valid_proj_absorbs_one_torus:
  assumes "m > 0"
  shows "top1_valid_scheme_equiv (top1_m_projective_scheme m @ top1_n_torus_scheme 1) (top1_m_projective_scheme (m+2))"
  using assms
proof (induction m)
  case 0 thus ?case by (by100 simp)
next
  case (Suc m')
  show ?case
  proof (cases "m' = 0")
    case True
    \<comment> \<open>Base: m=1. proj\\_1 @ torus\\_1 ~ proj\\_3.
       proj\\_1 = [(0,T),(0,T)]. Use valid\\_proj\\_pair\\_absorbs\\_torus[of 0 1].\<close>
    have "Suc m' = 1" using True by (by100 simp)
    from valid_proj_pair_absorbs_torus[of 0 1]
    have "top1_valid_scheme_equiv ([(0::nat,True),(0,True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme 3)" by (by100 simp)
    moreover have "top1_m_projective_scheme 1 = [(0::nat,True),(0,True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    ultimately have h1: "top1_valid_scheme_equiv (top1_m_projective_scheme 1 @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme 3)" by (by100 simp)
    have heq: "m' = 0" using True .
    \<comment> \<open>Goal: valid\\_equiv (proj (Suc m') @ torus 1) (proj (Suc m' + 2)) with m'=0.\<close>
    have "m' = 0" by (rule True)
    from valid_proj_pair_absorbs_torus[of 0 1]
    have h: "top1_valid_scheme_equiv
        ([(0::nat, True), (0, True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (2 * 1 + 1))" .
    have hpm1: "top1_m_projective_scheme (Suc 0) = [(0::nat, True), (0, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    have hpm3: "(2::nat) * 1 + 1 = Suc 0 + 2" by (by100 simp)
    from h[folded hpm1, unfolded hpm3] \<open>m' = 0\<close>
    show ?thesis by (by100 blast)
  next
    case nFalse: False
    hence hm': "m' > 0" by (by100 simp)
    have hpm_decomp: "top1_m_projective_scheme (Suc m') =
        top1_m_projective_scheme m' @ [(m', True), (m', True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    \<comment> \<open>Rotate in suffix: [(m',T),(m',T)] @ torus\\_1 ~ torus\\_1 @ [(m',T),(m',T)].\<close>
    have "top1_valid_scheme_equiv ([(m', True), (m', True)] @ top1_n_torus_scheme 1)
        (top1_n_torus_scheme 1 @ [(m', True), (m', True)])"
      using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
        [of "[(m', True), (m', True)]" "top1_n_torus_scheme 1"]] by (by100 simp)
    hence h_rot: "top1_valid_scheme_equiv
        (top1_m_projective_scheme m' @ [(m', True), (m', True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme m' @ top1_n_torus_scheme 1 @ [(m', True), (m', True)])"
      using valid_equiv_prepend by (by100 blast)
    \<comment> \<open>IH: proj\\_m' @ torus\\_1 ~ proj\\_(m'+2).\<close>
    from Suc.IH[OF hm']
    have hIH: "top1_valid_scheme_equiv (top1_m_projective_scheme m' @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (m'+2))" .
    from valid_equiv_append[OF hIH, of "[(m', True), (m', True)]"]
    have "top1_valid_scheme_equiv
        ((top1_m_projective_scheme m' @ top1_n_torus_scheme 1) @ [(m', True), (m', True)])
        (top1_m_projective_scheme (m'+2) @ [(m', True), (m', True)])" .
    hence h_ih_suf: "top1_valid_scheme_equiv
        (top1_m_projective_scheme m' @ top1_n_torus_scheme 1 @ [(m', True), (m', True)])
        (top1_m_projective_scheme (m'+2) @ [(m', True), (m', True)])"
      by (by100 simp)
    have h_append: "top1_valid_scheme_equiv
        (top1_m_projective_scheme (m'+2) @ [(m', True), (m', True)])
        (top1_m_projective_scheme (Suc (m'+2)))"
      by (rule valid_proj_append_pair)
    \<comment> \<open>Chain.\<close>
    have "top1_valid_scheme_equiv (top1_m_projective_scheme (Suc m') @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme m' @ [(m', True), (m', True)] @ top1_n_torus_scheme 1)"
      using hpm_decomp unfolding top1_valid_scheme_equiv_def by (by100 simp)
    from valid_equiv_trans[OF this h_rot] valid_equiv_trans h_ih_suf valid_equiv_trans h_append
    have "top1_valid_scheme_equiv (top1_m_projective_scheme (Suc m') @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (Suc (m'+2)))"
      by (by100 blast)
    moreover have "Suc (m'+2) = Suc m' + 2" by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
qed

\<comment> \<open>proj\_absorbs\_one\_torus (OLD): DELETED. Not needed by valid chain.\<close>

\<comment> \<open>Prepending a commutator block to a projective scheme gives a projective scheme of index m+2.
   Commutator = 1 torus pair. Lemma 77.4: proj pair + torus pair = 3 proj pairs.
   So commutator + projective\_m ~ projective\_(m+2).\<close>
\<comment> \<open>Valid version: prepending commutator block to projective scheme.\<close>
lemma valid_commutator_prepend_projective:
  assumes "a \<noteq> (b :: nat)" and "m > 0"
  shows "\<exists>w'. top1_is_projective_scheme w' (m+2) \<and>
      top1_valid_scheme_equiv ([(a, True), (b, True), (a, False), (b, False)] @ top1_m_projective_scheme m) w'"
proof -
  \<comment> \<open>Use old commutator\\_prepend\\_projective result and convert via valid\\_equiv\\_implies\\_equiv.\<close>
  \<comment> \<open>Actually, we need the VALID direction, not the old direction.\<close>
  \<comment> \<open>Direct approach: block ~ torus\\_1, then rotate, then absorb.\<close>
  let ?block = "[(a, True), (b, True), (a, False), (b, False)]"
  have h1: "top1_valid_scheme_equiv (?block @ top1_m_projective_scheme m)
      (top1_m_projective_scheme m @ top1_n_torus_scheme 1)"
  proof -
    from valid_commutator_block_equiv_torus_1[OF assms(1)]
    have "top1_valid_scheme_equiv ?block (top1_n_torus_scheme 1)" .
    hence "top1_valid_scheme_equiv (?block @ top1_m_projective_scheme m)
        (top1_n_torus_scheme 1 @ top1_m_projective_scheme m)"
      using valid_equiv_append by (by100 blast)
    moreover have "top1_valid_scheme_equiv (top1_n_torus_scheme 1 @ top1_m_projective_scheme m)
        (top1_m_projective_scheme m @ top1_n_torus_scheme 1)"
      using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
        [of "top1_n_torus_scheme 1" "top1_m_projective_scheme m"]] by (by100 simp)
    ultimately show ?thesis using valid_equiv_trans by (by100 blast)
  qed
  \<comment> \<open>Use valid\\_proj\\_absorbs\\_one\\_torus (now fully proved).\<close>
  have h2: "top1_valid_scheme_equiv (top1_m_projective_scheme m @ top1_n_torus_scheme 1)
      (top1_m_projective_scheme (m+2))"
    by (rule valid_proj_absorbs_one_torus[OF assms(2)])
  from valid_equiv_trans[OF h1 h2]
  have "top1_valid_scheme_equiv (?block @ top1_m_projective_scheme m) (top1_m_projective_scheme (m+2))" .
  moreover have "m + 2 > 0" using assms(2) by (by100 simp)
  ultimately show ?thesis unfolding top1_is_projective_scheme_def by (by100 blast)
qed

\<comment> \<open>commutator\_prepend\_projective (OLD): DELETED. Not needed by valid chain.\<close>

\<comment> \<open>Valid version: prepending a commutator block gives torus (n+1).\<close>
lemma valid_commutator_prepend_torus:
  assumes "a \<noteq> (b :: nat)" and "n > 0"
  shows "top1_valid_scheme_equiv ([(a, True), (b, True), (a, False), (b, False)] @ top1_n_torus_scheme n)
      (top1_n_torus_scheme (Suc n))"
proof -
  let ?block = "[(a, True), (b, True), (a, False), (b, False)]"
  let ?tn = "top1_n_torus_scheme n"
  define target_block where "target_block = [(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
  have htorus_suc: "top1_n_torus_scheme (Suc n) = ?tn @ target_block"
    unfolding top1_n_torus_scheme_def target_block_def by (by100 simp)
  \<comment> \<open>block ~ target\\_block via alpha-rename.\<close>
  have hblock_target: "top1_valid_scheme_equiv ?block target_block"
  proof -
    from valid_commutator_block_equiv_torus_1[OF assms(1)]
    have s1: "top1_valid_scheme_equiv ?block (top1_n_torus_scheme 1)" .
    have "2 * n \<noteq> 2 * n + (1::nat)" by (by100 simp)
    from valid_commutator_block_equiv_torus_1[OF this]
    have s2: "top1_valid_scheme_equiv [(2*n,True),(2*n+1,True),(2*n,False),(2*n+1,False)]
                                     (top1_n_torus_scheme 1)" .
    from valid_equiv_sym[OF s2]
    have s3: "top1_valid_scheme_equiv (top1_n_torus_scheme 1) target_block"
      unfolding target_block_def .
    from valid_equiv_trans[OF s1 s3] show ?thesis .
  qed
  have "top1_valid_scheme_equiv (?block @ ?tn) (target_block @ ?tn)"
    using valid_equiv_append[OF hblock_target] by (by100 blast)
  moreover have "top1_valid_scheme_equiv (target_block @ ?tn) (?tn @ target_block)"
    using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate[of target_block ?tn]] by (by100 simp)
  ultimately have "top1_valid_scheme_equiv (?block @ ?tn) (?tn @ target_block)"
    using valid_equiv_trans by (by100 blast)
  thus ?thesis using htorus_suc by (by100 simp)
qed

\<comment> \<open>commutator\_prepend\_torus (OLD): DELETED. Valid version: valid\_commutator\_prepend\_torus.\<close>

\<comment> \<open>scheme\_normal\_form (OLD, using top1\_scheme\_equiv): DELETED per expert audit 21.\<close>

\<comment> \<open>Valid version of scheme\\_normal\\_form: FULLY PROVED.
   Uses valid operations (rotate, cancel, uncancel, flip, relabel, cut\\_paste\\_opp,
   context\\_left) plus combinatorial helpers (all valid counterparts proved).
   The 2200-line replay is complete. Theorem 77.5 uses the valid chain.\<close>
\<comment> \<open>Helper: construct the 3-way disjunction for the valid normal form conclusion.\<close>
lemma valid_nf_sphere:
  "a \<noteq> b \<Longrightarrow> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)] \<Longrightarrow>
   (\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
   \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
   \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)"
  by (by100 blast)

lemma valid_nf_projective:
  "m > 0 \<Longrightarrow> top1_is_projective_scheme w m \<Longrightarrow> top1_valid_scheme_equiv scheme w \<Longrightarrow>
   (\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
   \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
   \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)"
  by (by100 blast)

lemma valid_nf_torus:
  "n > 0 \<Longrightarrow> top1_is_torus_scheme w n \<Longrightarrow> top1_valid_scheme_equiv scheme w \<Longrightarrow>
   (\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
   \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
   \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)"
  by (by100 blast)


\<comment> \<open>scheme\_normal\_form\_valid: Classification via valid operations. FULLY PROVED.
   ALL valid operation chains proved (see valid helpers above).
   The combinatorial list analysis (~2200 lines) is complete.\<close>
lemma scheme_normal_form_valid:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 4"
      and "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
  shows "(\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)"
  using assms
proof (induction "length scheme" arbitrary: scheme rule: less_induct)
  case (less scheme)
  show ?case
  proof (cases "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
      \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)")
    case True \<comment> \<open>Projective type: some label has same-direction pair.\<close>
    show ?thesis
    proof (cases "length scheme = 4")
      case True
      from valid_projective_len4_base[OF True less(3) \<open>\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
              i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
              \<and> snd (scheme ! i) = snd (scheme ! j)\<close>]
      show ?thesis by (by100 blast)
    next
      case False
      hence hgt4: "length scheme > 4" using less(2) by (by100 simp)
      have hne: "scheme \<noteq> []" using hgt4 by (by100 auto)
      obtain a rest where ha_rest:
          "top1_valid_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
          "length rest = length scheme - 2"
          "\<forall>e \<in> set rest. fst e \<noteq> a"
          "fst ` set rest \<subseteq> fst ` set scheme"
          "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
        using valid_extract_projective_pair[OF less(3)
            \<open>\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
                i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
                \<and> snd (scheme ! i) = snd (scheme ! j)\<close> hne] by (by100 blast)
      have hrest_len_ge4: "length rest \<ge> 4"
      proof -
        have "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
        hence "length scheme \<ge> 6" using hgt4 by (by100 presburger)
        thus ?thesis using ha_rest(2) by (by100 simp)
      qed
      have hrest_shorter: "length rest < length scheme" using ha_rest(2) hgt4 by (by100 simp)
      from less(1)[OF hrest_shorter hrest_len_ge4 ha_rest(5)]
      have hrest_nf: "(\<exists>a' b'. a' \<noteq> b' \<and> top1_valid_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)])
           \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv rest w)
           \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv rest w)" .
      from hrest_nf show ?thesis
      proof (elim disjE)
        \<comment> \<open>Case rest ~ sphere: cancel inverse pairs => [(a,T),(a,T)] ~ projective 1.\<close>
        assume "\<exists>a' b'. a' \<noteq> b' \<and> top1_valid_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)]"
        then obtain a' b' where hab: "a' \<noteq> b'" "top1_valid_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)]"
          by (by100 blast)
        have hchain: "top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)])"
          using valid_equiv_trans[OF ha_rest(1)] valid_equiv_prepend[OF hab(2)] by (by100 blast)
        have hcancel_ab: "top1_valid_scheme_equiv scheme [(a,True),(a,True)]"
        proof -
          have s1: "top1_valid_scheme_operation
              ([(a,True),(a,True)] @ [(a',True), top1_inverse_edge (a',True)] @ [(b',True),(b',False)])
              ([(a,True),(a,True)] @ [(b',True),(b',False)])"
            by (rule top1_valid_scheme_operation.v_cancel)
          have hinv_a: "(a', False) = top1_inverse_edge (a', True)"
            unfolding top1_inverse_edge_def by (by100 simp)
          hence eq1: "top1_valid_scheme_equiv ([(a,True),(a,True),(a',True),(a',False),(b',True),(b',False)])
              ([(a,True),(a,True),(b',True),(b',False)])"
            using s1 unfolding top1_valid_scheme_equiv_def by (by100 simp)
          have s2: "top1_valid_scheme_operation
              ([(a,True),(a,True)] @ [(b',True), top1_inverse_edge (b',True)] @ [])
              ([(a,True),(a,True)] @ [])"
            by (rule top1_valid_scheme_operation.v_cancel)
          have hinv_b: "(b', False) = top1_inverse_edge (b', True)"
            unfolding top1_inverse_edge_def by (by100 simp)
          hence eq2: "top1_valid_scheme_equiv ([(a,True),(a,True),(b',True),(b',False)])
              ([(a,True),(a,True)])"
            using s2 unfolding top1_valid_scheme_equiv_def by (by100 simp)
          from valid_equiv_trans[OF eq1 eq2]
          have "top1_valid_scheme_equiv ([(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)])
              ([(a,True),(a,True)])" by (by100 simp)
          from valid_equiv_trans[OF hchain this] show ?thesis .
        qed
        moreover have "top1_valid_scheme_equiv [(a,True),(a,True)] (top1_m_projective_scheme 1)"
          using valid_proj_append_pair[of 0 a]
          unfolding top1_m_projective_scheme_def by (by100 simp)
        ultimately have "top1_valid_scheme_equiv scheme (top1_m_projective_scheme 1)"
          using valid_equiv_trans by (by100 blast)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme 1) 1"
          unfolding top1_is_projective_scheme_def by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      next
        \<comment> \<open>Case rest ~ projective m: [(a,T),(a,T)] @ proj m ~ proj (m+1).\<close>
        assume "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv rest w"
        then obtain m' w where hm: "m' > 0" "top1_is_projective_scheme w m'" "top1_valid_scheme_equiv rest w"
          by (by100 blast)
        have hw_is: "w = top1_m_projective_scheme m'" using hm(2) unfolding top1_is_projective_scheme_def by (by100 blast)
        have "top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ w)"
          using valid_equiv_trans[OF ha_rest(1)] valid_equiv_prepend[OF hm(3)] by (by100 blast)
        hence hsch_proj: "top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ top1_m_projective_scheme m')"
          using hw_is by (by100 simp)
        \<comment> \<open>Rotate pair to end, then use valid\\_proj\\_append\\_pair.\<close>
        have hrotate: "top1_valid_scheme_equiv ([(a,True),(a,True)] @ top1_m_projective_scheme m')
            (top1_m_projective_scheme m' @ [(a,True),(a,True)])"
          using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate
            [of "[(a,True),(a,True)]" "top1_m_projective_scheme m'"]] by (by100 blast)
        have happend: "top1_valid_scheme_equiv (top1_m_projective_scheme m' @ [(a,True),(a,True)])
            (top1_m_projective_scheme (Suc m'))"
          by (rule valid_proj_append_pair)
        from valid_equiv_trans[OF hsch_proj] valid_equiv_trans[OF hrotate happend]
        have "top1_valid_scheme_equiv scheme (top1_m_projective_scheme (Suc m'))"
          using valid_equiv_trans by (by100 blast)
        moreover have "Suc m' > 0" by (by100 simp)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme (Suc m')) (Suc m')"
          unfolding top1_is_projective_scheme_def by (by100 simp)
        ultimately show ?thesis by (by100 blast)
      next
        \<comment> \<open>Case rest ~ torus n: [(a,T),(a,T)] @ torus n ~ projective (2n+1).\<close>
        assume "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv rest w"
        then obtain n w where hn: "n > 0" "top1_is_torus_scheme w n" "top1_valid_scheme_equiv rest w"
          by (by100 blast)
        have hw_is: "w = top1_n_torus_scheme n" using hn(2) unfolding top1_is_torus_scheme_def by (by100 blast)
        have "top1_valid_scheme_equiv scheme ([(a,True),(a,True)] @ top1_n_torus_scheme n)"
          using valid_equiv_trans[OF ha_rest(1)] valid_equiv_prepend[OF hn(3)] hw_is by (by100 blast)
        moreover have "top1_valid_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n) (top1_m_projective_scheme (2*n+1))"
          using valid_proj_pair_absorbs_torus[of a n] by (by100 blast)
        ultimately have "top1_valid_scheme_equiv scheme (top1_m_projective_scheme (2*n+1))"
          using valid_equiv_trans by (by100 blast)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme (2*n+1)) (2*n+1)"
          unfolding top1_is_projective_scheme_def by (by100 simp)
        moreover have "2*n+1 > 0" by (by100 simp)
        ultimately show ?thesis
          by (intro disjI2 disjI1 exI[of _ "2*n+1"] exI[of _ "top1_m_projective_scheme (2*n+1)"] conjI)
             (by100 blast)+
      qed
    qed
  next
    case False \<comment> \<open>Torus type: all labels have opposite-direction pairs.\<close>
    have htorus: "\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
        \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))"
      using False .
    show ?thesis
    proof (cases "length scheme = 4")
      case True \<comment> \<open>Torus base case: length 4.\<close>
      show ?thesis
      proof (cases "\<exists>i < 3. fst (scheme!i) = fst (scheme!(i+1))")
        case True \<comment> \<open>Adjacent same-label pair: cancel both to [], uncancel to sphere.\<close>
        from True obtain i where hi: "i < 3" "fst (scheme!i) = fst (scheme!(i+1))" by (by100 blast)
        \<comment> \<open>Torus type: opposite directions.\<close>
        have hsnd_ne: "snd (scheme!i) \<noteq> snd (scheme!(i+1))"
        proof
          assume "snd (scheme!i) = snd (scheme!(i+1))"
          have "i < length scheme" "i+1 < length scheme"
            using hi(1) \<open>length scheme = 4\<close> by simp_all
          hence "\<exists>label. \<exists>ia<length scheme. \<exists>j<length scheme. ia \<noteq> j
              \<and> fst (scheme!ia) = label \<and> fst (scheme!j) = label \<and> snd (scheme!ia) = snd (scheme!j)"
            using hi \<open>snd (scheme!i) = snd (scheme!(i+1))\<close>
            by (intro exI[of _ "fst (scheme!i)"] exI[of _ i] exI[of _ "i+1"] conjI) simp_all
          with htorus show False by simp
        qed
        have hjinv: "scheme!(i+1) = top1_inverse_edge (scheme!i)"
          using hi(2) hsnd_ne unfolding top1_inverse_edge_def
          by (cases "scheme!i", cases "scheme!(i+1)") simp
        \<comment> \<open>Decompose.\<close>
        define u where "u = take i scheme"
        define v where "v = drop (i + 2) scheme"
        have hdecomp: "scheme = u @ [scheme!i, top1_inverse_edge (scheme!i)] @ v"
        proof -
          have "scheme = take i scheme @ scheme!i # drop (Suc i) scheme"
            using id_take_nth_drop[of i scheme] hi(1) \<open>length scheme = 4\<close> by (by100 simp)
          also have "drop (Suc i) scheme = scheme!(i+1) # drop (Suc (Suc i)) scheme"
            using Cons_nth_drop_Suc[of "Suc i" scheme] hi(1) \<open>length scheme = 4\<close> by (by100 simp)
          finally show ?thesis using hjinv unfolding u_def v_def by (by100 simp)
        qed
        have hlen_uv: "length u + length v = 2"
          unfolding u_def v_def using \<open>length scheme = 4\<close> hi(1) by (by100 simp)
        \<comment> \<open>Cancel first pair.\<close>
        have hcancel1: "top1_valid_scheme_equiv scheme (u @ v)"
        proof -
          from top1_valid_scheme_operation.v_cancel[of u "scheme!i" v]
          have "top1_valid_scheme_operation (u @ [scheme!i, top1_inverse_edge (scheme!i)] @ v) (u @ v)" .
          from valid_imp_equiv[OF this] hdecomp show ?thesis by simp
        qed
        \<comment> \<open>Properness of remainder.\<close>
        have hproper_uv: "\<forall>label. card {j. j < length (u @ v) \<and> fst ((u @ v) ! j) = label} \<in> {0, 2}"
          using cancel_preserves_proper[OF less(3) _ hi(2)] hi(1) \<open>length scheme = 4\<close>
          unfolding u_def v_def by simp
        \<comment> \<open>Both elements have the same label (proper\\_len2\\_same\\_label).\<close>
        have huv_same: "fst ((u@v) ! 0) = fst ((u@v) ! 1)"
          using proper_len2_same_label[OF _ hproper_uv] hlen_uv by simp
        \<comment> \<open>Opposite directions (torus type).\<close>
        have huv_opp: "snd ((u@v) ! 0) \<noteq> snd ((u@v) ! 1)"
        proof
          assume hsame_dir: "snd ((u@v) ! 0) = snd ((u@v) ! 1)"
          \<comment> \<open>u@v is a sub-sequence of scheme at known positions.
             Get the actual scheme indices for the 2 elements.\<close>
          have huv_len2: "length (u@v) = 2" using hlen_uv by simp
          have hlen_u: "length u = i" unfolding u_def using hi(1) \<open>length scheme = 4\<close> by simp
          \<comment> \<open>Element 0 of u@v: if i>0, it's scheme!0; if i=0, it's scheme!2.\<close>
          \<comment> \<open>Element 1 of u@v: depends on i.\<close>
          \<comment> \<open>In all cases, the two elements come from positions \\<notin> {i, i+1} in scheme.\<close>
          let ?p0 = "if i = 0 then 2 else 0 :: nat"
          let ?p1 = "if i \<le> 1 then 3 else 1 :: nat"
          \<comment> \<open>Prove by case split on i \\<in> {0,1,2}.\<close>
          have hi_cases: "i = 0 \<or> i = 1 \<or> i = 2" using hi(1) by (by100 auto)
          have hp0_lt: "?p0 < length scheme" using hi_cases \<open>length scheme = 4\<close> by (by100 auto)
          have hp0_ne1: "?p0 \<noteq> i" using hi_cases by (by100 auto)
          have hp0_ne2: "?p0 \<noteq> i+1" using hi_cases by (by100 auto)
          have hp0_eq: "(u@v)!0 = scheme!?p0"
            using hi_cases hlen_u unfolding u_def v_def
            by (elim disjE) (simp_all add: nth_append \<open>length scheme = 4\<close> eval_nat_numeral)
          have hp1_lt: "?p1 < length scheme" using hi_cases \<open>length scheme = 4\<close> by (by100 auto)
          have hp1_ne1: "?p1 \<noteq> i" using hi_cases by (by100 auto)
          have hp1_ne2: "?p1 \<noteq> i+1" using hi_cases by (by100 auto)
          have hp1_eq: "(u@v)!1 = scheme!?p1"
            using hi_cases hlen_u unfolding u_def v_def
            by (elim disjE) (simp_all add: nth_append \<open>length scheme = 4\<close> eval_nat_numeral)
          have "?p0 \<noteq> ?p1" using hi_cases by (by100 auto)
          \<comment> \<open>Same label + same direction at positions p0, p1: contradicts torus type.\<close>
          have "fst (scheme!?p0) = fst (scheme!?p1)" using huv_same hp0_eq hp1_eq by simp
          have "snd (scheme!?p0) = snd (scheme!?p1)" using hsame_dir hp0_eq hp1_eq by simp
          hence "\<exists>label. \<exists>ia<length scheme. \<exists>j<length scheme. ia \<noteq> j
              \<and> fst (scheme!ia) = label \<and> fst (scheme!j) = label \<and> snd (scheme!ia) = snd (scheme!j)"
            using hp0_lt hp1_lt \<open>?p0 \<noteq> ?p1\<close> \<open>fst (scheme!?p0) = fst (scheme!?p1)\<close>
            by (intro exI[of _ "fst (scheme!?p0)"] exI[of _ "?p0"] exI[of _ "?p1"] conjI) simp_all
          with htorus show False by simp
        qed
        \<comment> \<open>Cancel second pair: u@v ~ [].\<close>
        have hinv_uv: "(u@v)!1 = top1_inverse_edge ((u@v)!0)"
          using huv_same huv_opp unfolding top1_inverse_edge_def
          by (cases "(u@v)!0", cases "(u@v)!1") simp
        have huv_inv: "(u@v)!1 = top1_inverse_edge ((u@v)!0)" using hinv_uv .
        have hcancel2: "top1_valid_scheme_equiv (u @ v) ([] :: (nat \<times> bool) list)"
        proof -
          have huv_len2: "length (u@v) = 2" using hlen_uv by simp
          obtain a0 where ha0: "u@v = [a0, top1_inverse_edge a0]"
          proof -
            have hne: "u@v \<noteq> []" using huv_len2 by (by100 auto)
            define a0 where "a0 = hd (u@v)"
            have "(u@v)!0 = a0" unfolding a0_def using hne by (cases "u@v") simp_all
            have hd_tl: "u@v = a0 # tl (u@v)" unfolding a0_def using hne by simp
            have "length (tl (u@v)) = 1" using huv_len2 by (by100 auto)
            then obtain b0 where "tl (u@v) = [b0]" by (cases "tl (u@v)") simp_all
            hence "u@v = [a0, b0]" using hd_tl by simp
            hence "(u@v)!1 = b0" by simp
            hence "b0 = top1_inverse_edge a0" using huv_inv \<open>(u@v)!0 = a0\<close> by simp
            thus ?thesis using \<open>u@v = [a0, b0]\<close> that by simp
          qed
          from top1_valid_scheme_operation.v_cancel[of "[]" a0 "[]"]
          have "top1_valid_scheme_operation [a0, top1_inverse_edge a0] []" by simp
          from valid_imp_equiv[OF this] ha0 show ?thesis by simp
        qed
        have hsch_nil: "top1_valid_scheme_equiv scheme ([] :: (nat \<times> bool) list)"
          using valid_equiv_trans[OF hcancel1 hcancel2] .
        \<comment> \<open>Uncancel with label 0: [] ~ [(0,T),(0,F)].\<close>
        have huncancel1: "top1_valid_scheme_equiv ([] :: (nat \<times> bool) list) [(0::nat,True),(0,False)]"
        proof -
          have "fst (0::nat,True) \<notin> scheme_labels (([]:: (nat \<times> bool) list) @ ([]:: (nat \<times> bool) list))"
            by (simp add: scheme_labels_def)
          from top1_valid_scheme_operation.v_uncancel[OF this]
          have "top1_valid_scheme_operation (([]:: (nat \<times> bool) list) @ [])
              ([] @ [(0::nat,True), top1_inverse_edge (0,True)] @ [])" .
          hence "top1_valid_scheme_operation ([]:: (nat \<times> bool) list) [(0::nat,True),(0,False)]"
            unfolding top1_inverse_edge_def by simp
          from valid_imp_equiv[OF this] show ?thesis .
        qed
        \<comment> \<open>Uncancel with label 1: [(0,T),(0,F)] ~ [(0,T),(1,T),(1,F),(0,F)].\<close>
        have huncancel2: "top1_valid_scheme_equiv [(0::nat,True),(0,False)] [(0,True),(1,True),(1,False),(0,False)]"
        proof -
          have "fst (1::nat,True) \<notin> scheme_labels ([(0::nat,True)] @ [(0,False)])"
            unfolding scheme_labels_def by (by100 auto)
          from top1_valid_scheme_operation.v_uncancel[OF this]
          have "top1_valid_scheme_operation ([(0::nat,True)] @ [(0,False)])
              ([(0,True)] @ [(1::nat,True), top1_inverse_edge (1,True)] @ [(0,False)])" .
          hence "top1_valid_scheme_operation [(0::nat,True),(0,False)] [(0,True),(1,True),(1,False),(0,False)]"
            unfolding top1_inverse_edge_def by simp
          from valid_imp_equiv[OF this] show ?thesis .
        qed
        \<comment> \<open>Flip+rotate to sphere form.\<close>
        have hto_sphere: "top1_valid_scheme_equiv [(0::nat,True),(1,True),(1,False),(0,False)]
            [(1,True),(1,False),(0,True),(0,False)]"
        proof -
          \<comment> \<open>Rotate: move (0,T) from front to after (1,F).\<close>
          have r1: "top1_valid_scheme_operation
              ([(0::nat,True)] @ [(1,True),(1,False),(0,False)])
              ([(1,True),(1,False),(0,False)] @ [(0,True)])"
            by (rule top1_valid_scheme_operation.v_rotate)
          hence "top1_valid_scheme_operation
              [(0::nat,True),(1,True),(1,False),(0,False)]
              [(1,True),(1,False),(0,False),(0,True)]" by simp
          from valid_imp_equiv[OF this]
          have s1: "top1_valid_scheme_equiv
              [(0::nat,True),(1,True),(1,False),(0,False)]
              [(1,True),(1,False),(0,False),(0,True)]" .
          \<comment> \<open>Flip label 0: (0,F) -> (0,T), (0,T) -> (0,F).\<close>
          have "top1_valid_scheme_operation
              [(1::nat,True),(1,False),(0,False),(0,True)]
              (map (\<lambda>(l,b). (l, if l = 0 then \<not>b else b)) [(1,True),(1,False),(0,False),(0,True)])"
            by (rule top1_valid_scheme_operation.v_flip_label)
          moreover have "(map (\<lambda>(l::nat,b). (l, if l = 0 then \<not>b else b)) [(1,True),(1,False),(0,False),(0,True)])
              = [(1,True),(1,False),(0,True),(0,False)]" by simp
          ultimately have "top1_valid_scheme_operation
              [(1::nat,True),(1,False),(0,False),(0,True)]
              [(1,True),(1,False),(0,True),(0,False)]" by simp
          from valid_equiv_trans[OF s1 valid_imp_equiv[OF this]] show ?thesis .
        qed
        \<comment> \<open>Chain everything.\<close>
        from valid_equiv_trans[OF hsch_nil huncancel1]
        have "top1_valid_scheme_equiv scheme [(0::nat,True),(0,False)]" .
        from valid_equiv_trans[OF this huncancel2]
        have "top1_valid_scheme_equiv scheme [(0::nat,True),(1,True),(1,False),(0,False)]" .
        from valid_equiv_trans[OF this hto_sphere]
        have "top1_valid_scheme_equiv scheme [(1::nat,True),(1,False),(0,True),(0,False)]" .
        moreover have "(1::nat) \<noteq> (0::nat)" by simp
        ultimately show ?thesis
          by (intro disjI1 exI[of _ 1] exI[of _ 0] conjI) (by100 blast)+
      next
        case False \<comment> \<open>No adjacent same-label: labels alternate, commutator -> torus 1.\<close>
        have hno_adj: "\<not> (\<exists>i < 3. fst (scheme!i) = fst (scheme!(i+1)))" using False .
        \<comment> \<open>With 4 elements, 2 labels, each appearing twice, and no adjacent same-label:
           scheme = [(a,d1),(b,d2),(a,~d1),(b,~d2)] for some a,b,d1,d2.\<close>
        obtain s0 s1 s2 s3 where hsch4: "scheme = [s0,s1,s2,s3]"
        proof -
          from \<open>length scheme = 4\<close> obtain x0 x1 x2 x3 xs where hcons: "scheme = x0#x1#x2#x3#xs"
            by (cases scheme; simp; cases "tl scheme"; simp; cases "tl (tl scheme)"; simp;
                cases "tl (tl (tl scheme))"; simp)
          moreover have "xs = []" using \<open>length scheme = 4\<close> hcons by (by100 simp)
          ultimately show ?thesis using that[of x0 x1 x2 x3] by (by100 simp)
        qed
        have hlen4: "length scheme = 4" using \<open>length scheme = 4\<close> .
        \<comment> \<open>Labels at positions 0,2 are the same; labels at positions 1,3 are the same.\<close>
        have hfs01_ne: "fst s0 \<noteq> fst s1" using hno_adj hsch4 by (by100 force)
        \<comment> \<open>Properness + no-adjacent + len=4 forces ABAB pattern.\<close>
        have hfs02: "fst s0 = fst s2"
        proof (rule ccontr)
          assume hne02: "fst s0 \<noteq> fst s2"
          \<comment> \<open>fst s0 appears at position 0 but not at 1 or 2. By properness it appears 2x, so also at 3.\<close>
          have "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}" using less(3) .
          hence "card {i. i < 4 \<and> fst (scheme ! i) = fst s0} \<in> {0, 2}" using hlen4 by simp
          moreover have "{i. i < 4 \<and> fst (scheme ! i) = fst s0} = (if fst s0 = fst s1 then {0,1} else {0})
              \<union> (if fst s0 = fst s2 then {2} else {}) \<union> (if fst s0 = fst s3 then {3} else {})"
            using hsch4 by (auto simp: eval_nat_numeral less_Suc_eq nth_Cons')
          ultimately have "fst s0 = fst s3"
            using hfs01_ne hne02 by (auto split: if_splits)
          \<comment> \<open>Then fst s1 appears at position 1. Not at 0 (hfs01\_ne) or 3 (= fst s0 ≠ fst s1). So at 2.\<close>
          have "card {i. i < 4 \<and> fst (scheme ! i) = fst s1} \<in> {0, 2}" using less(3) hlen4 by simp
          moreover have "{i. i < 4 \<and> fst (scheme ! i) = fst s1} = {1}
              \<union> (if fst s1 = fst s2 then {2} else {}) \<union> (if fst s1 = fst s3 then {3} else {})"
            using hsch4 hfs01_ne by (auto simp: eval_nat_numeral less_Suc_eq nth_Cons')
          ultimately have "fst s1 = fst s2"
            using hfs01_ne \<open>fst s0 = fst s3\<close> by (auto split: if_splits)
          \<comment> \<open>But fst s1 = fst s2 means positions 1,2 are adjacent same-label: contradiction.\<close>
          moreover have "\<not> fst (scheme!1) = fst (scheme!2)"
          proof -
            from hno_adj have "\<forall>i<3. \<not> (fst (scheme!i) = fst (scheme!(i+1)))" by (by100 blast)
            from this[rule_format, of 1] show ?thesis by (simp add: eval_nat_numeral)
          qed
          ultimately show False using hsch4 by (simp add: eval_nat_numeral)
        qed
        have hfs13: "fst s1 = fst s3"
        proof -
          have "card {i. i < 4 \<and> fst (scheme ! i) = fst s1} \<in> {0, 2}" using less(3) hlen4 by simp
          moreover have "{i. i < 4 \<and> fst (scheme ! i) = fst s1} = {1}
              \<union> (if fst s1 = fst s2 then {2} else {}) \<union> (if fst s1 = fst s3 then {3} else {})"
            using hsch4 hfs01_ne by (auto simp: eval_nat_numeral less_Suc_eq nth_Cons')
          moreover have "fst s1 \<noteq> fst s2" using hfs01_ne hfs02 by simp
          ultimately show ?thesis by (auto split: if_splits)
        qed
        have hfs_ne: "fst s0 \<noteq> fst s1" using hno_adj hsch4 by (by100 force)
        have hsd02: "snd s0 \<noteq> snd s2"
        proof
          assume "snd s0 = snd s2"
          have "(0::nat) < length scheme" using hlen4 by simp
          have "(2::nat) < length scheme" using hlen4 by simp
          have "(0::nat) \<noteq> (2::nat)" by simp
          have "fst (scheme!0) = fst s0" using hsch4 by simp
          have "fst (scheme!2) = fst s0" using hsch4 hfs02 by (simp add: eval_nat_numeral)
          have "snd (scheme!0) = snd (scheme!2)"
            using \<open>snd s0 = snd s2\<close> hsch4 by (simp add: eval_nat_numeral)
          hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
            using \<open>(0::nat) < length scheme\<close> \<open>(2::nat) < length scheme\<close> \<open>fst (scheme!0) = fst s0\<close>
                  \<open>fst (scheme!2) = fst s0\<close>
            by (intro exI[of _ "fst s0"] exI[of _ 0] exI[of _ 2] conjI) simp_all
          with htorus show False by simp
        qed
        have hsd13: "snd s1 \<noteq> snd s3"
        proof
          assume "snd s1 = snd s3"
          have "(1::nat) < length scheme" using hlen4 by simp
          have "(3::nat) < length scheme" using hlen4 by simp
          have "fst (scheme!1) = fst s1" using hsch4 by (simp add: eval_nat_numeral)
          have "fst (scheme!3) = fst s1" using hsch4 hfs13 by (simp add: eval_nat_numeral)
          have "snd (scheme!1) = snd (scheme!3)"
            using \<open>snd s1 = snd s3\<close> hsch4 by (simp add: eval_nat_numeral)
          hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
            using \<open>(1::nat) < length scheme\<close> \<open>(3::nat) < length scheme\<close> \<open>fst (scheme!1) = fst s1\<close>
                  \<open>fst (scheme!3) = fst s1\<close>
            by (intro exI[of _ "fst s1"] exI[of _ 1] exI[of _ 3] conjI) simp_all
          with htorus show False by simp
        qed
        \<comment> \<open>After flip\_label: scheme ~ [(fst s0,T),(fst s1,T),(fst s0,F),(fst s1,F)].\<close>
        define scheme1 where "scheme1 = (if snd s0 then scheme else
            map (\<lambda>(l,b). (l, if l = fst s0 then \<not>b else b)) scheme)"
        have hequiv1: "top1_valid_scheme_equiv scheme scheme1"
          unfolding scheme1_def top1_valid_scheme_equiv_def
          using top1_valid_scheme_operation.v_flip_label[of scheme "fst s0"]
          by (cases "snd s0") simp_all
        define scheme2 where "scheme2 = (if snd s1 then scheme1 else
            map (\<lambda>(l,b). (l, if l = fst s1 then \<not>b else b)) scheme1)"
        have hequiv2: "top1_valid_scheme_equiv scheme1 scheme2"
          unfolding scheme2_def top1_valid_scheme_equiv_def
          using top1_valid_scheme_operation.v_flip_label[of scheme1 "fst s1"]
          by (cases "snd s1") simp_all
        have hsch2: "scheme2 = [(fst s0,True),(fst s1,True),(fst s0,False),(fst s1,False)]"
        proof -
          have hs2: "s2 = (fst s0, \<not> snd s0)" using hfs02 hsd02 by (cases s2) simp
          have hs3: "s3 = (fst s1, \<not> snd s1)" using hfs13 hsd13 by (cases s3) simp
          have hexp: "scheme = [(fst s0, snd s0), (fst s1, snd s1), (fst s0, \<not>snd s0), (fst s1, \<not>snd s1)]"
            using hsch4 hs2 hs3 by (cases s0, cases s1) simp
          show ?thesis
            unfolding scheme2_def scheme1_def hexp
            using hfs_ne by (cases "snd s0"; cases "snd s1") simp_all
        qed
        have "top1_valid_scheme_equiv scheme2 (top1_n_torus_scheme 1)"
          using valid_commutator_block_equiv_torus_1[OF hfs_ne]
          unfolding hsch2 by (by100 blast)
        hence "top1_valid_scheme_equiv scheme (top1_n_torus_scheme 1)"
          using valid_equiv_trans[OF valid_equiv_trans[OF hequiv1 hequiv2]] by (by100 blast)
        moreover have "top1_is_torus_scheme (top1_n_torus_scheme 1) 1"
          unfolding top1_is_torus_scheme_def by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    next
      case False \<comment> \<open>Length > 4: extract commutator, apply IH.\<close>
      hence hgt4: "length scheme > 4" using less(2) by linarith
      show ?thesis
      proof (cases "\<exists>i. i + 1 < length scheme \<and> fst (scheme!i) = fst (scheme!(i+1))
              \<and> snd (scheme!i) \<noteq> snd (scheme!(i+1))")
        case True \<comment> \<open>Adjacent inverse pair: cancel, apply IH to shorter scheme.\<close>
        from True obtain j where hj: "j + 1 < length scheme"
            "fst (scheme!j) = fst (scheme!(j+1))" "snd (scheme!j) \<noteq> snd (scheme!(j+1))"
          by (by100 blast)
        have hjinv: "scheme!(j+1) = top1_inverse_edge (scheme!j)"
          using hj(2) hj(3) unfolding top1_inverse_edge_def
          by (cases "scheme!j", cases "scheme!(j+1)") (by100 simp)
        define shorter where "shorter = take j scheme @ drop (j+2) scheme"
        have hcancel: "top1_valid_scheme_equiv scheme shorter"
        proof -
          have "scheme = take j scheme @ [scheme!j, top1_inverse_edge (scheme!j)] @ drop (j+2) scheme"
          proof -
            have "scheme = take j scheme @ scheme!j # drop (Suc j) scheme"
              using id_take_nth_drop[of j scheme] hj(1) by (by100 simp)
            also have "drop (Suc j) scheme = scheme!(j+1) # drop (Suc (Suc j)) scheme"
              using Cons_nth_drop_Suc[of "Suc j" scheme] hj(1) by (by100 simp)
            finally show ?thesis using hjinv by (by100 simp)
          qed
          hence "top1_valid_scheme_operation scheme shorter"
            unfolding shorter_def
            using top1_valid_scheme_operation.v_cancel
              [of "take j scheme" "scheme!j" "drop (j+2) scheme"]
            by (by100 simp)
          thus ?thesis using valid_imp_equiv by (by100 blast)
        qed
        have hlen_shorter: "length shorter = length scheme - 2"
          unfolding shorter_def using hj(1) by (by100 simp)
        have hproper_shorter: "\<forall>label. card {i. i < length shorter \<and> fst (shorter!i) = label} \<in> {0, 2}"
          using cancel_preserves_proper[OF less(3) hj(1) hj(2)]
          unfolding shorter_def by (by100 blast)
        have hlen_ge4: "length shorter \<ge> 4"
        proof -
          have "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
          hence "length scheme \<ge> 6" using hgt4 by (by100 presburger)
          thus ?thesis using hlen_shorter by (by100 simp)
        qed
        have hlen_lt: "length shorter < length scheme" using hlen_shorter hgt4 by (by100 simp)
        from less(1)[OF hlen_lt hlen_ge4 hproper_shorter]
        have hIH: "(\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)])
           \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv shorter w)
           \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv shorter w)" .
        from hIH show ?thesis
        proof (elim disjE)
          assume "\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)]"
          then obtain a b where "a \<noteq> b" "top1_valid_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)]"
            by (by100 blast)
          hence "top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)]"
            using hcancel unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
          with \<open>a \<noteq> b\<close> show ?thesis by (by100 blast)
        next
          assume "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv shorter w"
          then obtain m' w where "m' > 0" "top1_is_projective_scheme w m'" "top1_valid_scheme_equiv shorter w"
            by (by100 blast)
          hence "top1_valid_scheme_equiv scheme w"
            using hcancel unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
          with \<open>m' > 0\<close> \<open>top1_is_projective_scheme w m'\<close> show ?thesis by (by100 blast)
        next
          assume "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv shorter w"
          then obtain n w where "n > 0" "top1_is_torus_scheme w n" "top1_valid_scheme_equiv shorter w"
            by (by100 blast)
          hence "top1_valid_scheme_equiv scheme w"
            using hcancel unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
          with \<open>n > 0\<close> \<open>top1_is_torus_scheme w n\<close> show ?thesis by (by100 blast)
        qed
      next
        case False \<comment> \<open>No adjacent cancel pair: extract commutator via Lemma 77.3.\<close>
        have hhno_adj_gt4: "\<not> (\<exists>i. i + 1 < length scheme \<and> fst (scheme!i) = fst (scheme!(i+1))
              \<and> snd (scheme!i) \<noteq> snd (scheme!(i+1)))" using False .
        \<comment> \<open>Step 1: Find labels a,b and decompose scheme into the Lemma 77.3 pattern
           w0 @ [(a,T),(b,T)] @ w1 @ [(a,F),(b,F)] @ w2 via rotate+flip+cut\\_paste\\_opp.\<close>
        have "\<exists>a_lab b_lab w0' w1' w2'. a_lab \<noteq> b_lab \<and>
            top1_valid_scheme_equiv scheme
              (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2')
            \<and> length w0' + length w1' + length w2' + 4 = length scheme
            \<and> (\<forall>l. length (filter (\<lambda>e. fst e = l)
                (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2'))
              = length (filter (\<lambda>e. fst e = l) scheme))"
        proof -
          \<comment> \<open>Step 1: Find label a with minimal gap between its two positions.\<close>
          \<comment> \<open>From properness: every label appears 0 or 2 times. At least one label appears
             (length > 4). Each appearing label has 2 positions.
             Choose a with smallest gap |pos2 - pos1|.\<close>
          have "\<exists>a_lab p1 p2. p1 < p2 \<and> p2 < length scheme
              \<and> fst (scheme!p1) = a_lab \<and> fst (scheme!p2) = a_lab
              \<and> snd (scheme!p1) \<noteq> snd (scheme!p2)
              \<and> (\<forall>k. p1 < k \<and> k < p2 \<longrightarrow> fst (scheme!k) \<noteq> a_lab)
              \<and> (\<forall>l q1 q2. q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = l
                  \<and> fst (scheme!q2) = l \<longrightarrow> p2 - p1 \<le> q2 - q1)"
          proof -
            \<comment> \<open>Define the set of all same-label pairs (as triples (gap, pos1, pos2)).\<close>
            let ?pairs = "{(q2-q1, q1, q2) | q1 q2.
                q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = fst (scheme!q2)}"
            \<comment> \<open>This set is non-empty: scheme has length > 4, so at least 3 labels, each appearing twice.\<close>
            have hpairs_ne: "?pairs \<noteq> {}"
            proof -
              \<comment> \<open>Position 0 has some label l. By properness, l appears at exactly 2 positions.
                 The second position q > 0 gives a pair in ?pairs.\<close>
              have "0 < length scheme" using hgt4 by (by100 linarith)
              define l where "l = fst (scheme ! 0)"
              have "card {i. i < length scheme \<and> fst (scheme!i) = l} = 2"
              proof -
                from less(3) have "card {i. i < length scheme \<and> fst (scheme!i) = l} \<in> {0, 2}"
                  by (by100 blast)
                moreover have "0 \<in> {i. i < length scheme \<and> fst (scheme!i) = l}"
                  using \<open>0 < length scheme\<close> unfolding l_def by (by100 blast)
                hence "{i. i < length scheme \<and> fst (scheme!i) = l} \<noteq> {}" by (by100 blast)
                hence "card {i. i < length scheme \<and> fst (scheme!i) = l} \<noteq> 0" by (by100 simp)
                ultimately show ?thesis by (by100 blast)
              qed
              \<comment> \<open>card = 2 and 0 is one element \<Rightarrow> there exists another.\<close>
              have "finite {i. i < length scheme \<and> fst (scheme!i) = l}" by (by100 simp)
              have h0_in_l: "0 \<in> {i. i < length scheme \<and> fst (scheme!i) = l}"
                using \<open>0 < length scheme\<close> unfolding l_def by (by100 blast)
              have "card ({i. i < length scheme \<and> fst (scheme!i) = l} - {0}) = 1"
                using \<open>card {i. i < length scheme \<and> fst (scheme!i) = l} = 2\<close> h0_in_l
                by (by100 simp)
              hence "{i. i < length scheme \<and> fst (scheme!i) = l} - {0} \<noteq> {}" by (by100 force)
              then obtain q where hq_props: "q \<in> {i. i < length scheme \<and> fst (scheme!i) = l} - {0}"
                by (by100 blast)
              hence "q \<noteq> 0" "q < length scheme" "fst (scheme!q) = l" by (by100 simp)+
              \<comment> \<open>Either 0 < q (so (q-0, 0, q) \<in> ?pairs) or q < 0 (impossible since q is nat).\<close>
              have "0 < q" using \<open>q \<noteq> 0\<close> by (by100 simp)
              hence "(q - 0, 0, q) \<in> ?pairs"
                using \<open>q < length scheme\<close> \<open>fst (scheme!q) = l\<close> \<open>0 < length scheme\<close>
                unfolding l_def by (by100 force)
              thus ?thesis by (by100 blast)
            qed
            \<comment> \<open>This set is finite (bounded by length scheme).\<close>
            have hpairs_fin: "finite ?pairs"
            proof -
              have "?pairs \<subseteq> (\<lambda>(q1,q2). (q2-q1, q1, q2)) ` {(q1,q2). q1 < length scheme \<and> q2 < length scheme}"
                by (by100 force)
              moreover have "finite {(q1,q2). q1 < length scheme \<and> q2 < length scheme}"
                by (by100 simp)
              ultimately show ?thesis using finite_subset by (by100 blast)
            qed
            \<comment> \<open>Pick a triple with minimum first component (gap).\<close>
            obtain g p1 p2 where hmin: "(g, p1, p2) \<in> ?pairs"
                "\<forall>(g',p1',p2') \<in> ?pairs. g \<le> g'"
            proof -
              \<comment> \<open>The set of first components (gaps) is finite non-empty nat, so has a minimum.\<close>
              let ?gaps = "fst ` ?pairs"
              have "finite ?gaps" using hpairs_fin by (by100 simp)
              have "?gaps \<noteq> {}" using hpairs_ne by (by100 force)
              define gmin where "gmin = Min ?gaps"
              have "gmin \<in> ?gaps" unfolding gmin_def using Min_in[OF \<open>finite ?gaps\<close> \<open>?gaps \<noteq> {}\<close>] .
              hence "\<exists>p1 p2. (gmin, p1, p2) \<in> ?pairs" by (by100 force)
              then obtain p1 p2 where "(gmin, p1, p2) \<in> ?pairs" by (by100 blast)
              moreover have "\<forall>(g',p1',p2') \<in> ?pairs. gmin \<le> g'"
              proof (intro ballI)
                fix x assume "x \<in> ?pairs"
                obtain g' p1' p2' where "x = (g', p1', p2')" by (cases x) (by100 force)
                hence "g' \<in> ?gaps" using \<open>x \<in> ?pairs\<close> by (by100 force)
                hence "gmin \<le> g'" unfolding gmin_def using Min_le[OF \<open>finite ?gaps\<close>] by (by100 blast)
                thus "case x of (g', p1', p2') \<Rightarrow> gmin \<le> g'"
                  using \<open>x = (g', p1', p2')\<close> by (by100 simp)
              qed
              ultimately show ?thesis using that[of gmin p1 p2] by (by100 blast)
            qed
            define a_lab where "a_lab = fst (scheme!p1)"
            \<comment> \<open>From hmin: p1 < p2, p2 < length scheme, same label, g = p2 - p1.\<close>
            have hmin_props: "p1 < p2" "p2 < length scheme" "fst (scheme!p1) = fst (scheme!p2)" "g = p2 - p1"
              using hmin(1) by (by100 force)+
            have "fst (scheme!p2) = a_lab" using hmin_props(3) unfolding a_lab_def by (by100 simp)
            have hp1_lt: "p1 < length scheme" using hmin_props(1,2) by (by100 linarith)
            \<comment> \<open>Opposite directions from torus type.\<close>
            have "snd (scheme!p1) \<noteq> snd (scheme!p2)"
            proof
              assume "snd (scheme!p1) = snd (scheme!p2)"
              hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                  \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
                apply (rule_tac x="fst (scheme!p1)" in exI)
                apply (rule_tac x=p1 in exI)
                using hmin_props(1,2) hp1_lt \<open>fst (scheme!p2) = a_lab\<close>
                unfolding a_lab_def by (by100 force)
              thus False using \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. _)\<close> by (by100 blast)
            qed
            \<comment> \<open>No same-label between: from properness (only 2 occurrences).\<close>
            have "\<forall>k. p1 < k \<and> k < p2 \<longrightarrow> fst (scheme!k) \<noteq> a_lab"
            proof (intro allI impI)
              fix k assume hk: "p1 < k \<and> k < p2"
              have hfin_a: "finite {i. i < length scheme \<and> fst (scheme!i) = a_lab}" by (by100 simp)
              have hcard_a: "card {i. i < length scheme \<and> fst (scheme!i) = a_lab} = 2"
              proof -
                from less(3) have "card {i. i < length scheme \<and> fst (scheme!i) = a_lab} \<in> {0, 2}"
                  by (by100 blast)
                moreover have "p1 \<in> {i. i < length scheme \<and> fst (scheme!i) = a_lab}"
                  using hp1_lt unfolding a_lab_def by (by100 blast)
                hence "{i. i < length scheme \<and> fst (scheme!i) = a_lab} \<noteq> {}" by (by100 blast)
                hence "card {i. i < length scheme \<and> fst (scheme!i) = a_lab} \<noteq> 0" by (by100 simp)
                ultimately show ?thesis by (by100 blast)
              qed
              have "{p1, p2} \<subseteq> {i. i < length scheme \<and> fst (scheme!i) = a_lab}"
                using hmin_props(1,2) \<open>fst (scheme!p2) = a_lab\<close> unfolding a_lab_def by (by100 force)
              have "card {p1, p2} = 2" using hmin_props(1) by (by100 simp)
              from card_seteq[OF hfin_a \<open>{p1,p2} \<subseteq> _\<close>] hcard_a this
              have "{i. i < length scheme \<and> fst (scheme!i) = a_lab} = {p1, p2}" by (by100 simp)
              moreover have "k \<noteq> p1" "k \<noteq> p2" using hk by (by100 linarith)+
              ultimately have "k \<notin> {i. i < length scheme \<and> fst (scheme!i) = a_lab}" by (by100 blast)
              moreover have "k < length scheme" using hk hmin_props(2) by (by100 linarith)
              ultimately show "fst (scheme!k) \<noteq> a_lab" by (by100 blast)
            qed
            \<comment> \<open>Minimality: for any other same-label pair, gap \<ge> g = p2-p1.\<close>
            have "\<forall>l q1 q2. q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = l
                \<and> fst (scheme!q2) = l \<longrightarrow> p2 - p1 \<le> q2 - q1"
            proof (intro allI impI)
              fix l q1 q2 assume hq: "q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = l \<and> fst (scheme!q2) = l"
              hence "(q2 - q1, q1, q2) \<in> ?pairs" by (by100 force)
              from hmin(2) this have "g \<le> q2 - q1" by (by100 force)
              thus "p2 - p1 \<le> q2 - q1" using hmin_props(4) by (by100 simp)
            qed
            show ?thesis
              using \<open>p1 < p2\<close> \<open>p2 < length scheme\<close> \<open>fst (scheme!p2) = a_lab\<close>
                  \<open>snd (scheme!p1) \<noteq> snd (scheme!p2)\<close>
                  \<open>\<forall>k. p1 < k \<and> k < p2 \<longrightarrow> fst (scheme!k) \<noteq> a_lab\<close>
                  \<open>\<forall>l q1 q2. q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = l
                      \<and> fst (scheme!q2) = l \<longrightarrow> p2 - p1 \<le> q2 - q1\<close>
              unfolding a_lab_def by blast
          qed
          then obtain a_lab p1 p2 where hclose:
              "p1 < p2" "p2 < length scheme"
              "fst (scheme!p1) = a_lab" "fst (scheme!p2) = a_lab"
              "snd (scheme!p1) \<noteq> snd (scheme!p2)"
              "\<forall>k. p1 < k \<and> k < p2 \<longrightarrow> fst (scheme!k) \<noteq> a_lab"
              "\<forall>l q1 q2. q1 < q2 \<and> q2 < length scheme \<and> fst (scheme!q1) = l
                  \<and> fst (scheme!q2) = l \<longrightarrow> p2 - p1 \<le> q2 - q1"
            by blast
          \<comment> \<open>Step 2: p2 > p1 + 1 (no adjacent same-label from no\_adj\_gt4).\<close>
          have hgap: "p2 > p1 + 1"
          proof (rule ccontr)
            assume "\<not> p2 > p1 + 1"
            hence "p2 = p1 + 1" using hclose(1) by (by100 simp)
            hence "fst (scheme!p1) = fst (scheme!(p1+1))" using hclose(3,4) by (by100 simp)
            moreover have "snd (scheme!p1) \<noteq> snd (scheme!(p1+1))"
              using hclose(5) \<open>p2 = p1 + 1\<close> by (by100 simp)
            moreover have "p1 + 1 < length scheme" using hclose(2) \<open>p2 = p1 + 1\<close> by (by100 simp)
            ultimately show False using hhno_adj_gt4 by (by100 blast)
          qed
          \<comment> \<open>Step 3: Element at p1+1 has label b \<noteq> a\_lab.\<close>
          define b_lab where "b_lab = fst (scheme!(p1+1))"
          have "b_lab \<noteq> a_lab"
            using hclose(6)[rule_format, of "p1+1"] hgap unfolding b_lab_def by (by100 simp)
          \<comment> \<open>Step 4: Rotate + flip to standard form, then use cut\_paste\_opp.
             This produces the required pattern w0@[(a,T),(b,T)]@w1@[(a,F),(b,F)]@w2.\<close>
          \<comment> \<open>Detailed construction: rotate scheme to bring (a\_lab,dir) to front,
             flip if needed so a has True direction, find b's inverse,
             use cut\_paste\_opp to bring b\<inverse> adjacent to a\<inverse>.\<close>
          \<comment> \<open>Step 4a: Rotate scheme to bring p1 to front.\<close>
          have "top1_valid_scheme_equiv scheme (drop p1 scheme @ take p1 scheme)"
            using valid_imp_equiv[OF top1_valid_scheme_operation.v_rotate[of "take p1 scheme" "drop p1 scheme"]]
            by (by100 simp)
          \<comment> \<open>Step 4b: Flip a\_lab and b\_lab directions to True, then reverse cut\_paste\_opp.\<close>
          \<comment> \<open>After rotation, the scheme has (a\_lab,dir\_a) at position 0, (b\_lab,dir\_b) at position 1,
             (a\_lab,\\<not>dir\_a) at position (p2-p1), and (b\_lab,\\<not>dir\_b) at some position k > p2-p1.
             Flip a\_lab if dir\_a=False, flip b\_lab if dir\_b=False.
             Then apply reverse cut\_paste\_opp with a\_lab to move material between
             (a\_lab,F) and (b\_lab,F) to before (a\_lab,T).
             Result: before\_b\_inv @ [(a\_lab,T),(b\_lab,T)] @ middle @ [(a\_lab,F),(b\_lab,F)] @ after\_b\_inv.\<close>
          \<comment> \<open>The whole chain: scheme \<sim> rotated \<sim> flipped \<sim> pattern.\<close>
          \<comment> \<open>Step 4b-i: Flip a\_lab direction to True (if not already).\<close>
          define R where "R = drop p1 scheme @ take p1 scheme"
          have hR_equiv: "top1_valid_scheme_equiv scheme R" using \<open>top1_valid_scheme_equiv scheme (drop p1 scheme @ take p1 scheme)\<close>
            unfolding R_def .
          define dir_a where "dir_a = snd (scheme!p1)"
          define dir_b where "dir_b = snd (scheme!(p1+1))"
          \<comment> \<open>Step 4b-ii: Apply flip\_label a\_lab if dir\_a = False, then flip\_label b\_lab if dir\_b = False.
             After both flips: front is (a\_lab,T), next is (b\_lab,T), (a\_lab,F) at gap position.
             Then decompose and apply reverse cut\_paste\_opp.\<close>
          \<comment> \<open>Step 4b-iii: The flipped+rotated scheme has the form
             [(a\_lab,T),(b\_lab,T)] @ mid @ [(a\_lab,F)] @ between @ [(b\_lab,F)] @ after.
             Apply reverse cut\_paste\_opp to move 'between' before (a\_lab,T).\<close>
          \<comment> \<open>For now: produce the existential directly (gap for the chain construction).\<close>
          have "\<exists>w0 w1 w2. top1_valid_scheme_equiv scheme
              (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2)
              \<and> length w0 + length w1 + length w2 + 4 = length scheme
              \<and> (\<forall>l. length (filter (\<lambda>e. fst e = l)
                  (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2))
                = length (filter (\<lambda>e. fst e = l) scheme))"
          proof -
            \<comment> \<open>Step A: Flip a\_lab direction. scheme \<sim> R. Then R \<sim> R\_a (a\_lab has True at front).\<close>
            define R_a where "R_a = (if dir_a then R else
                map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R)"
            have hRa_equiv: "top1_valid_scheme_equiv scheme R_a"
            proof (cases dir_a)
              case True thus ?thesis unfolding R_a_def using hR_equiv by (by100 simp)
            next
              case False
              hence "R_a = map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R" unfolding R_a_def by (by100 simp)
              moreover have "top1_valid_scheme_equiv R (map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R)"
                using valid_imp_equiv[OF top1_valid_scheme_operation.v_flip_label[of R a_lab]] by (by100 simp)
              ultimately show ?thesis using hR_equiv unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
            qed
            \<comment> \<open>Step B: Flip b\_lab direction. R\_a \<sim> R\_ab (b\_lab has True at position 1).\<close>
            define R_ab where "R_ab = (if dir_b then R_a else
                map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a)"
            have hRab_equiv: "top1_valid_scheme_equiv scheme R_ab"
            proof (cases dir_b)
              case True thus ?thesis unfolding R_ab_def using hRa_equiv by (by100 simp)
            next
              case False
              hence "R_ab = map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a" unfolding R_ab_def by (by100 simp)
              moreover have "top1_valid_scheme_equiv R_a (map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a)"
                using valid_imp_equiv[OF top1_valid_scheme_operation.v_flip_label[of R_a b_lab]] by (by100 simp)
              ultimately show ?thesis using hRa_equiv unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
            qed
            \<comment> \<open>Step C: R\_ab has the form [(a\_lab,T),(b\_lab,T)] @ mid @ [(a\_lab,F)] @ between @ [(b\_lab,F)] @ after.\<close>
            have hRab_len: "length R_ab = length scheme"
              unfolding R_ab_def R_a_def R_def by (by100 simp)
            have hp1_lt: "p1 < length scheme" using hclose(1,2) by (by100 linarith)
            have hp1_1_lt: "p1 + 1 < length scheme" using hgap hclose(2) by (by100 linarith)
            have hdrop_ne: "drop p1 scheme \<noteq> []" using hp1_lt by (by100 simp)
            have hR_0: "R ! 0 = scheme ! p1"
            proof -
              have hlen_drop: "0 < length (drop p1 scheme)" using hp1_lt by (by100 simp)
              have "(drop p1 scheme @ take p1 scheme) ! 0 = (drop p1 scheme) ! 0"
                using nth_append[of "drop p1 scheme" "take p1 scheme" 0] hlen_drop by (by100 simp)
              also have "\<dots> = scheme ! p1" using hp1_lt by (by100 simp)
              finally show ?thesis unfolding R_def .
            qed
            have hR_1: "R ! 1 = scheme ! (p1+1)"
            proof -
              have hlen_drop: "1 < length (drop p1 scheme)" using hp1_1_lt by (by100 simp)
              have "(drop p1 scheme @ take p1 scheme) ! 1 = (drop p1 scheme) ! 1"
                using nth_append[of "drop p1 scheme" "take p1 scheme" 1] hlen_drop by (by100 simp)
              also have "\<dots> = scheme ! (p1 + 1)" using hp1_1_lt by (by100 simp)
              finally show ?thesis unfolding R_def .
            qed
            define gap where "gap = p2 - p1"
            have hR_gap: "R ! gap = scheme ! p2"
            proof -
              have hlen_drop_gap: "gap < length (drop p1 scheme)" unfolding gap_def using hclose(1,2) by (by100 simp)
              have "(drop p1 scheme @ take p1 scheme) ! gap = (drop p1 scheme) ! gap"
                using nth_append[of "drop p1 scheme" "take p1 scheme" gap] hlen_drop_gap by (by100 simp)
              also have "\<dots> = scheme ! (p1 + gap)"
                using hclose(1,2) unfolding gap_def by (by100 simp)
              also have "p1 + gap = p2" unfolding gap_def using hclose(1) by (by100 simp)
              finally show ?thesis unfolding R_def .
            qed
            \<comment> \<open>After flips: R\_ab!0 = (a\_lab, True), R\_ab!1 = (b\_lab, True), R\_ab!gap = (a\_lab, False).\<close>
            have hR_len: "length R = length scheme" unfolding R_def by (by100 simp)
            have hRa_len: "length R_a = length R" unfolding R_a_def by (by100 simp)
            have h0_lt: "0 < length R" using hp1_lt hR_len by (by100 linarith)
            have h1_lt: "1 < length R" using hp1_1_lt hR_len by (by100 linarith)
            have hgap_lt: "gap < length R" unfolding gap_def using hclose(2) hR_len by (by100 linarith)
            \<comment> \<open>R\_a!i = flip-a applied to R!i.\<close>
            have hRa_nth: "\<And>i. i < length R \<Longrightarrow>
                R_a ! i = (if dir_a then R ! i else (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) (R ! i))"
              unfolding R_a_def by (by100 simp)
            \<comment> \<open>R\_ab!i = flip-b applied to R\_a!i.\<close>
            have hRab_nth: "\<And>i. i < length R \<Longrightarrow>
                R_ab ! i = (if dir_b then R_a ! i else (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) (R_a ! i))"
              unfolding R_ab_def using hRa_len by (by100 simp)
            have hRab_0: "R_ab ! 0 = (a_lab, True)"
            proof -
              have "R ! 0 = (a_lab, dir_a)"
                using hR_0 hclose(3) unfolding dir_a_def
                by (cases "scheme ! p1") (by100 simp)
              hence "R_a ! 0 = (a_lab, True)" using hRa_nth[OF h0_lt] by (cases dir_a) (by100 simp)+
              moreover have "a_lab \<noteq> b_lab" using \<open>b_lab \<noteq> a_lab\<close> by (by100 simp)
              ultimately show ?thesis using hRab_nth[OF h0_lt] by (cases dir_b) (by100 simp)+
            qed
            have hRab_1: "R_ab ! 1 = (b_lab, True)"
            proof -
              have "R ! 1 = (b_lab, dir_b)"
                using hR_1 unfolding b_lab_def dir_b_def
                by (cases "scheme ! (p1+1)") (by100 simp)
              hence "R_a ! 1 = (b_lab, dir_b)"
                using hRa_nth[OF h1_lt] \<open>b_lab \<noteq> a_lab\<close> by (cases dir_a) (by100 simp)+
              thus ?thesis using hRab_nth[OF h1_lt] by (cases dir_b) (by100 simp)+
            qed
            have hRab_gap: "R_ab ! gap = (a_lab, False)"
            proof -
              have hR_gap_val: "R ! gap = (a_lab, \<not> dir_a)"
                using hR_gap hclose(3,4,5) unfolding dir_a_def
                by (cases "scheme ! p1", cases "scheme ! p2") (by100 simp)
              have "R_a ! gap = (a_lab, False)"
              proof (cases dir_a)
                case True
                hence "R_a ! gap = R ! gap" using hRa_nth[OF hgap_lt] by (by100 simp)
                thus ?thesis using hR_gap_val True by (by100 simp)
              next
                case False
                hence "R_a ! gap = (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) (R ! gap)"
                  using hRa_nth[OF hgap_lt] by (by100 simp)
                also have "\<dots> = (a_lab, \<not> (\<not> dir_a))" using hR_gap_val by (by100 simp)
                also have "\<dots> = (a_lab, False)" using False by (by100 simp)
                finally show ?thesis .
              qed
              moreover have "a_lab \<noteq> b_lab" using \<open>b_lab \<noteq> a_lab\<close> by (by100 simp)
              ultimately show ?thesis using hRab_nth[OF hgap_lt] by (cases dir_b) (by100 simp)+
            qed
            have hgap_gt1: "gap > 1" using hgap unfolding gap_def by (by100 linarith)
            \<comment> \<open>Step D: Find position of (b\_lab, False) in R\_ab. It is at some position k\_b > gap.\<close>
            have "\<exists>k_b. k_b > gap \<and> k_b < length R_ab \<and> R_ab ! k_b = (b_lab, False)"
            proof -
              \<comment> \<open>b\_lab appears exactly twice in scheme. Properness gives card = 2.\<close>
              have hcard_b: "card {i. i < length scheme \<and> fst (scheme!i) = b_lab} = 2"
              proof -
                from less(3) have "card {i. i < length scheme \<and> fst (scheme!i) = b_lab} \<in> {0, 2}"
                  by (by100 blast)
                moreover have "p1+1 \<in> {i. i < length scheme \<and> fst (scheme!i) = b_lab}"
                  using hp1_1_lt b_lab_def by (by100 blast)
                hence "{i. i < length scheme \<and> fst (scheme!i) = b_lab} \<noteq> {}" by (by100 blast)
                hence "card {i. i < length scheme \<and> fst (scheme!i) = b_lab} \<noteq> 0" by (by100 simp)
                ultimately show ?thesis by (by100 blast)
              qed
              \<comment> \<open>Position p1+1 is one occurrence. Get the other, call it q\_b.\<close>
              have hp1_1_in: "p1 + 1 \<in> {i. i < length scheme \<and> fst (scheme!i) = b_lab}"
                using hp1_1_lt b_lab_def by (by100 blast)
              have hfin_b: "finite {i. i < length scheme \<and> fst (scheme!i) = b_lab}" by (by100 simp)
              have "card ({i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1}) = 1"
                using hfin_b hp1_1_in hcard_b by (by100 simp)
              have "{i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1} \<noteq> {}"
              proof
                assume "{i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1} = {}"
                hence "card ({i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1}) = 0" by (by100 simp)
                thus False using \<open>card ({i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1}) = 1\<close> by (by100 simp)
              qed
              then obtain q_b where hqb: "q_b \<in> {i. i < length scheme \<and> fst (scheme!i) = b_lab} - {p1+1}"
                by (by100 blast)
              hence hqb_props: "q_b < length scheme" "fst (scheme!q_b) = b_lab" "q_b \<noteq> p1 + 1"
                by (by100 simp)+
              \<comment> \<open>By minimality: gap between b\_lab's positions \<ge> a\_lab's gap.\<close>
              \<comment> \<open>The two b\_lab positions are p1+1 and q\_b. Their linear gap (larger - smaller)
                 must be \<ge> p2-p1 = gap. So q\_b is NOT between p1+1 and p2.\<close>
              have "q_b \<notin> {p1+2..p2}"
              proof
                assume "q_b \<in> {p1+2..p2}"
                hence "p1 + 1 < q_b" "q_b \<le> p2" by (by100 simp)+
                \<comment> \<open>b\_lab positions are p1+1 < q\_b, both < length scheme.\<close>
                have "fst (scheme!(p1+1)) = b_lab" using b_lab_def by (by100 simp)
                have "p1 + 1 < q_b \<and> q_b < length scheme \<and> fst (scheme!(p1+1)) = b_lab
                    \<and> fst (scheme!q_b) = b_lab"
                  using \<open>p1 + 1 < q_b\<close> hp1_1_lt hqb_props(1,2) \<open>fst (scheme!(p1+1)) = b_lab\<close>
                  by (by100 blast)
                hence "p2 - p1 \<le> q_b - (p1+1)" using hclose(7) by (by100 blast)
                hence "q_b \<ge> p2 + 1" using \<open>p1 + 1 < q_b\<close> hclose(1) by (by100 linarith)
                thus False using \<open>q_b \<le> p2\<close> by (by100 linarith)
              qed
              \<comment> \<open>In R\_ab, q\_b maps to position (q\_b - p1) mod (length scheme).
                 Since q\_b \<notin> {p1+2..p2}, the R\_ab position is > gap.\<close>
              define k_b where "k_b = (if q_b > p1 then q_b - p1 else q_b + length scheme - p1)"
              have "k_b > gap"
              proof (cases "q_b > p1")
                case True
                hence "k_b = q_b - p1" unfolding k_b_def by (by100 simp)
                moreover have "q_b > p2" using \<open>q_b \<notin> {p1+2..p2}\<close> hqb_props(3) True by (by100 simp)
                ultimately show ?thesis unfolding gap_def using hclose(1) by (by100 linarith)
              next
                case False
                hence "q_b \<le> p1" by (by100 simp)
                hence "k_b = q_b + length scheme - p1" unfolding k_b_def by (by100 simp)
                moreover have "gap < length scheme - p1" unfolding gap_def using hclose(1,2) by (by100 linarith)
                ultimately show ?thesis by (by100 linarith)
              qed
              have "k_b < length R_ab"
              proof (cases "q_b > p1")
                case True
                hence "k_b = q_b - p1" unfolding k_b_def by (by100 simp)
                thus ?thesis using hqb_props(1) hRab_len by (by100 linarith)
              next
                case False
                hence "q_b \<le> p1" by (by100 simp)
                have "q_b \<noteq> p1"
                proof
                  assume "q_b = p1"
                  hence "fst (scheme!p1) = b_lab" using hqb_props(2) by (by100 simp)
                  hence "a_lab = b_lab" using hclose(3) by (by100 simp)
                  thus False using \<open>b_lab \<noteq> a_lab\<close> by (by100 simp)
                qed
                hence "q_b < p1" using \<open>q_b \<le> p1\<close> by (by100 linarith)
                hence "k_b = q_b + length scheme - p1" unfolding k_b_def using False by (by100 simp)
                thus ?thesis using \<open>q_b < p1\<close> hp1_lt hRab_len by (by100 linarith)
              qed
              have hkb_lt_R: "k_b < length R" using \<open>k_b < length R_ab\<close> hRab_len hR_len by (by100 linarith)
              have hR_kb: "R ! k_b = scheme ! q_b"
                proof (cases "q_b > p1")
                  case True
                  hence hkb_eq: "k_b = q_b - p1" unfolding k_b_def by (by100 simp)
                  have "k_b < length (drop p1 scheme)" using hqb_props(1) True hkb_eq by (by100 simp)
                  hence "(drop p1 scheme @ take p1 scheme) ! k_b = (drop p1 scheme) ! k_b"
                    using nth_append[of "drop p1 scheme" "take p1 scheme" k_b] by (by100 simp)
                  also have "\<dots> = scheme ! (p1 + k_b)" using hqb_props(1) hkb_eq True by (by100 simp)
                  also have "p1 + k_b = q_b" using hkb_eq True by (by100 linarith)
                  finally show ?thesis unfolding R_def by (by100 simp)
                next
                  case False
                  hence hqb_le: "q_b \<le> p1" by (by100 simp)
                  hence hkb_eq: "k_b = q_b + length scheme - p1" unfolding k_b_def by (by100 simp)
                  have "length (drop p1 scheme) = length scheme - p1" by (by100 simp)
                  have "k_b \<ge> length scheme - p1"
                    using hqb_le hp1_lt hkb_eq by (by100 linarith)
                  hence "k_b \<ge> length (drop p1 scheme)"
                    using \<open>length (drop p1 scheme) = length scheme - p1\<close> by (by100 simp)
                  hence "(drop p1 scheme @ take p1 scheme) ! k_b
                      = (take p1 scheme) ! (k_b - length (drop p1 scheme))"
                    using nth_append[of "drop p1 scheme" "take p1 scheme" k_b] by (by100 simp)
                  also have "k_b - length (drop p1 scheme) = q_b"
                    using hkb_eq hp1_lt by (by100 simp)
                  also have "q_b \<noteq> p1"
                  proof
                    assume "q_b = p1"
                    hence "b_lab = a_lab" using hqb_props(2) hclose(3) by (by100 simp)
                    thus False using \<open>b_lab \<noteq> a_lab\<close> by (by100 simp)
                  qed
                  hence "q_b < p1" using hqb_le by (by100 linarith)
                  hence "(take p1 scheme) ! q_b = scheme ! q_b" by (by100 simp)
                  finally show ?thesis unfolding R_def .
                qed
              have "fst (R ! k_b) = b_lab" using hR_kb hqb_props(2) by (by100 simp)
              hence "fst (R_a ! k_b) = b_lab"
                using hRa_nth[OF hkb_lt_R] \<open>b_lab \<noteq> a_lab\<close>
                by (cases dir_a, by100 simp, cases "R ! k_b", by100 simp)
              hence "fst (R_ab ! k_b) = b_lab"
                using hRab_nth[OF hkb_lt_R]
                by (cases dir_b, by100 simp, cases "R_a ! k_b", by100 simp)
              \<comment> \<open>Direction: torus type means b\_lab has opposite dirs at its two positions.
                 Position 1 has True (after flip). So k\_b has False.\<close>
              have "snd (R_ab ! k_b) \<noteq> snd (R_ab ! 1)"
              proof
                assume heq: "snd (R_ab ! k_b) = snd (R_ab ! 1)"
                \<comment> \<open>Both R\_ab positions have fst = b\_lab. If snd is equal, this gives
                   a same-direction pair for b\_lab, contradicting torus type.
                   Track snd through flips: flip b\_lab affects BOTH equally (both have fst=b\_lab),
                   flip a\_lab affects NEITHER (a\_lab \<noteq> b\_lab). So snd equality in R\_ab
                   implies snd equality in R, hence in scheme.\<close>
                \<comment> \<open>R\_ab!i for fst=b\_lab: flip a\_lab is identity, flip b\_lab negates both.\<close>
                have "snd (R ! k_b) = snd (R ! 1)"
                proof -
                  \<comment> \<open>R\_a!i = R!i when fst(R!i) \<noteq> a\_lab (flip a doesn't touch b\_lab).\<close>
                  have "snd (R_a ! k_b) = snd (R ! k_b)"
                    using hRa_nth[OF hkb_lt_R] \<open>fst (R ! k_b) = b_lab\<close> \<open>b_lab \<noteq> a_lab\<close>
                    by (cases dir_a, by100 simp, cases "R ! k_b", by100 simp)
                  have hR1_fst: "fst (R ! 1) = b_lab" using hR_1 b_lab_def by (by100 simp)
                  have "snd (R_a ! 1) = snd (R ! 1)"
                    using hRa_nth[OF h1_lt] hR1_fst \<open>b_lab \<noteq> a_lab\<close>
                    by (cases dir_a, by100 simp, cases "R ! 1", by100 simp)
                  \<comment> \<open>R\_ab!i for fst=b\_lab: flip b\_lab negates both equally.\<close>
                  have hRa1_fst: "fst (R_a ! 1) = b_lab"
                    using hRa_nth[OF h1_lt] hR1_fst \<open>b_lab \<noteq> a_lab\<close>
                    by (cases dir_a, by100 simp, cases "R ! 1", by100 simp)
                  have hsnd_kb: "snd (R_ab ! k_b) = (if dir_b then snd (R_a ! k_b) else \<not> snd (R_a ! k_b))"
                    using hRab_nth[OF hkb_lt_R] \<open>fst (R_a ! k_b) = b_lab\<close>
                    by (cases dir_b, by100 simp, cases "R_a ! k_b", by100 simp)
                  have hsnd_1: "snd (R_ab ! 1) = (if dir_b then snd (R_a ! 1) else \<not> snd (R_a ! 1))"
                    using hRab_nth[OF h1_lt] hRa1_fst
                    by (cases dir_b, by100 simp, cases "R_a ! 1", by100 simp)
                  from heq hsnd_kb hsnd_1
                  have "snd (R_a ! k_b) = snd (R_a ! 1)" by (cases dir_b) (by100 simp)+
                  thus ?thesis using \<open>snd (R_a ! k_b) = snd (R ! k_b)\<close> \<open>snd (R_a ! 1) = snd (R ! 1)\<close>
                    by (by100 simp)
                qed
                \<comment> \<open>R!1 = scheme!(p1+1), R!k\_b = scheme!q\_b. So snd(scheme!(p1+1)) = snd(scheme!q\_b).\<close>
                hence "snd (scheme!(p1+1)) = snd (scheme!q_b)"
                  using hR_1 hR_kb by (by100 simp)
                \<comment> \<open>This gives a same-direction pair for b\_lab, contradicting torus type.\<close>
                hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                    \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
                  using hp1_1_lt hqb_props b_lab_def by (by100 blast)
                thus False using \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. _)\<close> by (by100 blast)
              qed
              hence "snd (R_ab ! k_b) = False" using hRab_1 by (by100 simp)
              have "R_ab ! k_b = (b_lab, False)"
                using \<open>fst (R_ab ! k_b) = b_lab\<close> \<open>snd (R_ab ! k_b) = False\<close>
                by (cases "R_ab ! k_b") (by100 simp)
              thus ?thesis using \<open>k_b > gap\<close> \<open>k_b < length R_ab\<close> by (by100 blast)
            qed
            then obtain k_b where hkb: "k_b > gap" "k_b < length R_ab" "R_ab ! k_b = (b_lab, False)"
              by (by100 blast)
            \<comment> \<open>Step E: Decompose R\_ab at positions 0, 1, gap, k\_b.\<close>
            define mid where "mid = take (gap - 2) (drop 2 R_ab)"
            define between where "between = take (k_b - gap - 1) (drop (gap + 1) R_ab)"
            define after where "after = drop (k_b + 1) R_ab"
            have hRab_decomp: "R_ab = [(a_lab,True),(b_lab,True)] @ mid @ [(a_lab,False)]
                @ between @ [(b_lab,False)] @ after"
            proof -
              \<comment> \<open>Split at position gap: R\_ab = take gap R\_ab @ [R\_ab!gap] @ drop(gap+1) R\_ab.\<close>
              have hgap_lt_Rab: "gap < length R_ab" using hgap_lt hRab_len hR_len by (by100 linarith)
              have "R_ab = take gap R_ab @ R_ab!gap # drop (Suc gap) R_ab"
                using id_take_nth_drop[of gap R_ab] hgap_lt_Rab by (by100 simp)
              hence s1: "R_ab = take gap R_ab @ [(a_lab,False)] @ drop (gap+1) R_ab"
                using hRab_gap by (by100 simp)
              \<comment> \<open>take gap R\_ab = [R\_ab!0, R\_ab!1] @ mid. Split at positions 0 and 1.\<close>
              have h2_le_gap: "2 \<le> gap" using hgap_gt1 by (by100 linarith)
              have "take gap R_ab = take 2 R_ab @ drop 2 (take gap R_ab)"
                using append_take_drop_id[of 2 "take gap R_ab"] h2_le_gap by (by100 simp)
              moreover have "take 2 R_ab = [R_ab!0, R_ab!1]"
                using h0_lt h1_lt hRab_len hR_len by (cases R_ab, by100 simp, cases "tl R_ab", by100 simp, by100 simp)
              moreover have "drop 2 (take gap R_ab) = take (gap - 2) (drop 2 R_ab)"
                using h2_le_gap by (simp add: drop_take)
              ultimately have htake_gap: "take gap R_ab = [(a_lab,True),(b_lab,True)] @ mid"
                using hRab_0 hRab_1 unfolding mid_def by (by100 simp)
              \<comment> \<open>drop(gap+1) R\_ab: split at position k\_b-gap-1.\<close>
              \<comment> \<open>Split drop(gap+1) R\_ab at position k\_b-gap-1.\<close>
              have hkb_rel: "k_b - gap - 1 < length (drop (gap+1) R_ab)"
                using hkb(1,2) by (by100 simp)
              have "(drop (gap+1) R_ab) ! (k_b - gap - 1) = R_ab ! k_b"
                using hkb(1,2) by (by100 simp)
              hence hrel_blab: "(drop (gap+1) R_ab) ! (k_b - gap - 1) = (b_lab, False)"
                using hkb(3) by (by100 simp)
              let ?d = "drop (gap+1) R_ab"
              have "?d = take (k_b-gap-1) ?d @ ?d!(k_b-gap-1) # drop (Suc (k_b-gap-1)) ?d"
                using id_take_nth_drop[OF hkb_rel] by (by100 simp)
              hence "?d = take (k_b-gap-1) ?d @ [(b_lab,False)] @ drop (Suc (k_b-gap-1)) ?d"
                using hrel_blab by (by100 simp)
              moreover have "Suc (k_b - gap - 1) = k_b - gap" using hkb(1) by (by100 linarith)
              moreover have "drop (k_b - gap) ?d = drop (k_b+1) R_ab"
              proof -
                have "k_b - gap + (gap + 1) = k_b + 1" using hkb(1) by (by100 linarith)
                thus ?thesis by (simp add: drop_drop)
              qed
              ultimately have hdrop_gap: "drop (gap+1) R_ab = between @ [(b_lab,False)] @ after"
                unfolding between_def after_def by (by100 simp)
              show ?thesis using s1 htake_gap hdrop_gap by (by100 simp)
            qed
            \<comment> \<open>Step F: Apply reverse cut\_paste\_opp with a\_lab.
               u0 @ [(a\_lab,T)] @ u2 @ [(a\_lab,F)] @ u1 @ u3
               \<to> u0 @ u1 @ [(a\_lab,T)] @ u2 @ [(a\_lab,F)] @ u3
               with u0 = [], u2 = [(b\_lab,T)]@mid, u1 = between@[(b\_lab,F)], ... wait
               Actually we want to move 'between' from between (a\_lab,F) and (b\_lab,F) to before (a\_lab,T).\<close>
            \<comment> \<open>The reverse cut\_paste\_opp with c = a\_lab:
               [] @ [(a\_lab,T)] @ [(b\_lab,T)]@mid @ [(a\_lab,F)] @ between @ [(b\_lab,F)]@after
               \<to> between @ [(a\_lab,T)] @ [(b\_lab,T)]@mid @ [(a\_lab,F)] @ [(b\_lab,F)]@after
               This moves 'between' from after (a\_lab,F) to before (a\_lab,T).\<close>
            have "top1_valid_scheme_equiv R_ab
                (between @ [(a_lab,True),(b_lab,True)] @ mid @ [(a_lab,False),(b_lab,False)] @ after)"
            proof -
              \<comment> \<open>R\_ab = [] @ [(a\_lab,T)] @ [(b\_lab,T)]@mid @ [(a\_lab,F)] @ between @ [(b\_lab,F)]@after
                 This is: u0 @ [(c,T)] @ u2 @ [(c,F)] @ u1 @ u3 with c=a\_lab,
                 u0=[], u2=[(b\_lab,T)]@mid, u1=between, u3=[(b\_lab,F)]@after.
                 Reverse cut\_paste\_opp (3 steps): ~ u0 @ u1 @ [(c,T)] @ u2 @ [(c,F)] @ u3
                 = between @ [(a\_lab,T),(b\_lab,T)] @ mid @ [(a\_lab,F),(b\_lab,F)] @ after.\<close>
              define u0 :: "(nat \<times> bool) list" where "u0 = []"
              define u2 where "u2 = [(b_lab,True)] @ mid"
              define u1 where "u1 = between"
              define u3 where "u3 = [(b_lab,False)] @ after"
              have hRab_eq: "R_ab = u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1 @ u3"
                using hRab_decomp unfolding u0_def u2_def u1_def u3_def by (by100 simp)
              \<comment> \<open>3 elementary operations: rotate + cut\_paste\_opp + rotate.\<close>
              have r1: "top1_valid_scheme_operation
                  (u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1 @ u3)
                  (u3 @ u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1)"
                using top1_valid_scheme_operation.v_rotate
                  [of "u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1" u3] by simp
              have r2: "top1_valid_scheme_operation
                  (u3 @ u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1)
                  ([(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3 @ u0 @ u1)"
                using top1_valid_scheme_operation.v_cut_paste_opp
                  [of "[]" "u3 @ u0" a_lab u2 u1] by simp
              have r3: "top1_valid_scheme_operation
                  ([(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3 @ u0 @ u1)
                  (u0 @ u1 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3)"
                using top1_valid_scheme_operation.v_rotate
                  [of "[(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3" "u0 @ u1"] by simp
              have "top1_valid_scheme_equiv R_ab (u0 @ u1 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3)"
                unfolding hRab_eq top1_valid_scheme_equiv_def
                using r1 r2 r3 by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
              thus ?thesis unfolding u0_def u1_def u2_def u3_def by (by100 simp)
            qed
            hence "top1_valid_scheme_equiv scheme
                (between @ [(a_lab,True),(b_lab,True)] @ mid @ [(a_lab,False),(b_lab,False)] @ after)"
              using hRab_equiv unfolding top1_valid_scheme_equiv_def by (meson rtranclp_trans)
            moreover have "length between + length mid + length after + 4 = length scheme"
            proof -
              have "length R_ab = 2 + length mid + 1 + length between + 1 + length after"
                using hRab_decomp by (by100 simp)
              thus ?thesis using hRab_len hR_len by (by100 linarith)
            qed
            moreover have "\<forall>l. length (filter (\<lambda>e. fst e = l)
                (between @ [(a_lab, True), (b_lab, True)] @ mid @ [(a_lab, False), (b_lab, False)] @ after))
              = length (filter (\<lambda>e. fst e = l) scheme)"
            proof (intro allI)
              fix l
              \<comment> \<open>Chain: scheme \\<to> R (rotate) \\<to> R\_a (flip a) \\<to> R\_ab (flip b) \\<to> rearranged.
                 Each step preserves fst-filter-counts.\<close>
              have fc_R: "length (filter (\<lambda>e. fst e = l) R) = length (filter (\<lambda>e. fst e = l) scheme)"
              proof -
                have "length (filter (\<lambda>e. fst e = l) (take p1 scheme @ drop p1 scheme))
                    = length (filter (\<lambda>e. fst e = l) (drop p1 scheme @ take p1 scheme))"
                  using filter_count_rotate by (by100 blast)
                thus ?thesis unfolding R_def by (by100 simp)
              qed
              have fc_Ra: "length (filter (\<lambda>e. fst e = l) R_a) = length (filter (\<lambda>e. fst e = l) R)"
                unfolding R_a_def using filter_count_flip_label[of l a_lab R] by (by100 simp)
              have fc_Rab: "length (filter (\<lambda>e. fst e = l) R_ab) = length (filter (\<lambda>e. fst e = l) R_a)"
                unfolding R_ab_def using filter_count_flip_label[of l b_lab R_a] by (by100 simp)
              \<comment> \<open>R\_ab is rearranged to between@[(a,T),(b,T)]@mid@[(a,F),(b,F)]@after by cut\_paste\_opp+rotate.
                 These preserve filter-counts.\<close>
              have fc_inter: "length (filter (\<lambda>e. fst e = l)
                  (between @ [(a_lab, True), (b_lab, True)] @ mid @ [(a_lab, False), (b_lab, False)] @ after))
                = length (filter (\<lambda>e. fst e = l) R_ab)"
                unfolding hRab_decomp by (by100 simp)
              show "length (filter (\<lambda>e. fst e = l)
                  (between @ [(a_lab, True), (b_lab, True)] @ mid @ [(a_lab, False), (b_lab, False)] @ after))
                = length (filter (\<lambda>e. fst e = l) scheme)"
                using fc_R fc_Ra fc_Rab fc_inter by (by100 linarith)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          then obtain w0 w1 w2 where hw_equiv: "top1_valid_scheme_equiv scheme
              (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2)"
              and hw_len: "length w0 + length w1 + length w2 + 4 = length scheme"
              and hw_filt: "\<forall>l. length (filter (\<lambda>e. fst e = l)
                  (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2))
                = length (filter (\<lambda>e. fst e = l) scheme)"
            by (by100 blast)
          thus ?thesis
            apply (rule_tac x=a_lab in exI)
            apply (rule_tac x=b_lab in exI)
            using \<open>b_lab \<noteq> a_lab\<close> hw_equiv hw_len hw_filt by (by100 blast)
        qed
        then obtain a_lab b_lab w0' w1' w2' where hab: "a_lab \<noteq> b_lab"
            and hfull_equiv_inner: "top1_valid_scheme_equiv scheme
              (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2')"
            and hlen_w: "length w0' + length w1' + length w2' + 4 = length scheme"
            and hlabel_count_inner: "\<forall>l. length (filter (\<lambda>e. fst e = l)
                (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2'))
              = length (filter (\<lambda>e. fst e = l) scheme)"
          by blast
        then obtain a_lab b_lab w0' w1' w2' where
            hab: "a_lab \<noteq> b_lab"
            and hfull_equiv: "top1_valid_scheme_equiv scheme
                (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2')"
            and hlen_w: "length w0' + length w1' + length w2' + 4 = length scheme"
            and hlabel_count: "\<forall>l. length (filter (\<lambda>e. fst e = l)
                (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2'))
              = length (filter (\<lambda>e. fst e = l) scheme)"
          by blast
        \<comment> \<open>Step 2: Apply valid\\_Lemma\\_77\\_3\\_torus\\_extraction.\<close>
        define block where "block = [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)]"
        define w3 where "w3 = w0' @ w1' @ w2'"
        define full where "full = block @ w3"
        have hfull_block: "full = [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ w0' @ w1' @ w2'"
          unfolding full_def block_def w3_def by simp
        have hextracted: "top1_valid_scheme_equiv
            (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2')
            full"
          unfolding full_def block_def w3_def
          using valid_Lemma_77_3_torus_extraction[OF hab, of w0' w1' w2'] by (by100 blast)
        have hsch_full: "top1_valid_scheme_equiv scheme full"
          using valid_equiv_trans[OF hfull_equiv hextracted] .
        \<comment> \<open>Step 3: w3 proper and shorter.\<close>
        have hlen_w3: "length w3 = length scheme - 4" unfolding w3_def using hlen_w by (by100 simp)
        have hlt_w3: "length w3 < length scheme" using hlen_w3 hgt4 by (by100 linarith)
        \<comment> \<open>Step 4: Apply IH to w3 if length w3 \\<ge> 4. Otherwise handle directly.\<close>
        show ?thesis
        proof (cases "length w3 = 0")
          case True \<comment> \<open>w3 empty: full = block = torus 1.\<close>
          have "full = block" using True unfolding full_def w3_def by simp
          hence "top1_valid_scheme_equiv scheme block" using hsch_full by simp
          moreover have "top1_valid_scheme_equiv block (top1_n_torus_scheme 1)"
            using valid_commutator_block_equiv_torus_1[OF hab] unfolding block_def by (by100 blast)
          ultimately have "top1_valid_scheme_equiv scheme (top1_n_torus_scheme 1)"
            using valid_equiv_trans by (by100 blast)
          moreover have "top1_is_torus_scheme (top1_n_torus_scheme 1) 1"
            unfolding top1_is_torus_scheme_def by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        next
          case False \<comment> \<open>w3 non-empty.\<close>
          hence hlen_w3_pos: "length w3 > 0" by (by100 simp)
          have heven_w3: "even (length w3)"
          proof -
            have "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
            thus ?thesis using hlen_w3 by (by100 presburger)
          qed
          have hproper_w3: "\<forall>label. card {j. j < length w3 \<and> fst (w3!j) = label} \<in> {0, 2}"
          proof (intro allI)
            fix label
            have hcount_decomp: "length (filter (\<lambda>e. fst e = label)
                (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2'))
                = length (filter (\<lambda>e. fst e = label) scheme)"
              using hlabel_count by (by100 blast)
            have hcount_decomp2: "length (filter (\<lambda>e. fst e = label)
                (w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2'))
              = length (filter (\<lambda>e. fst e = label) block)
              + length (filter (\<lambda>e. fst e = label) w3)"
              unfolding block_def w3_def by (simp add: filter_append)
            hence hcount_full: "length (filter (\<lambda>e. fst e = label) block)
              + length (filter (\<lambda>e. fst e = label) w3)
                = length (filter (\<lambda>e. fst e = label) scheme)"
              using hcount_decomp by (by100 linarith)
            have hcount_block: "length (filter (\<lambda>e. fst e = label) block)
                = (if label = a_lab \<or> label = b_lab then 2 else 0)"
              unfolding block_def using hab by (by100 auto)
            from less(3) have "card {j. j < length scheme \<and> fst (scheme!j) = label} \<in> {0, 2}" by (by100 blast)
            hence "length (filter (\<lambda>e. fst e = label) scheme) \<in> {0, 2}"
              using length_filter_conv_card[of "\<lambda>e. fst e = label" scheme, symmetric] by (by100 simp)
            have "length (filter (\<lambda>e. fst e = label) w3) \<in> {0, 2}"
            proof -
              have hb: "length (filter (\<lambda>e. fst e = label) block) \<in> {0, 2}" using hcount_block by (by100 auto)
              have hs: "length (filter (\<lambda>e. fst e = label) scheme) \<in> {0, 2}"
                using \<open>length (filter (\<lambda>e. fst e = label) scheme) \<in> {0, 2}\<close> .
              from hcount_full hb hs show ?thesis by (by100 force)
            qed
            thus "card {j. j < length w3 \<and> fst (w3!j) = label} \<in> {0, 2}"
              using length_filter_conv_card[of "\<lambda>e. fst e = label" w3, symmetric] by (by100 simp)
          qed
          show ?thesis
          proof (cases "length w3 < 4")
            case True \<comment> \<open>length w3 = 2 (even, > 0, < 4).\<close>
            hence hlen2: "length w3 = 2" using hlen_w3_pos heven_w3 by (by100 presburger)
            \<comment> \<open>w3 has 2 elements, proper -> same label.\<close>
            have hsame_lab: "fst (w3!0) = fst (w3!1)" using proper_len2_same_label[OF hlen2 hproper_w3] .
            define c where "c = fst (w3!0)"
            show ?thesis
            proof (cases "snd (w3!0) = snd (w3!1)")
              case True \<comment> \<open>Same direction: projective pair [(c,d),(c,d)]. block @ proj 1 ~ proj 3.\<close>
              define d where "d = snd (w3!0)"
              have hw3_eq: "w3 = [(c,d),(c,d)]"
              proof -
                obtain e0 e1 where "w3 = [e0,e1]"
                proof -
                  have "length w3 = 2" using hlen2 .
                  then obtain x0 rest where "w3 = x0 # rest" by (cases w3) simp_all
                  then obtain x1 rest2 where "rest = x1 # rest2"
                    using \<open>length w3 = 2\<close> by (cases rest) simp_all
                  have "rest2 = []" using \<open>length w3 = 2\<close> \<open>w3 = x0 # rest\<close> \<open>rest = x1 # rest2\<close> by simp
                  thus ?thesis using \<open>w3 = x0 # rest\<close> \<open>rest = x1 # rest2\<close> that by simp
                qed
                hence "e0 = (c,d)" "e1 = (c,d)" using hsame_lab True c_def d_def by (cases e0; cases e1; simp)+
                thus ?thesis using \<open>w3 = [e0,e1]\<close> by simp
              qed
              \<comment> \<open>block @ [(c,d),(c,d)]: flip c to True if needed, then block @ proj 1.\<close>
              \<comment> \<open>scheme ~ block @ w3 = block @ [(c,d),(c,d)].\<close>
              have "top1_valid_scheme_equiv scheme (block @ [(c,d),(c,d)])"
                using hsch_full hw3_eq unfolding full_def by simp
              \<comment> \<open>[(c,d),(c,d)] ~ projective 1 via flip + valid\\_proj\\_append\\_pair.\<close>
              moreover have "top1_valid_scheme_equiv (block @ [(c,d),(c,d)]) (block @ top1_m_projective_scheme 1)"
              proof -
                have "top1_valid_scheme_equiv [(c,d),(c,d)] [(c,True),(c,True)]"
                proof (cases d)
                  case True thus ?thesis unfolding top1_valid_scheme_equiv_def by simp
                next
                  case False
                  from top1_valid_scheme_operation.v_flip_label[of "[(c,d),(c,d)]" c]
                  have "top1_valid_scheme_operation [(c,d),(c,d)] [(c,\<not>d),(c,\<not>d)]" by simp
                  hence "top1_valid_scheme_operation [(c,d),(c,d)] [(c,True),(c,True)]"
                    using False by simp
                  thus ?thesis using valid_imp_equiv by (by100 blast)
                qed
                moreover have "top1_valid_scheme_equiv [(c,True),(c,True)] (top1_m_projective_scheme 1)"
                  using valid_proj_append_pair[of 0 c]
                  unfolding top1_m_projective_scheme_def by (by100 simp)
                ultimately have "top1_valid_scheme_equiv [(c,d),(c,d)] (top1_m_projective_scheme 1)"
                  using valid_equiv_trans by (by100 blast)
                from valid_equiv_prepend[OF this, of block] show ?thesis by (by100 blast)
              qed
              \<comment> \<open>block @ proj 1 ~ proj 3 via commutator\\_prepend\\_projective.\<close>
              \<comment> \<open>Use block @ proj 1 ~ proj 3.\<close>
              moreover have "\<exists>w'. top1_is_projective_scheme w' 3 \<and>
                  top1_valid_scheme_equiv (block @ top1_m_projective_scheme 1) w'"
              proof -
                from valid_commutator_prepend_projective[OF hab, of 1]
                have "\<exists>w'. top1_is_projective_scheme w' (1+2) \<and>
                    top1_valid_scheme_equiv ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1) w'"
                  by simp
                thus ?thesis unfolding block_def by (simp add: eval_nat_numeral)
              qed
              then obtain w' where "top1_is_projective_scheme w' 3"
                  "top1_valid_scheme_equiv (block @ top1_m_projective_scheme 1) w'"
                by (by100 blast)
              ultimately have "top1_valid_scheme_equiv scheme w'"
                using valid_equiv_trans by (by100 blast)
              moreover have "(3::nat) > 0" by simp
              ultimately show ?thesis using \<open>top1_is_projective_scheme w' 3\<close>
                by (intro disjI2 disjI1 exI[of _ 3] exI[of _ w'] conjI) (by100 blast)+
            next
              case False \<comment> \<open>Opposite direction: cancel pair [(c,d),(c,~d)]. Cancel -> block ~ torus 1.\<close>
              \<comment> \<open>w3 = [(c,d),(c,~d)] which is an inverse pair. Cancel to get block ~ torus 1.\<close>
              have hinv_w3: "w3!1 = top1_inverse_edge (w3!0)"
                using hsame_lab False unfolding top1_inverse_edge_def
                by (cases "w3!0", cases "w3!1") simp
              \<comment> \<open>Cancel w3: block @ w3 ~ block @ [] = block.\<close>
              obtain a0 where ha0: "w3 = [a0, top1_inverse_edge a0]"
              proof -
                define a0 where "a0 = w3!0"
                have hne: "w3 \<noteq> []" using hlen2 by (by100 auto)
                have "w3 = [a0, w3!1]"
                proof -
                  obtain x0 rest where "w3 = x0 # rest" using hne by (cases w3) simp_all
                  obtain x1 rest2 where "rest = x1 # rest2" using hlen2 \<open>w3 = x0 # rest\<close> by (cases rest) simp_all
                  have "rest2 = []" using hlen2 \<open>w3 = x0 # rest\<close> \<open>rest = x1 # rest2\<close> by simp
                  thus ?thesis unfolding a0_def using \<open>w3 = x0 # rest\<close> \<open>rest = x1 # rest2\<close> by simp
                qed
                thus ?thesis using hinv_w3 that unfolding a0_def by simp
              qed
              from top1_valid_scheme_operation.v_cancel[of block a0 "[]"]
              have "top1_valid_scheme_operation (block @ [a0, top1_inverse_edge a0] @ []) (block @ [])" .
              hence "top1_valid_scheme_operation (block @ w3) block" using ha0 by simp
              from valid_imp_equiv[OF this]
              have "top1_valid_scheme_equiv (block @ w3) block" .
              hence "top1_valid_scheme_equiv scheme block"
                using valid_equiv_trans[OF hsch_full] unfolding full_def by (by100 blast)
              moreover have "top1_valid_scheme_equiv block (top1_n_torus_scheme 1)"
                using valid_commutator_block_equiv_torus_1[OF hab] unfolding block_def by (by100 blast)
              ultimately have "top1_valid_scheme_equiv scheme (top1_n_torus_scheme 1)"
                using valid_equiv_trans by (by100 blast)
              moreover have "top1_is_torus_scheme (top1_n_torus_scheme 1) 1"
                unfolding top1_is_torus_scheme_def by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
          next
            case False \<comment> \<open>length w3 \\<ge> 4: apply IH.\<close>
            hence hge4_w3: "length w3 \<ge> 4" by (by100 simp)
            from less(1)[OF hlt_w3 hge4_w3 hproper_w3]
            have hIH_w3: "(\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv w3 [(a,True),(a,False),(b,True),(b,False)])
                 \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv w3 w)
                 \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv w3 w)" .
            from hIH_w3 show ?thesis
            proof (elim disjE)
              \<comment> \<open>Case w3 ~ sphere: block @ sphere -> cancel pairs -> block ~ torus 1.\<close>
              assume "\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv w3 [(a,True),(a,False),(b,True),(b,False)]"
              then obtain c d where hcd: "c \<noteq> d" "top1_valid_scheme_equiv w3 [(c,True),(c,False),(d,True),(d,False)]"
                by (by100 blast)
              have "top1_valid_scheme_equiv scheme (block @ [(c,True),(c,False),(d,True),(d,False)])"
                using valid_equiv_trans[OF hsch_full] valid_equiv_prepend[OF hcd(2)]
                unfolding full_def by (by100 blast)
              \<comment> \<open>Cancel (c,T)(c,F) and (d,T)(d,F) from block @ sphere.\<close>
              moreover have "top1_valid_scheme_equiv (block @ [(c,True),(c,False),(d,True),(d,False)]) block"
              proof -
                have hinv_c: "top1_inverse_edge (c,True) = (c,False)" unfolding top1_inverse_edge_def by simp
                have hinv_d: "top1_inverse_edge (d,True) = (d,False)" unfolding top1_inverse_edge_def by simp
                from top1_valid_scheme_operation.v_cancel[of block "(c,True)" "[(d,True),(d,False)]"]
                have "top1_valid_scheme_operation (block @ [(c,True),(c,False)] @ [(d,True),(d,False)])
                    (block @ [(d,True),(d,False)])" using hinv_c by simp
                from valid_imp_equiv[OF this]
                have s1: "top1_valid_scheme_equiv (block @ [(c,True),(c,False),(d,True),(d,False)])
                    (block @ [(d,True),(d,False)])" by simp
                from top1_valid_scheme_operation.v_cancel[of block "(d,True)" "[]"]
                have "top1_valid_scheme_operation (block @ [(d,True),(d,False)] @ [])
                    (block @ [])" using hinv_d by simp
                from valid_imp_equiv[OF this]
                have s2: "top1_valid_scheme_equiv (block @ [(d,True),(d,False)]) block" by simp
                from valid_equiv_trans[OF s1 s2] show ?thesis .
              qed
              ultimately have "top1_valid_scheme_equiv scheme block"
                using valid_equiv_trans by (by100 blast)
              moreover have "top1_valid_scheme_equiv block (top1_n_torus_scheme 1)"
                using valid_commutator_block_equiv_torus_1[OF hab] unfolding block_def by (by100 blast)
              ultimately have "top1_valid_scheme_equiv scheme (top1_n_torus_scheme 1)"
                using valid_equiv_trans by (by100 blast)
              moreover have "top1_is_torus_scheme (top1_n_torus_scheme 1) 1"
                unfolding top1_is_torus_scheme_def by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            next
              \<comment> \<open>Case w3 ~ projective m: block @ proj m ~ proj (m+2).\<close>
              assume "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv w3 w"
              then obtain m w where hm: "m > 0" "top1_is_projective_scheme w m" "top1_valid_scheme_equiv w3 w"
                by (by100 blast)
              have hw_is: "w = top1_m_projective_scheme m" using hm(2) unfolding top1_is_projective_scheme_def by (by100 blast)
              have "top1_valid_scheme_equiv scheme (block @ top1_m_projective_scheme m)"
                using valid_equiv_trans[OF hsch_full] valid_equiv_prepend[OF hm(3)] hw_is
                unfolding full_def by (by100 blast)
              moreover from valid_commutator_prepend_projective[OF hab hm(1)]
              obtain w' where hw': "top1_is_projective_scheme w' (m+2)"
                  "top1_valid_scheme_equiv ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme m) w'"
                by (by100 blast)
              hence "top1_valid_scheme_equiv (block @ top1_m_projective_scheme m) w'"
                unfolding block_def by simp
              ultimately have "top1_valid_scheme_equiv scheme w'"
                using valid_equiv_trans by (by100 blast)
              moreover have "m + 2 > 0" by (by100 simp)
              ultimately show ?thesis using hw'(1)
                by (intro disjI2 disjI1 exI[of _ "m+2"] exI[of _ w'] conjI) (by100 blast)+
            next
              \<comment> \<open>Case w3 ~ torus n: block @ torus n ~ torus (n+1).\<close>
              assume "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv w3 w"
              then obtain n w where hn: "n > 0" "top1_is_torus_scheme w n" "top1_valid_scheme_equiv w3 w"
                by (by100 blast)
              have hw_is: "w = top1_n_torus_scheme n" using hn(2) unfolding top1_is_torus_scheme_def by (by100 blast)
              have "top1_valid_scheme_equiv scheme (block @ top1_n_torus_scheme n)"
                using valid_equiv_trans[OF hsch_full] valid_equiv_prepend[OF hn(3)] hw_is
                unfolding full_def by (by100 blast)
              moreover have "top1_valid_scheme_equiv (block @ top1_n_torus_scheme n) (top1_n_torus_scheme (Suc n))"
                using valid_commutator_prepend_torus[OF hab hn(1)] unfolding block_def by (by100 blast)
              ultimately have "top1_valid_scheme_equiv scheme (top1_n_torus_scheme (Suc n))"
                using valid_equiv_trans by (by100 blast)
              moreover have "top1_is_torus_scheme (top1_n_torus_scheme (Suc n)) (Suc n)"
                unfolding top1_is_torus_scheme_def by (by100 blast)
              moreover have "Suc n > 0" by simp
              ultimately show ?thesis by (by100 blast)
            qed
          qed
        qed
      qed
    qed
  qed
qed

(** from \<S>77 Theorem 77.5: Classification theorem for compact surfaces.
    Every compact connected triangulable surface is homeomorphic to either:
    - the sphere S^2,
    - the n-fold torus T_n for some n \<ge> 1, or
    - the m-fold projective plane P_m for some m \<ge> 1. **)

end
